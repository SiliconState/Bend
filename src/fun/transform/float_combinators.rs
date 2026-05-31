use crate::{
  fun::{Book, Definition, Name, Pattern, Rule, Source, Term},
  maybe_grow, multi_iterator,
};
use indexmap::{IndexMap, IndexSet};
use std::collections::{BTreeMap, BTreeSet};

pub const NAME_SEP: &str = "__C";

impl Book {
  /// Extracts combinator terms into new definitions.
  ///
  /// Precondition: Variables must have been sanitized.
  ///
  /// The floating algorithm follows these rules:
  /// For each child of the term:
  /// - Recursively float every grandchild term.
  /// - If the child is a combinator:
  ///   * If the child is not "safe", extract it.
  ///   * If the term is a combinator and it's "safe":
  ///     - If the term is currently larger than `max_size`, extract the child.
  ///   * Otherwise, always extract the child to a new definition.
  /// - If the child is not a combinator, we can't extract it since
  ///   it would generate an invalid term.
  ///
  /// Terms are considered combinators if they have no free vars,
  /// no unmatched unscoped binds/vars and are not references (to
  /// avoid infinite recursion).
  ///
  /// See [`Term::is_safe`] for what is considered safe here.
  ///
  /// See [`Term::size`] for the measurement of size.
  /// It should more or less correspond to the compiled inet size.
  pub fn float_combinators(&mut self, max_size: usize) {
    // REF-04 (`workspace/notes/isomorphic-optimization-reference.md`): compute
    // immutable per-definition safety from the pre-mutation book instead of
    // cloning the whole book for reference lookups during mutation.
    let def_safety = precompute_def_safety(self);
    let constructors = self.ctrs.keys().cloned().collect();
    let mut ctx = FloatCombinatorsCtx::new(def_safety, constructors, max_size);

    for (def_name, def) in self.defs.iter_mut() {
      // Don't float combinators in the main entrypoint.
      // This avoids making programs unexpectedly too lazy,
      // returning just a reference without executing anything.
      if let Some(main) = self.entrypoint.as_ref() {
        if def_name == main {
          continue;
        }
      }

      let source = def.source.clone();
      let check = def.check;
      let body = &mut def.rule_mut().body;
      ctx.reset();
      ctx.def_size = body.float_facts().size;
      body.float_combinators(&mut ctx, def_name, source, check);
    }

    self.defs.extend(ctx.combinators.into_iter().map(|(nam, (_, def))| (nam, def)));
  }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum SafetyState {
  Visiting,
  Safe,
  Unsafe,
}

struct FloatCombinatorsCtx {
  pub combinators: BTreeMap<Name, (bool, Definition)>,
  pub name_gen: usize,
  pub def_safety: BTreeMap<Name, bool>,
  pub constructors: BTreeSet<Name>,
  pub max_size: usize,
  pub def_size: usize,
}

impl FloatCombinatorsCtx {
  fn new(def_safety: BTreeMap<Name, bool>, constructors: BTreeSet<Name>, max_size: usize) -> Self {
    Self { combinators: Default::default(), name_gen: 0, def_safety, constructors, max_size, def_size: 0 }
  }

  fn reset(&mut self) {
    self.def_size = 0;
    self.name_gen = 0;
  }
}

#[derive(Default)]
struct TermFacts {
  size: usize,
  free_vars: IndexMap<Name, u64>,
  unscoped_declared: IndexSet<Name>,
  unscoped_used: IndexSet<Name>,
}

impl TermFacts {
  fn is_combinator(&self, term: &Term) -> bool {
    self.free_vars.is_empty() && !self.has_unscoped_diff() && !matches!(term, Term::Ref { .. })
  }

  fn has_unscoped_diff(&self) -> bool {
    self.unscoped_declared.difference(&self.unscoped_used).next().is_some()
      || self.unscoped_used.difference(&self.unscoped_declared).next().is_some()
  }
}

fn precompute_def_safety(book: &Book) -> BTreeMap<Name, bool> {
  let mut memo = BTreeMap::new();
  for name in book.defs.keys() {
    let _ = original_def_is_safe(name, book, &mut memo);
  }
  memo.into_iter().map(|(name, state)| (name, matches!(state, SafetyState::Safe))).collect()
}

fn original_def_is_safe(name: &Name, book: &Book, memo: &mut BTreeMap<Name, SafetyState>) -> bool {
  match memo.get(name).copied() {
    Some(SafetyState::Safe) => return true,
    Some(SafetyState::Unsafe | SafetyState::Visiting) => return false,
    None => {}
  }

  memo.insert(name.clone(), SafetyState::Visiting);
  let safe =
    book.defs.get(name).map(|def| original_term_is_safe(&def.rule().body, book, memo)).unwrap_or(false);
  memo.insert(name.clone(), if safe { SafetyState::Safe } else { SafetyState::Unsafe });
  safe
}

fn original_term_is_safe(term: &Term, book: &Book, memo: &mut BTreeMap<Name, SafetyState>) -> bool {
  maybe_grow(|| match term {
    Term::Num { .. }
    | Term::Era
    | Term::Err
    | Term::Fan { .. }
    | Term::App { .. }
    | Term::Oper { .. }
    | Term::Swt { .. } => term.children().all(|c| original_term_is_safe(c, book, memo)),
    Term::Lam { .. } => original_lambda_is_safe(term, book, memo),
    Term::Ref { nam } => book.ctrs.contains_key(nam) || original_def_is_safe(nam, book, memo),
    // TODO: Variables can be safe depending on how they're used.
    _ => false,
  })
}

fn original_lambda_is_safe(term: &Term, book: &Book, memo: &mut BTreeMap<Name, SafetyState>) -> bool {
  let mut current = term;
  let mut scope = Vec::new();

  while let Term::Lam { pat, bod, .. } = current {
    scope.extend(pat.binds().filter_map(|x| x.as_ref()));
    current = bod;
  }

  match current {
    Term::Var { nam } if scope.contains(&nam) => true,
    Term::Ref { .. } => true,
    term => original_term_is_safe(term, book, memo),
  }
}

impl Term {
  fn float_combinators(
    &mut self,
    ctx: &mut FloatCombinatorsCtx,
    def_name: &Name,
    source: Source,
    check: bool,
  ) {
    maybe_grow(|| {
      // Recursively float the grandchildren terms.
      for child in self.float_children_mut() {
        child.float_combinators(ctx, def_name, source.clone(), check);
      }

      // REF-02: collect size/free-var/unscoped facts in one local pass rather
      // than calling size(), free_vars(), and unscoped_vars() separately.
      let facts = self.float_facts();
      let mut size = facts.size;
      let is_combinator = facts.is_combinator(self);

      // Float unsafe children and children that make the term too big.
      for child in self.float_children_mut() {
        let child_facts = child.float_facts();
        let child_is_safe = child.is_safe(ctx);
        let child_size = child_facts.size;

        let extract_for_size = if is_combinator { size > ctx.max_size } else { ctx.def_size > ctx.max_size };

        if child_facts.is_combinator(child) && child_size > 0 && (!child_is_safe || extract_for_size) {
          ctx.def_size -= child_size;
          size -= child_size;
          child.float(ctx, def_name, source.clone(), check, child_is_safe);
        }
      }
    })
  }

  /// Inserts a new definition for the given term in the combinators map.
  fn float(
    &mut self,
    ctx: &mut FloatCombinatorsCtx,
    def_name: &Name,
    source: Source,
    check: bool,
    is_safe: bool,
  ) {
    let comb_name = Name::new(format!("{}{}{}", def_name, NAME_SEP, ctx.name_gen));
    ctx.name_gen += 1;

    let comb_ref = Term::Ref { nam: comb_name.clone() };
    let extracted_term = std::mem::replace(self, comb_ref);

    let rules = vec![Rule { body: extracted_term, pats: Vec::new() }];
    let rule = Definition::new_gen(comb_name.clone(), rules, source, check);
    ctx.combinators.insert(comb_name, (is_safe, rule));
  }
}

impl Term {
  /// A term can be considered safe if it is:
  /// - A Number or an Eraser.
  /// - A Tuple or Superposition where all elements are safe.
  /// - An application or numeric operation where all arguments are safe.
  /// - A safe Lambda, e.g. a nullary constructor or a lambda with safe body.
  /// - A Reference with a safe body.
  ///
  /// A reference to a recursive definition (or mutually recursive) is not safe.
  fn is_safe(&self, ctx: &mut FloatCombinatorsCtx) -> bool {
    maybe_grow(|| match self {
      Term::Num { .. }
      | Term::Era
      | Term::Err
      | Term::Fan { .. }
      | Term::App { .. }
      | Term::Oper { .. }
      | Term::Swt { .. } => self.children().all(|c| c.is_safe(ctx)),
      Term::Lam { .. } => self.is_safe_lambda(ctx),
      Term::Ref { nam } => {
        // Constructors are safe.
        if ctx.constructors.contains(nam) {
          return true;
        }
        // Original definitions use precomputed summaries; generated
        // combinators are checked from the insertion map.
        if let Some(safe) = ctx.def_safety.get(nam) {
          *safe
        } else if let Some((safe, _)) = ctx.combinators.get(nam) {
          *safe
        } else {
          false
        }
      }
      // TODO: Variables can be safe depending on how they're used
      // For example, in a well-typed numop they're safe.
      _ => false,
    })
  }

  /// Checks if the term is a lambda sequence with a safe body.
  /// If the body is a variable bound in the lambdas, it's a nullary constructor.
  /// If the body is a reference, it's in inactive position, so always safe.
  fn is_safe_lambda(&self, ctx: &mut FloatCombinatorsCtx) -> bool {
    let mut current = self;
    let mut scope = Vec::new();

    while let Term::Lam { pat, bod, .. } = current {
      scope.extend(pat.binds().filter_map(|x| x.as_ref()));
      current = bod;
    }

    match current {
      Term::Var { nam } if scope.contains(&nam) => true,
      Term::Ref { .. } => true,
      term => term.is_safe(ctx),
    }
  }

  pub fn has_unscoped_diff(&self) -> bool {
    let (declared, used) = self.unscoped_vars();
    declared.difference(&used).count() != 0 || used.difference(&declared).count() != 0
  }

  fn float_facts(&self) -> TermFacts {
    fn go_pattern(pat: &Pattern, declared: &mut IndexSet<Name>) {
      maybe_grow(|| {
        if let Pattern::Chn(name) = pat {
          declared.insert(name.clone());
        }
        for child in pat.children() {
          go_pattern(child, declared);
        }
      })
    }

    fn go(term: &Term) -> TermFacts {
      maybe_grow(|| {
        let mut facts = TermFacts { size: term.base_size(), ..Default::default() };

        if let Term::Var { nam } = term {
          *facts.free_vars.entry(nam.clone()).or_default() += 1;
        }
        if let Term::Link { nam } = term {
          facts.unscoped_used.insert(nam.clone());
        }
        if let Some(pat) = term.pattern() {
          go_pattern(pat, &mut facts.unscoped_declared);
        }

        for (child, binds) in term.children_with_binds() {
          let mut child_facts = go(child);
          facts.size += child_facts.size;
          for nam in binds.flatten() {
            child_facts.free_vars.shift_remove(nam);
          }
          facts.free_vars.extend(child_facts.free_vars);
          facts.unscoped_declared.extend(child_facts.unscoped_declared);
          facts.unscoped_used.extend(child_facts.unscoped_used);
        }

        facts
      })
    }

    go(self)
  }

  fn base_size(&self) -> usize {
    match self {
      Term::Let { pat, .. } => pat.size(),
      Term::Fan { els, .. } => els.len() - 1,
      Term::Mat { arms, .. } => arms.len(),
      Term::Swt { arms, .. } => 2 * (arms.len() - 1),
      Term::Lam { .. } => 1,
      Term::App { .. } => 1,
      Term::Oper { .. } => 1,
      Term::Var { .. } => 0,
      Term::Link { .. } => 0,
      Term::Use { .. } => 0,
      Term::Num { .. } => 0,
      Term::Ref { .. } => 0,
      Term::Era => 0,
      Term::Bend { .. }
      | Term::Fold { .. }
      | Term::Nat { .. }
      | Term::Str { .. }
      | Term::List { .. }
      | Term::With { .. }
      | Term::Ask { .. }
      | Term::Open { .. }
      | Term::Def { .. }
      | Term::Err => unreachable!(),
    }
  }

  pub fn float_children_mut(&mut self) -> impl Iterator<Item = &mut Term> {
    multi_iterator!(FloatIter { Zero, Two, Vec, Mat, App, Swt });
    match self {
      Term::App { .. } => {
        let mut next = Some(self);
        FloatIter::App(std::iter::from_fn(move || {
          let cur = next.take();
          if let Some(Term::App { fun, arg, .. }) = cur {
            next = Some(&mut *fun);
            Some(&mut **arg)
          } else {
            cur
          }
        }))
      }
      Term::Mat { arg, bnd: _, with_bnd: _, with_arg, arms } => FloatIter::Mat(
        [arg.as_mut()].into_iter().chain(with_arg.iter_mut()).chain(arms.iter_mut().map(|r| &mut r.2)),
      ),
      Term::Swt { arg, bnd: _, with_bnd: _, with_arg, pred: _, arms } => {
        FloatIter::Swt([arg.as_mut()].into_iter().chain(with_arg.iter_mut()).chain(arms.iter_mut()))
      }
      Term::Fan { els, .. } | Term::List { els } => FloatIter::Vec(els),
      Term::Let { val: fst, nxt: snd, .. }
      | Term::Use { val: fst, nxt: snd, .. }
      | Term::Oper { fst, snd, .. } => FloatIter::Two([fst.as_mut(), snd.as_mut()]),
      Term::Lam { bod, .. } => bod.float_children_mut(),
      Term::Var { .. }
      | Term::Link { .. }
      | Term::Num { .. }
      | Term::Nat { .. }
      | Term::Str { .. }
      | Term::Ref { .. }
      | Term::Era
      | Term::Err => FloatIter::Zero([]),
      Term::With { .. }
      | Term::Ask { .. }
      | Term::Bend { .. }
      | Term::Fold { .. }
      | Term::Open { .. }
      | Term::Def { .. } => {
        unreachable!()
      }
    }
  }
}

impl Pattern {
  fn size(&self) -> usize {
    match self {
      Pattern::Var(_) => 0,
      Pattern::Chn(_) => 0,
      Pattern::Fan(_, _, pats) => pats.len() - 1 + pats.iter().map(|p| p.size()).sum::<usize>(),

      Pattern::Num(_) | Pattern::Lst(_) | Pattern::Str(_) | Pattern::Ctr(_, _) => unreachable!(),
    }
  }
}
