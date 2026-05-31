//! Optional Hindley-Milner-like type system.
//!
//! Based on https://github.com/developedby/algorithm-w-rs
//! and https://github.com/mgrabmueller/AlgorithmW.
use crate::{
  diagnostics::Diagnostics,
  fun::{num_to_name, Adt, Book, Ctx, FanKind, MatchRule, Name, Num, Op, Pattern, Tag, Term, Type},
  maybe_grow,
};
use std::collections::{BTreeMap, BTreeSet, HashMap};

impl Ctx<'_> {
  pub fn type_check(&mut self) -> Result<(), Diagnostics> {
    let types = infer_book(self.book, &mut self.info)?;

    for def in self.book.defs.values_mut() {
      def.typ = types[&def.name].instantiate(&mut VarGen::default());
    }

    Ok(())
  }
}

type ProgramTypes = HashMap<Name, Scheme>;

/// A type scheme, aka a polymorphic type.
#[derive(Clone, Debug)]
struct Scheme(Vec<Name>, Type);

/// A finite mapping from type variables to types.
#[derive(Clone, Default, Debug)]
struct Subst(BTreeMap<Name, Type>);

/// A mapping from term variables to type schemes.
#[derive(Clone, Default, Debug)]
struct TypeEnv(BTreeMap<Name, Scheme>);

/// Variable generator for type variables.
#[derive(Default)]
struct VarGen(usize);

/// Mutable type-inference state.
///
/// REF-01 (`workspace/notes/isomorphic-optimization-reference.md`): the old
/// inferencer returned and composed persistent substitutions after most AST
/// nodes. This state keeps one path-compressed substitution table for a whole
/// recursive group, so unification mutates the table in place and later reads
/// prune through it instead of repeatedly cloning whole types/environments.
#[derive(Default)]
struct InferState {
  subst: Subst,
  var_gen: VarGen,
}

/// Topologically ordered set of mutually recursive groups of functions.
struct RecGroups(Vec<Vec<Name>>);

/* Implementations */

impl Type {
  fn free_type_vars(&self) -> BTreeSet<Name> {
    maybe_grow(|| match self {
      Type::Var(x) => BTreeSet::from([x.clone()]),
      Type::Ctr(_, ts) | Type::Tup(ts) => ts.iter().flat_map(|t| t.free_type_vars()).collect(),
      Type::Arr(t1, t2) => t1.free_type_vars().union(&t2.free_type_vars()).cloned().collect(),
      Type::Number(t) | Type::Integer(t) => t.free_type_vars(),
      Type::U24 | Type::F24 | Type::I24 | Type::None | Type::Any | Type::Hole => BTreeSet::new(),
    })
  }

  fn subst(&self, subst: &Subst) -> Type {
    maybe_grow(|| match self {
      Type::Var(nam) => match subst.0.get(nam) {
        Some(new) => new.clone(),
        None => self.clone(),
      },
      Type::Ctr(name, ts) => Type::Ctr(name.clone(), ts.iter().map(|t| t.subst(subst)).collect()),
      Type::Arr(t1, t2) => Type::Arr(Box::new(t1.subst(subst)), Box::new(t2.subst(subst))),
      Type::Tup(els) => Type::Tup(els.iter().map(|t| t.subst(subst)).collect()),
      Type::Number(t) => Type::Number(Box::new(t.subst(subst))),
      Type::Integer(t) => Type::Integer(Box::new(t.subst(subst))),
      t @ (Type::U24 | Type::F24 | Type::I24 | Type::None | Type::Any | Type::Hole) => t.clone(),
    })
  }

  /// Converts a monomorphic type into a closed type scheme by abstracting
  /// over all type variables free in `self`.
  fn generalize_closed(&self) -> Scheme {
    Scheme(self.free_type_vars().into_iter().collect(), self.clone())
  }
}

impl Scheme {
  /// Converts a type scheme into a monomorphic type by assigning
  /// fresh type variables to each variable bound by the scheme.
  fn instantiate(&self, var_gen: &mut VarGen) -> Type {
    let new_vars = self.0.iter().map(|_| var_gen.fresh());
    let subst = Subst(self.0.iter().cloned().zip(new_vars).collect());
    self.1.subst(&subst)
  }
}

impl TypeEnv {
  fn insert(&mut self, name: Name, scheme: Scheme) {
    self.0.insert(name, scheme);
  }

  fn add_binds<'a>(
    &mut self,
    bnd: impl IntoIterator<Item = (&'a Option<Name>, Scheme)>,
  ) -> Vec<(Name, Option<Scheme>)> {
    let mut old_bnd = vec![];
    for (name, scheme) in bnd {
      if let Some(name) = name {
        let old = self.0.insert(name.clone(), scheme);
        old_bnd.push((name.clone(), old));
      }
    }
    old_bnd
  }

  fn pop_binds(&mut self, old_bnd: Vec<(Name, Option<Scheme>)>) {
    for (name, scheme) in old_bnd.into_iter().rev() {
      if let Some(scheme) = scheme {
        self.0.insert(name, scheme);
      } else {
        self.0.remove(&name);
      }
    }
  }
}

impl VarGen {
  fn fresh(&mut self) -> Type {
    let x = self.fresh_name();
    Type::Var(x)
  }

  fn fresh_name(&mut self) -> Name {
    let x = num_to_name(self.0 as u64);
    self.0 += 1;
    Name::new(x)
  }
}

impl InferState {
  fn fresh(&mut self) -> Type {
    self.var_gen.fresh()
  }

  fn instantiate(&mut self, scheme: &Scheme) -> Type {
    let new_vars = scheme.0.iter().map(|_| self.fresh());
    let subst = Subst(scheme.0.iter().cloned().zip(new_vars).collect());
    self.prune(&scheme.1.subst(&subst))
  }

  fn generalize(&mut self, typ: &Type, env: &TypeEnv) -> Scheme {
    let typ = self.prune(typ);
    let vars_env = self.env_free_type_vars(env);
    let vars_t = typ.free_type_vars();
    let vars = vars_t.difference(&vars_env).cloned().collect();
    Scheme(vars, typ)
  }

  fn env_free_type_vars(&mut self, env: &TypeEnv) -> BTreeSet<Name> {
    let mut vars = BTreeSet::new();
    for scheme in env.0.values() {
      vars.extend(self.scheme_free_type_vars(scheme));
    }
    vars
  }

  fn scheme_free_type_vars(&mut self, scheme: &Scheme) -> BTreeSet<Name> {
    let bound_vars = scheme.0.iter().cloned().collect::<BTreeSet<_>>();
    let typ = self.prune_except(&scheme.1, &bound_vars);
    typ.free_type_vars().difference(&bound_vars).cloned().collect()
  }

  fn prune(&mut self, typ: &Type) -> Type {
    self.prune_except(typ, &BTreeSet::new())
  }

  fn prune_except(&mut self, typ: &Type, bound_vars: &BTreeSet<Name>) -> Type {
    maybe_grow(|| match typ {
      Type::Var(nam) if !bound_vars.contains(nam) => {
        if let Some(new) = self.subst.0.get(nam).cloned() {
          let pruned = self.prune_except(&new, bound_vars);
          self.subst.0.insert(nam.clone(), pruned.clone());
          pruned
        } else {
          typ.clone()
        }
      }
      Type::Ctr(name, ts) => {
        Type::Ctr(name.clone(), ts.iter().map(|t| self.prune_except(t, bound_vars)).collect())
      }
      Type::Arr(t1, t2) => {
        Type::Arr(Box::new(self.prune_except(t1, bound_vars)), Box::new(self.prune_except(t2, bound_vars)))
      }
      Type::Tup(els) => Type::Tup(els.iter().map(|t| self.prune_except(t, bound_vars)).collect()),
      Type::Number(t) => Type::Number(Box::new(self.prune_except(t, bound_vars))),
      Type::Integer(t) => Type::Integer(Box::new(self.prune_except(t, bound_vars))),
      t @ (Type::Var(_) | Type::U24 | Type::F24 | Type::I24 | Type::None | Type::Any | Type::Hole) => {
        t.clone()
      }
    })
  }

  fn occurs(&mut self, var: &Name, typ: &Type) -> bool {
    self.prune(typ).free_type_vars().contains(var)
  }

  fn bind_var(&mut self, var: &Name, typ: &Type) -> Result<Type, String> {
    let typ = self.prune(typ);
    if let Type::Var(other) = &typ {
      if other == var {
        return Ok(typ);
      }
    }
    if self.occurs(var, &typ) {
      return Err(format!(" Variable '{var}' occurs in '{typ}'"));
    }
    self.subst.0.insert(var.clone(), typ.clone());
    Ok(typ)
  }

  fn unify_term(&mut self, t1: &Type, t2: &Type, ctx: &Term) -> Result<Type, String> {
    match self.unify(t1, t2) {
      Ok(t) => Ok(t),
      Err(msg) => Err(format!(
        "In {ctx}:
  Can't unify '{t1}' and '{t2}'.{msg}"
      )),
    }
  }

  fn unify(&mut self, t1: &Type, t2: &Type) -> Result<Type, String> {
    maybe_grow(|| {
      let t1 = self.prune(t1);
      let t2 = self.prune(t2);
      match (t1, t2) {
        (t, Type::Hole) | (Type::Hole, t) => Ok(t),
        // Keep the old unifier's branch order: when one side is a variable,
        // bind the right-side variable first. This preserves deterministic
        // diagnostic type-variable names in existing snapshots.
        (t, Type::Var(x)) | (Type::Var(x), t) => self.bind_var(&x, &t),
        (Type::Arr(l1, r1), Type::Arr(l2, r2)) => {
          let l = self.unify(&l1, &l2)?;
          let r = self.unify(&r1, &r2)?;
          Ok(self.prune(&Type::Arr(Box::new(l), Box::new(r))))
        }
        (Type::Ctr(name1, ts1), Type::Ctr(name2, ts2)) if name1 == name2 && ts1.len() == ts2.len() => {
          let mut ts = Vec::with_capacity(ts1.len());
          for (t1, t2) in ts1.iter().zip(ts2.iter()) {
            ts.push(self.unify(t1, t2)?);
          }
          Ok(self.prune(&Type::Ctr(name1, ts)))
        }
        (Type::Tup(els1), Type::Tup(els2)) if els1.len() == els2.len() => {
          let mut ts = Vec::with_capacity(els1.len());
          for (t1, t2) in els1.iter().zip(els2.iter()) {
            ts.push(self.unify(t1, t2)?);
          }
          Ok(self.prune(&Type::Tup(ts)))
        }
        t @ ((Type::U24, Type::U24)
        | (Type::F24, Type::F24)
        | (Type::I24, Type::I24)
        | (Type::None, Type::None)) => Ok(t.0),
        (Type::Number(t1), Type::Number(t2)) => {
          let t = self.unify(&t1, &t2)?;
          Ok(Type::Number(Box::new(t)))
        }
        (Type::Number(tn), Type::Integer(ti)) | (Type::Integer(ti), Type::Number(tn)) => {
          let t = self.unify(&ti, &tn)?;
          Ok(Type::Integer(Box::new(t)))
        }
        (Type::Integer(t1), Type::Integer(t2)) => {
          let t = self.unify(&t1, &t2)?;
          Ok(Type::Integer(Box::new(t)))
        }
        (Type::Number(t1) | Type::Integer(t1), t2 @ (Type::U24 | Type::I24 | Type::F24))
        | (t2 @ (Type::U24 | Type::I24 | Type::F24), Type::Number(t1) | Type::Integer(t1)) => {
          self.unify(&t1, &t2)
        }

        (Type::Any, t) | (t, Type::Any) => {
          for child in t.children() {
            self.unify(&Type::Any, child)?;
          }
          Ok(Type::Any)
        }

        _ => Err(String::new()),
      }
    })
  }
}

impl RecGroups {
  fn from_book(book: &Book) -> RecGroups {
    type DependencyGraph<'a> = BTreeMap<&'a Name, BTreeSet<&'a Name>>;

    fn collect_dependencies<'a>(
      term: &'a Term,
      book: &'a Book,
      scope: &mut Vec<Name>,
      deps: &mut BTreeSet<&'a Name>,
    ) {
      if let Term::Ref { nam } = term {
        if book.ctrs.contains_key(nam) || book.hvm_defs.contains_key(nam) || !book.defs[nam].check {
          // Don't infer types for constructors or unchecked functions
        } else {
          deps.insert(nam);
        }
      }
      for (child, binds) in term.children_with_binds() {
        scope.extend(binds.clone().flatten().cloned());
        collect_dependencies(child, book, scope, deps);
        scope.truncate(scope.len() - binds.flatten().count());
      }
    }

    /// Tarjan's algorithm for finding strongly connected components.
    fn strong_connect<'a>(
      v: &'a Name,
      deps: &DependencyGraph<'a>,
      index: &mut usize,
      index_map: &mut BTreeMap<&'a Name, usize>,
      low_link: &mut BTreeMap<&'a Name, usize>,
      stack: &mut Vec<&'a Name>,
      on_stack: &mut BTreeSet<&'a Name>,
      components: &mut Vec<BTreeSet<Name>>,
    ) {
      maybe_grow(|| {
        index_map.insert(v, *index);
        low_link.insert(v, *index);
        *index += 1;
        stack.push(v);
        on_stack.insert(v);

        if let Some(neighbors) = deps.get(v) {
          for w in neighbors {
            if !index_map.contains_key(w) {
              // Successor w has not yet been visited, recurse on it.
              strong_connect(w, deps, index, index_map, low_link, stack, on_stack, components);
              low_link.insert(v, low_link[v].min(low_link[w]));
            } else if on_stack.contains(w) {
              // Successor w is in stack S and hence in the current SCC.
              low_link.insert(v, low_link[v].min(index_map[w]));
            } else {
              // If w is not on stack, then (v, w) is an edge pointing
              // to an SCC already found and must be ignored.
            }
          }
        }

        // If v is a root node, pop the stack and generate an SCC.
        if low_link[v] == index_map[v] {
          let mut component = BTreeSet::new();
          while let Some(w) = stack.pop() {
            on_stack.remove(w);
            component.insert(w.clone());
            if w == v {
              break;
            }
          }
          components.push(component);
        }
      })
    }

    // Build the dependency graph
    let mut deps = DependencyGraph::default();
    for (name, def) in &book.defs {
      if book.ctrs.contains_key(name) || !def.check {
        // Don't infer types for constructors or unchecked functions
        continue;
      }
      let mut fn_deps = Default::default();
      collect_dependencies(&def.rule().body, book, &mut vec![], &mut fn_deps);
      deps.insert(name, fn_deps);
    }

    let mut index = 0;
    let mut stack = Vec::new();
    let mut on_stack = BTreeSet::new();
    let mut index_map = BTreeMap::new();
    let mut low_link = BTreeMap::new();
    let mut components = Vec::new();
    for name in deps.keys() {
      if !index_map.contains_key(name) {
        strong_connect(
          name,
          &deps,
          &mut index,
          &mut index_map,
          &mut low_link,
          &mut stack,
          &mut on_stack,
          &mut components,
        );
      }
    }
    let components = components.into_iter().map(|x| x.into_iter().collect()).collect();
    RecGroups(components)
  }
}

/* Inference, unification and type checking */
fn infer_book(book: &Book, diags: &mut Diagnostics) -> Result<ProgramTypes, Diagnostics> {
  let groups = RecGroups::from_book(book);
  let mut env = TypeEnv::default();
  // Note: We store the inferred and generalized types in a separate
  // environment, to avoid unnecessary cloning (since no immutable data).
  let mut types = ProgramTypes::default();

  // Add the constructors to the environment.
  for adt in book.adts.values() {
    for ctr in adt.ctrs.values() {
      types.insert(ctr.name.clone(), ctr.typ.generalize_closed());
    }
  }
  // Add the types of unchecked functions to the environment.
  for def in book.defs.values() {
    if !def.check {
      types.insert(def.name.clone(), def.typ.generalize_closed());
    }
  }
  // Add the types of hvm functions to the environment.
  for def in book.hvm_defs.values() {
    types.insert(def.name.clone(), def.typ.generalize_closed());
  }

  // Infer the types of regular functions.
  for group in &groups.0 {
    infer_group(&mut env, book, group, &mut types, diags)?;
  }
  Ok(types)
}

fn infer_group(
  env: &mut TypeEnv,
  book: &Book,
  group: &[Name],
  types: &mut ProgramTypes,
  diags: &mut Diagnostics,
) -> Result<(), Diagnostics> {
  let state = &mut InferState::default();
  // Generate fresh type variables for each function in the group.
  let tvs = group.iter().map(|_| state.fresh()).collect::<Vec<_>>();
  for (name, tv) in group.iter().zip(tvs.iter()) {
    env.insert(name.clone(), Scheme(vec![], tv.clone()));
  }

  // Infer the types of the functions in the group. REF-01 keeps constraints in
  // `state` instead of composing one substitution per definition.
  let mut inf_ts = vec![];
  let mut exp_ts = vec![];
  for name in group {
    let def = &book.defs[name];
    let t = infer(env, book, types, &def.rule().body, state).map_err(|e| {
      diags.add_function_error(e, name.clone(), def.source.clone());
      std::mem::take(diags)
    })?;
    let t = state.prune(&t);
    inf_ts.push(t);
    exp_ts.push(&def.typ);
  }

  // Remove the type variables of the group from the environment.
  // This avoids cloning of already generalized types.
  for name in group.iter() {
    env.0.remove(name);
  }

  // Unify the inferred body with the corresponding type variable.
  let mut ts = vec![];
  for ((bod_t, tv), nam) in inf_ts.into_iter().zip(tvs.iter()).zip(group.iter()) {
    let tv = state.prune(tv);
    let t = state.unify_term(&tv, &bod_t, &book.defs[nam].rule().body)?;
    ts.push(state.prune(&t));
  }

  // Match the old substitution-composition path: after all group constraints
  // are known, re-prune every inferred type through the final group state.
  let ts = ts.into_iter().map(|t| state.prune(&t)).collect::<Vec<_>>();

  // Specialize against the expected type, then generalize and store. Any
  // remaining substitutions from the recursive group are local to this group;
  // applying them to a closed specialized type can rewrite freshly-instantiated
  // variables in later groups. The previous substitution-composition path also
  // stored closed schemes here, so keep the state boundary explicit.
  for ((name, exp_t), inf_t) in group.iter().zip(exp_ts.iter()).zip(ts.iter()) {
    let t = specialize(inf_t, exp_t).map_err(|e| {
      diags.add_function_error(e, name.clone(), book.defs[name].source.clone());
      std::mem::take(diags)
    })?;
    types.insert(name.clone(), t.generalize_closed());
  }

  diags.fatal(())
}

/// Infer the type of a term in the given environment.
///
/// The type environment must contain bindings for all the free variables of the term.
///
/// The returned substitution records the type constraints imposed on type variables by the term.
/// The returned type is the type of the term.
fn infer(
  env: &mut TypeEnv,
  book: &Book,
  types: &ProgramTypes,
  term: &Term,
  state: &mut InferState,
) -> Result<Type, String> {
  let res = maybe_grow(|| match term {
    Term::Var { nam } | Term::Ref { nam } => {
      if let Some(scheme) = env.0.get(nam) {
        Ok::<_, String>(state.instantiate(scheme))
      } else if let Some(scheme) = types.get(nam) {
        Ok(state.instantiate(scheme))
      } else {
        unreachable!("unbound name '{}'", nam)
      }
    }
    Term::Lam { tag: Tag::Static, pat, bod } => match pat.as_ref() {
      Pattern::Var(nam) => {
        let tv = state.fresh();
        let old_bnd = env.add_binds([(nam, Scheme(vec![], tv.clone()))]);
        let bod_t = infer(env, book, types, bod, state)?;
        env.pop_binds(old_bnd);
        let var_t = state.prune(&tv);
        Ok(Type::Arr(Box::new(var_t), Box::new(state.prune(&bod_t))))
      }
      _ => unreachable!("{}", term),
    },
    Term::App { tag: Tag::Static, fun, arg } => {
      let fun_t = infer(env, book, types, fun, state)?;
      let arg_t = infer(env, book, types, arg, state)?;
      let app_t = state.fresh();
      let expected = Type::Arr(Box::new(arg_t), Box::new(app_t.clone()));
      state.unify_term(&fun_t, &expected, fun)?;
      Ok(state.prune(&app_t))
    }
    Term::Let { pat, val, nxt } => match pat.as_ref() {
      Pattern::Var(nam) => {
        let val_t = infer(env, book, types, val, state)?;
        let scheme = state.generalize(&val_t, env);
        let old_bnd = env.add_binds([(nam, scheme)]);
        let nxt_t = infer(env, book, types, nxt, state)?;
        env.pop_binds(old_bnd);
        Ok(state.prune(&nxt_t))
      }
      Pattern::Fan(FanKind::Tup, Tag::Static, _) => {
        // Tuple elimination behaves like pattern matching.
        // Variables from tuple patterns don't get generalized.
        debug_assert!(!(pat.has_unscoped() || pat.has_nested()));
        let val_t = infer(env, book, types, val, state)?;

        let tvs = pat.binds().map(|_| state.fresh()).collect::<Vec<_>>();
        let old_bnd = env.add_binds(pat.binds().zip(tvs.iter().map(|tv| Scheme(vec![], tv.clone()))));
        let nxt_t = infer(env, book, types, nxt, state)?;
        env.pop_binds(old_bnd);
        let tvs = tvs.iter().map(|tv| state.prune(tv)).collect::<Vec<_>>();
        state.unify_term(&val_t, &Type::Tup(tvs), val)?;
        Ok(state.prune(&nxt_t))
      }
      Pattern::Fan(FanKind::Dup, Tag::Auto, _) => {
        // We pretend that sups don't exist and dups don't collide.
        // All variables must have the same type as the body of the dup.
        debug_assert!(!(pat.has_unscoped() || pat.has_nested()));
        let mut val_t = infer(env, book, types, val, state)?;
        let tvs = pat.binds().map(|_| state.fresh()).collect::<Vec<_>>();
        let old_bnd = env.add_binds(pat.binds().zip(tvs.iter().map(|tv| Scheme(vec![], tv.clone()))));
        let nxt_t = infer(env, book, types, nxt, state)?;
        env.pop_binds(old_bnd);
        for tv in tvs {
          let tv = state.prune(&tv);
          val_t = state.unify_term(&val_t, &tv, val)?;
        }
        Ok(state.prune(&nxt_t))
      }
      _ => unreachable!(),
    },

    Term::Mat { bnd: _, arg, with_bnd: _, with_arg: _, arms } => {
      // Infer type of the scrutinee
      let t1 = infer(env, book, types, arg, state)?;

      // Instantiate the expected type of the scrutinee
      let adt_name = book.ctrs.get(arms[0].0.as_ref().unwrap()).unwrap();
      let adt = &book.adts[adt_name];
      let (adt_s, adt_t) = instantiate_adt(adt, &mut state.var_gen)?;

      // For each case, infer the types and unify them all.
      // Unify the inferred type of the destructured fields with the
      // expected from what we inferred from the scrutinee.
      let nxt_t = infer_match_cases(env, book, types, adt, arms, &adt_s, state)?;

      // Unify the inferred type with the expected type
      state.unify_term(&t1, &adt_t, arg)?;
      Ok(state.prune(&nxt_t))
    }

    Term::Num { val } => {
      let t = match val {
        Num::U24(_) => Type::U24,
        Num::I24(_) => Type::I24,
        Num::F24(_) => Type::F24,
      };
      Ok(t)
    }
    Term::Oper { opr, fst, snd } => {
      let t1 = infer(env, book, types, fst, state)?;
      let t2 = infer(env, book, types, snd, state)?;
      let t_args = state.unify_term(&t2, &t1, term)?;
      // Check numeric type matches the operation
      let tv = state.fresh();
      let t_opr = match opr {
        // Any numeric type
        Op::ADD | Op::SUB | Op::MUL | Op::DIV => {
          state.unify_term(&t_args, &Type::Number(Box::new(tv.clone())), term)?
        }
        Op::EQ | Op::NEQ | Op::LT | Op::GT | Op::GE | Op::LE => {
          state.unify_term(&t_args, &Type::Number(Box::new(tv.clone())), term)?;
          Type::U24
        }
        // Integers
        Op::REM | Op::AND | Op::OR | Op::XOR | Op::SHL | Op::SHR => {
          state.unify_term(&t_args, &Type::Integer(Box::new(tv.clone())), term)?
        }
        // Floating
        Op::POW => state.unify_term(&t_args, &Type::F24, term)?,
      };
      Ok(state.prune(&t_opr))
    }
    Term::Swt { bnd: _, arg, with_bnd: _, with_arg: _, pred, arms } => {
      let t1 = infer(env, book, types, arg, state)?;
      state.unify_term(&t1, &Type::U24, arg)?;

      let mut ts_nums = vec![];
      for arm in arms.iter().rev().skip(1) {
        let t = infer(env, book, types, arm, state)?;
        ts_nums.push(t);
      }
      let old_bnd = env.add_binds([(pred, Scheme(vec![], Type::U24))]);
      let t_succ = infer(env, book, types, &arms[1], state)?;
      env.pop_binds(old_bnd);

      let mut t_swt = t_succ;
      for t_num in ts_nums {
        t_swt = state.unify_term(&t_swt, &t_num, term)?;
      }

      Ok(state.prune(&t_swt))
    }

    Term::Fan { fan: FanKind::Tup, tag: Tag::Static, els } => {
      let ts = els.iter().map(|el| infer(env, book, types, el, state)).collect::<Result<Vec<_>, _>>()?;
      Ok(Type::Tup(ts.into_iter().map(|t| state.prune(&t)).collect()))
    }
    Term::Era => Ok(Type::None),
    Term::Fan { .. } | Term::Lam { tag: _, .. } | Term::App { tag: _, .. } | Term::Link { .. } => {
      unreachable!("'{term}' while type checking. Should never occur in checked functions")
    }
    Term::Use { .. }
    | Term::With { .. }
    | Term::Ask { .. }
    | Term::Nat { .. }
    | Term::Str { .. }
    | Term::List { .. }
    | Term::Fold { .. }
    | Term::Bend { .. }
    | Term::Open { .. }
    | Term::Def { .. }
    | Term::Err => unreachable!("'{term}' while type checking. Should have been removed in earlier pass"),
  })?;
  Ok(state.prune(&res))
}

/// Instantiates the type constructor of an ADT, also returning the
/// ADT var to instantiated var substitution, to be used when
/// instantiating the types of the fields of the eliminated constructors.
fn instantiate_adt(adt: &Adt, var_gen: &mut VarGen) -> Result<(Subst, Type), String> {
  let tvs = adt.vars.iter().map(|_| var_gen.fresh());
  let s = Subst(adt.vars.iter().zip(tvs).map(|(x, t)| (x.clone(), t)).collect());
  let t = Type::Ctr(adt.name.clone(), adt.vars.iter().cloned().map(Type::Var).collect());
  let t = t.subst(&s);
  Ok((s, t))
}

fn infer_match_cases(
  env: &mut TypeEnv,
  book: &Book,
  types: &ProgramTypes,
  adt: &Adt,
  arms: &[MatchRule],
  adt_s: &Subst,
  state: &mut InferState,
) -> Result<Type, String> {
  maybe_grow(|| {
    if let Some(((ctr_nam, vars, bod), rest)) = arms.split_first() {
      let ctr = &adt.ctrs[ctr_nam.as_ref().unwrap()];
      // One fresh var per field, we later unify with the expected type.
      let tvs = vars.iter().map(|_| state.fresh()).collect::<Vec<_>>();

      // Infer the body and unify the inferred field types with the expected.
      let old_bnd = env.add_binds(vars.iter().zip(tvs.iter().map(|tv| Scheme(vec![], tv.clone()))));
      let t1 = infer(env, book, types, bod, state)?;
      env.pop_binds(old_bnd);
      let inf_ts = tvs.iter().map(|tv| state.prune(tv)).collect::<Vec<_>>();
      let exp_ts = ctr.fields.iter().map(|f| f.typ.subst(adt_s)).collect::<Vec<_>>();
      unify_fields(inf_ts.iter().zip(exp_ts.iter()), bod, state)?;

      // Recurse and unify with the other arms.
      let t_rest = infer_match_cases(env, book, types, adt, rest, adt_s, state)?;
      let t_final = state.unify_term(&t1, &t_rest, bod)?;

      Ok(state.prune(&t_final))
    } else {
      Ok(state.fresh())
    }
  })
}

fn unify_fields<'a>(
  ts: impl Iterator<Item = (&'a Type, &'a Type)>,
  ctx: &Term,
  state: &mut InferState,
) -> Result<(), String> {
  for (inf, exp) in ts {
    state.unify_term(inf, exp, ctx)?;
  }
  Ok(())
}

/// Specializes the inferred type against the type annotation.
/// This way, the annotation can be less general than the inferred type.
///
/// It also forces inferred 'Any' to the annotated, inferred types to
/// annotated 'Any' and fills 'Hole' with the inferred type.
///
/// Errors if the first type is not a superset of the second type.
fn specialize(inf: &Type, ann: &Type) -> Result<Type, String> {
  fn merge_specialization(inf: &Type, exp: &Type, s: &mut Subst) -> Result<Type, String> {
    maybe_grow(|| match (inf, exp) {
      // These rules have to come before
      (t, Type::Hole) => Ok(t.clone()),
      (Type::Hole, _) => unreachable!("Hole should never appear in the inferred type"),

      (_inf, Type::Any) => Ok(Type::Any),
      (Type::Any, exp) => Ok(exp.clone()),

      (Type::Var(x), new) => {
        if let Some(old) = s.0.get(x) {
          if old == new {
            Ok(new.clone())
          } else {
            Err(format!(" Inferred type variable '{x}' must be both '{old}' and '{new}'"))
          }
        } else {
          s.0.insert(x.clone(), new.clone());
          Ok(new.clone())
        }
      }

      (Type::Arr(l1, r1), Type::Arr(l2, r2)) => {
        let l = merge_specialization(l1, l2, s)?;
        let r = merge_specialization(r1, r2, s)?;
        Ok(Type::Arr(Box::new(l), Box::new(r)))
      }
      (Type::Ctr(name1, ts1), Type::Ctr(name2, ts2)) if name1 == name2 && ts1.len() == ts2.len() => {
        let mut ts = vec![];
        for (t1, t2) in ts1.iter().zip(ts2.iter()) {
          let t = merge_specialization(t1, t2, s)?;
          ts.push(t);
        }
        Ok(Type::Ctr(name1.clone(), ts))
      }
      (Type::Tup(ts1), Type::Tup(ts2)) if ts1.len() == ts2.len() => {
        let mut ts = vec![];
        for (t1, t2) in ts1.iter().zip(ts2.iter()) {
          let t = merge_specialization(t1, t2, s)?;
          ts.push(t);
        }
        Ok(Type::Tup(ts))
      }
      (Type::Number(t1), Type::Number(t2)) => Ok(Type::Number(Box::new(merge_specialization(t1, t2, s)?))),
      (Type::Integer(t1), Type::Integer(t2)) => Ok(Type::Integer(Box::new(merge_specialization(t1, t2, s)?))),
      (Type::U24, Type::U24) | (Type::F24, Type::F24) | (Type::I24, Type::I24) | (Type::None, Type::None) => {
        Ok(inf.clone())
      }
      _ => Err(String::new()),
    })
  }

  // Refresh the variable names to avoid conflicts when unifying
  // Names of type vars in the annotation have nothing to do with names in the inferred type.
  let var_gen = &mut VarGen::default();
  let inf2 = inf.generalize_closed().instantiate(var_gen);
  let ann2 = ann.generalize_closed().instantiate(var_gen);

  let mut state = InferState::default();
  let t = state
    .unify(&inf2, &ann2)
    .map_err(|e| format!("Type Error: Expected function type '{ann}' but found '{inf}'.{e}"))?;
  let t = state.prune(&t);

  // Merge the inferred specialization with the expected type.
  // This is done to cast to/from `Any` and `_` types.
  let mut merge_s = Subst::default();
  let t2 = merge_specialization(&t, ann, &mut merge_s).map_err(|e| {
    format!("Type Error: Annotated type '{ann}' is not a subtype of inferred type '{inf2}'.{e}")
  })?;

  Ok(t2.subst(&merge_s))
}

impl std::fmt::Display for Subst {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    writeln!(f, "Subst {{")?;
    for (x, y) in &self.0 {
      writeln!(f, "  {x} => {y},")?;
    }
    write!(f, "}}")
  }
}
