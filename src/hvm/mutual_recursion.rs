use super::tree_children;
use crate::{
  diagnostics::{Diagnostics, WarningType, ERR_INDENT_SIZE},
  fun::transform::definition_merge::MERGE_SEPARATOR,
  maybe_grow,
};
use hvm::ast::{Book, Tree};
use indexmap::{IndexMap, IndexSet};
use std::fmt::Debug;

type Ref = String;
type RefSet = IndexSet<Ref>;

#[derive(Default)]
pub struct Graph(IndexMap<Ref, RefSet>);

pub fn check_cycles(book: &Book, diagnostics: &mut Diagnostics) -> Result<(), Diagnostics> {
  let graph = Graph::from(book);
  let cycles = graph.cycles();

  if !cycles.is_empty() {
    let msg = format!(include_str!("mutual_recursion.message"), cycles = show_cycles(cycles));
    diagnostics.add_book_warning(msg.as_str(), WarningType::RecursionCycle);
  }

  diagnostics.fatal(())
}
fn show_cycles(mut cycles: Vec<Vec<Ref>>) -> String {
  let tail = if cycles.len() > 5 {
    format!("\n{:ERR_INDENT_SIZE$}and {} other cycles...", "", cycles.len() - 5)
  } else {
    String::new()
  };

  cycles = cycles.into_iter().flat_map(combinations_from_merges).collect::<Vec<_>>();

  let mut cycles = cycles
    .iter()
    .take(5)
    .map(|cycle| {
      let cycle_str = cycle
        .iter()
        .filter(|nam| !nam.contains("__C"))
        .chain(cycle.first())
        .cloned()
        .collect::<Vec<_>>()
        .join(" -> ");
      format!("{:ERR_INDENT_SIZE$}* {}", "", cycle_str)
    })
    .collect::<Vec<String>>()
    .join("\n");

  cycles.push_str(&tail);

  cycles
}

impl Graph {
  pub fn cycles(&self) -> Vec<Vec<Ref>> {
    // REF-05 (`workspace/notes/isomorphic-optimization-reference.md`): use
    // Tarjan SCC state with O(1) `on_stack` membership instead of scanning the
    // DFS stack for every back edge.
    let tarjan = Tarjan::new(&self.0);
    let mut cycles = tarjan
      .cycles()
      .into_iter()
      .map(|cycle| self.representative_cycle(cycle))
      .collect::<Vec<_>>();
    cycles.sort_by_key(|cycle| (usize::from(cycle.len() == 1), self.first_index(cycle)));
    cycles
  }

  fn representative_cycle(&self, component: Vec<Ref>) -> Vec<Ref> {
    if component.len() <= 1 {
      return component;
    }

    let in_component = component.iter().cloned().collect::<RefSet>();
    let start = component
      .iter()
      .min_by_key(|r#ref| self.0.get_index_of(*r#ref).unwrap_or(usize::MAX))
      .cloned()
      .unwrap_or_else(|| component[0].clone());
    let mut path = vec![start.clone()];
    let mut on_path = RefSet::from([start.clone()]);
    if self.find_cycle_to_start(&start, &start, &in_component, &mut on_path, &mut path) {
      path
    } else {
      // Tarjan proved this is a recursive component, so this fallback should not
      // be reached. If it is, keep the component visible rather than dropping a
      // recursion diagnostic.
      component
    }
  }

  fn find_cycle_to_start(
    &self,
    current: &Ref,
    start: &Ref,
    in_component: &RefSet,
    on_path: &mut RefSet,
    path: &mut Vec<Ref>,
  ) -> bool {
    maybe_grow(|| {
      let Some(dependencies) = self.0.get(current) else {
        return false;
      };
      for dep in dependencies.iter().filter(|dep| in_component.contains(*dep)) {
        if dep == start && path.len() > 1 {
          return true;
        }
        if on_path.insert(dep.clone()) {
          path.push(dep.clone());
          if self.find_cycle_to_start(dep, start, in_component, on_path, path) {
            return true;
          }
          path.pop();
          on_path.shift_remove(dep);
        }
      }
      false
    })
  }

  fn first_index(&self, cycle: &[Ref]) -> usize {
    cycle.iter().filter_map(|r#ref| self.0.get_index_of(r#ref)).min().unwrap_or(usize::MAX)
  }
}

struct Tarjan<'a> {
  graph: &'a IndexMap<Ref, RefSet>,
  index: usize,
  indices: IndexMap<&'a Ref, usize>,
  lowlink: IndexMap<&'a Ref, usize>,
  stack: Vec<&'a Ref>,
  on_stack: IndexSet<&'a Ref>,
  cycles: Vec<Vec<Ref>>,
}

impl<'a> Tarjan<'a> {
  fn new(graph: &'a IndexMap<Ref, RefSet>) -> Self {
    Self {
      graph,
      index: 0,
      indices: IndexMap::new(),
      lowlink: IndexMap::new(),
      stack: Vec::new(),
      on_stack: IndexSet::new(),
      cycles: Vec::new(),
    }
  }

  fn cycles(mut self) -> Vec<Vec<Ref>> {
    for r#ref in self.graph.keys() {
      if !self.indices.contains_key(r#ref) {
        self.strong_connect(r#ref);
      }
    }
    self.cycles
  }

  fn strong_connect(&mut self, r#ref: &'a Ref) {
    maybe_grow(|| {
      self.indices.insert(r#ref, self.index);
      self.lowlink.insert(r#ref, self.index);
      self.index += 1;
      self.stack.push(r#ref);
      self.on_stack.insert(r#ref);

      if let Some(dependencies) = self.graph.get(r#ref) {
        for dep in dependencies {
          if !self.indices.contains_key(dep) {
            self.strong_connect(dep);
            let low = self.lowlink[r#ref].min(self.lowlink[dep]);
            self.lowlink.insert(r#ref, low);
          } else if self.on_stack.contains(dep) {
            let low = self.lowlink[r#ref].min(self.indices[dep]);
            self.lowlink.insert(r#ref, low);
          }
        }
      }

      if self.lowlink[r#ref] == self.indices[r#ref] {
        let mut component = Vec::new();
        while let Some(dep) = self.stack.pop() {
          self.on_stack.shift_remove(dep);
          component.push(dep.clone());
          if dep == r#ref {
            break;
          }
        }
        component.reverse();
        if component.len() > 1 {
          self.cycles.push(component);
        } else if let Some(node) = component.first() {
          if self.has_self_edge(node) {
            self.cycles.push(vec![node.clone()]);
          }
        }
      }
    })
  }

  fn has_self_edge(&self, node: &Ref) -> bool {
    self.graph.get(node).is_some_and(|deps| deps.contains(node))
  }
}

/// Collect active refs from the tree.
fn collect_refs(current: Ref, tree: &Tree, graph: &mut Graph) {
  maybe_grow(|| match tree {
    Tree::Ref { nam, .. } => graph.add(current, nam.clone()),
    Tree::Con { fst: _, snd } => collect_refs(current.clone(), snd, graph),
    tree => {
      for subtree in tree_children(tree) {
        collect_refs(current.clone(), subtree, graph);
      }
    }
  });
}

impl From<&Book> for Graph {
  fn from(book: &Book) -> Self {
    let mut graph = Self::new();

    for (r#ref, net) in book.defs.iter() {
      // Collect active refs from the root.
      collect_refs(r#ref.clone(), &net.root, &mut graph);

      // Collect active refs from redexes.
      for (_, left, right) in net.rbag.iter() {
        if let Tree::Ref { nam, .. } = left {
          graph.add(r#ref.clone(), nam.clone());
        }
        if let Tree::Ref { nam, .. } = right {
          graph.add(r#ref.clone(), nam.clone());
        }
      }
    }

    graph
  }
}

impl Graph {
  pub fn new() -> Self {
    Self::default()
  }

  pub fn add(&mut self, r#ref: Ref, dependency: Ref) {
    self.0.entry(r#ref).or_default().insert(dependency.clone());
    self.0.entry(dependency).or_default();
  }

  pub fn get(&self, r#ref: &Ref) -> Option<&RefSet> {
    self.0.get(r#ref)
  }
}

impl Debug for Graph {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "Graph{:?}", self.0)
  }
}

fn combinations_from_merges(cycle: Vec<Ref>) -> Vec<Vec<Ref>> {
  let mut combinations: Vec<Vec<Ref>> = vec![vec![]];
  for r#ref in cycle {
    if let Some(index) = r#ref.find(MERGE_SEPARATOR) {
      let (left, right) = r#ref.split_at(index);
      let right = &right[MERGE_SEPARATOR.len()..]; // skip merge separator
      let mut new_combinations = Vec::new();
      for combination in &combinations {
        let mut left_comb = combination.clone();
        left_comb.push(left.to_string());
        new_combinations.push(left_comb);

        let mut right_comb = combination.clone();
        right_comb.push(right.to_string());
        new_combinations.push(right_comb);
      }
      combinations = new_combinations;
    } else {
      for combination in &mut combinations {
        combination.push(r#ref.clone());
      }
    }
  }
  combinations
}
