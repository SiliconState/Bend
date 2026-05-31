use super::tree_children;
use crate::maybe_grow;
use hvm::ast::{Book, Net, Tree};
use std::collections::{HashMap, HashSet};

pub fn add_recursive_priority(book: &mut Book) {
  // Direct dependencies
  let deps = book.defs.iter().map(|(nam, net)| (nam.clone(), dependencies(net))).collect::<HashMap<_, _>>();
  // Recursive cycles
  let cycles = cycles(&deps);

  for cycle in cycles {
    // For each function in a recursive component, if there are repeated
    // redexes pointing to another function in that component, add priority.
    // REF-05 returns SCCs rather than one arbitrary simple cycle, so branching
    // recursive components still get all intra-component recursive edges.
    let in_cycle = cycle.iter().cloned().collect::<HashSet<_>>();
    for cur_name in &cycle {
      let nexts = deps
        .get(cur_name)
        .into_iter()
        .flat_map(|deps| deps.iter())
        .filter(|nxt| in_cycle.contains(*nxt))
        .cloned()
        .collect::<Vec<_>>();
      let cur = book.defs.get_mut(cur_name).unwrap();
      for nxt in nexts {
        add_priority_next_in_cycle(cur, &nxt);
      }
    }
  }
}

fn add_priority_next_in_cycle(net: &mut Net, nxt: &String) {
  let mut count = 0;

  // Count the number of recursive refs
  for (_, a, b) in net.rbag.iter() {
    if let Tree::Ref { nam } = a {
      if nam == nxt {
        count += 1;
      }
    }
    if let Tree::Ref { nam } = b {
      if nam == nxt {
        count += 1;
      }
    }
  }

  // If there are more than one recursive ref, add a priority to them.
  if count > 1 {
    for (pri, a, b) in net.rbag.iter_mut().rev() {
      if let Tree::Ref { nam } = a {
        if nam == nxt {
          *pri = true;
        }
      }
      if let Tree::Ref { nam } = b {
        if nam == nxt {
          *pri = true;
        }
      }
    }
  }
}

type DepGraph = HashMap<String, HashSet<String>>;
type Cycles = Vec<Vec<String>>;

/// Find all recursive strongly connected components in the dependency graph.
pub fn cycles(deps: &DepGraph) -> Cycles {
  // REF-05 (`workspace/notes/isomorphic-optimization-reference.md`): Tarjan
  // SCC with an explicit `on_stack` set replaces linear stack scans.
  let tarjan = Tarjan::new(deps);
  tarjan.cycles()
}

struct Tarjan<'a> {
  deps: &'a DepGraph,
  index: usize,
  indices: HashMap<&'a String, usize>,
  lowlink: HashMap<&'a String, usize>,
  stack: Vec<&'a String>,
  on_stack: HashSet<&'a String>,
  cycles: Cycles,
}

impl<'a> Tarjan<'a> {
  fn new(deps: &'a DepGraph) -> Self {
    Self {
      deps,
      index: 0,
      indices: HashMap::new(),
      lowlink: HashMap::new(),
      stack: Vec::new(),
      on_stack: HashSet::new(),
      cycles: Vec::new(),
    }
  }

  fn cycles(mut self) -> Cycles {
    let mut names = self.deps.keys().collect::<Vec<_>>();
    names.sort();
    for nam in names {
      if !self.indices.contains_key(nam) {
        self.strong_connect(nam);
      }
    }
    self.cycles.sort();
    self.cycles
  }

  fn strong_connect(&mut self, nam: &'a String) {
    maybe_grow(|| {
      self.indices.insert(nam, self.index);
      self.lowlink.insert(nam, self.index);
      self.index += 1;
      self.stack.push(nam);
      self.on_stack.insert(nam);

      if let Some(dependencies) = self.deps.get(nam) {
        let mut dependencies = dependencies.iter().collect::<Vec<_>>();
        dependencies.sort();
        for dep in dependencies {
          if !self.indices.contains_key(dep) {
            self.strong_connect(dep);
            let low = self.lowlink[nam].min(self.lowlink[dep]);
            self.lowlink.insert(nam, low);
          } else if self.on_stack.contains(dep) {
            let low = self.lowlink[nam].min(self.indices[dep]);
            self.lowlink.insert(nam, low);
          }
        }
      }

      if self.lowlink[nam] == self.indices[nam] {
        let mut component = Vec::new();
        while let Some(dep) = self.stack.pop() {
          self.on_stack.remove(dep);
          component.push(dep.clone());
          if dep == nam {
            break;
          }
        }
        component.sort();
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

  fn has_self_edge(&self, node: &String) -> bool {
    self.deps.get(node).is_some_and(|deps| deps.contains(node))
  }
}

/// Gather the set of net that this net directly depends on (has a ref in the net).
fn dependencies(net: &Net) -> HashSet<String> {
  let mut deps = HashSet::new();
  dependencies_tree(&net.root, &mut deps);
  for (_, a, b) in &net.rbag {
    dependencies_tree(a, &mut deps);
    dependencies_tree(b, &mut deps);
  }
  deps
}

fn dependencies_tree(tree: &Tree, deps: &mut HashSet<String>) {
  if let Tree::Ref { nam, .. } = tree {
    deps.insert(nam.clone());
  } else {
    for subtree in tree_children(tree) {
      dependencies_tree(subtree, deps);
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  fn set(items: &[&str]) -> HashSet<String> {
    items.iter().map(|item| (*item).to_string()).collect()
  }

  #[test]
  fn cycles_returns_full_branching_scc() {
    let deps = HashMap::from([
      ("A".to_string(), set(&["B", "C"])),
      ("B".to_string(), set(&["A"])),
      ("C".to_string(), set(&["A"])),
      ("D".to_string(), set(&["E"])),
      ("E".to_string(), HashSet::new()),
    ]);

    assert_eq!(cycles(&deps), vec![vec!["A".to_string(), "B".to_string(), "C".to_string()]]);
  }

  #[test]
  fn cycles_keeps_self_edges() {
    let deps = HashMap::from([("A".to_string(), set(&["A"])), ("B".to_string(), HashSet::new())]);

    assert_eq!(cycles(&deps), vec![vec!["A".to_string()]]);
  }
}
