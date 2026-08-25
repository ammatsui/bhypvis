// Defines hypergraphs with binding, 
// implements safety checks,
// copying, glueing

use std::collections::HashSet;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Hyperedge {
    pub id: usize,
    pub label: String,
    pub ports: Vec<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Hypergraph {
    nodes: Vec<usize>,
    hyperedges: Vec<Hyperedge>,
}

impl Hypergraph {
    pub fn new() -> Self {
        Self {
            nodes: Vec::new(),
            hyperedges: Vec::new(),
        }
    }

    pub fn from_nodes(nodes: Vec<usize>) -> Self {
        let mut graph = Self::new();
        graph.nodes = nodes;
        graph
    }

    pub fn add_node(&mut self) -> usize {
        let next = self
            .nodes
            .iter()
            .max()
            .copied()
            .map(|value| value + 1)
            .unwrap_or(0);
        self.nodes.push(next);
        next
    }

    pub fn add_hyperedge(&mut self, label: impl Into<String>, ports: Vec<usize>) -> usize {
        let id = self
            .hyperedges
            .iter()
            .map(|edge| edge.id)
            .max()
            .map(|value| value + 1)
            .unwrap_or(0);

        self.hyperedges.push(Hyperedge {
            id,
            label: label.into(),
            ports,
        });
        id
    }

    pub fn push_hyperedge(&mut self, edge: Hyperedge) {
        self.hyperedges.push(edge);
    }

    pub fn remove_hyperedge_matching(&mut self, predicate: impl Fn(&Hyperedge) -> bool) {
        self.hyperedges.retain(|edge| !predicate(edge));
    }

    pub fn node_ids(&self) -> &[usize] {
        &self.nodes
    }

    pub fn hyperedges(&self) -> &[Hyperedge] {
        &self.hyperedges
    }

    pub fn copy(&self) -> Self {
        self.clone()
    }

    pub fn glue(&self, other: &Self) -> Result<Self, String> {
        let mut merged = self.clone();
        for node in other.nodes.iter().copied() {
            if !merged.nodes.contains(&node) {
                merged.nodes.push(node);
            }
        }

        for edge in &other.hyperedges {
            if !merged
                .hyperedges
                .iter()
                .any(|candidate| candidate.label == edge.label && candidate.ports == edge.ports)
            {
                merged.hyperedges.push(edge.clone());
            }
        }

        merged.safety_check()?;
        Ok(merged)
    }

    pub fn safety_check(&self) -> Result<(), String> {
        let mut seen = HashSet::new();
        for node in &self.nodes {
            if !seen.insert(*node) {
                return Err(format!("duplicate node id detected: {node}"));
            }
        }

        for edge in &self.hyperedges {
            for port in &edge.ports {
                if !self.nodes.contains(port) {
                    return Err(format!(
                        "hyperedge '{}' references missing node {}",
                        edge.label, port
                    ));
                }
            }
        }

        Ok(())
    }
}

impl Default for Hypergraph {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::Hypergraph;

    #[test]
    fn copy_keeps_structure() {
        let mut graph = Hypergraph::new();
        let a = graph.add_node();
        let b = graph.add_node();
        graph.add_hyperedge("edge", vec![a, b]);

        let copy = graph.copy();
        assert_eq!(copy.node_ids(), graph.node_ids());
        assert_eq!(copy.hyperedges(), graph.hyperedges());
    }

    #[test]
    fn safety_check_rejects_missing_port() {
        let mut graph = Hypergraph::new();
        graph.add_node();
        graph.add_hyperedge("bad", vec![0, 99]);

        assert!(graph.safety_check().is_err());
    }
}
