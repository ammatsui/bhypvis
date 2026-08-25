// implements metavariable substitution

use crate::hypergraph::Hypergraph;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RewriteError {
    pub message: String,
}

impl RewriteError {
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl std::fmt::Display for RewriteError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for RewriteError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Production {
    pub lhs: Hypergraph,
    pub rhs: Hypergraph,
    pub interface: Hypergraph,
}

impl Production {
    pub fn new(lhs: Hypergraph, rhs: Hypergraph, interface: Hypergraph) -> Result<Self, String> {
        lhs.safety_check()?;
        rhs.safety_check()?;
        interface.safety_check()?;

        Ok(Self {
            lhs,
            rhs,
            interface,
        })
    }

    pub fn matches(&self, host: &Hypergraph) -> Result<(), String> {
        self.lhs.safety_check()?;
        host.safety_check()?;

        let lhs_nodes = self.lhs.node_ids();
        let host_nodes = host.node_ids();

        for node in lhs_nodes {
            if !host_nodes.contains(node) {
                return Err(format!("host graph is missing node {node} required by LHS"));
            }
        }

        Ok(())
    }

    pub fn apply_dpo(&self, host: &Hypergraph) -> Result<Hypergraph, String> {
        self.matches(host)?;

        let mut rewritten = host.clone();

        for edge in self.lhs.hyperedges() {
            let matches = rewritten
                .hyperedges()
                .iter()
                .any(|candidate| candidate.label == edge.label && candidate.ports == edge.ports);
            if matches {
                rewritten.remove_hyperedge_matching(|candidate| {
                    candidate.label == edge.label && candidate.ports == edge.ports
                });
                break;
            }
        }

        for edge in self.rhs.hyperedges() {
            rewritten.push_hyperedge(edge.clone());
        }

        rewritten.safety_check()?;
        Ok(rewritten)
    }
}

pub fn substitute_via_dpo(
    host: &Hypergraph,
    lhs: &Hypergraph,
    rhs: &Hypergraph,
    interface: &Hypergraph,
) -> Result<Hypergraph, String> {
    let production = Production::new(lhs.clone(), rhs.clone(), interface.clone())?;
    production.apply_dpo(host)
}

#[cfg(test)]
mod tests {
    use super::Production;
    use crate::hypergraph::Hypergraph;

    #[test]
    fn dpo_rewrite_matches_lhs() {
        let mut lhs = Hypergraph::new();
        let a = lhs.add_node();
        let b = lhs.add_node();
        lhs.add_hyperedge("edge", vec![a, b]);

        let mut rhs = Hypergraph::new();
        let c = rhs.add_node();
        let d = rhs.add_node();
        rhs.add_hyperedge("edge2", vec![c, d]);

        let interface = Hypergraph::from_nodes(vec![a, b]);
        let production = Production::new(lhs, rhs, interface).unwrap();

        let mut host = Hypergraph::new();
        let p = host.add_node();
        let q = host.add_node();
        host.add_hyperedge("edge", vec![p, q]);

        let result = production.apply_dpo(&host).unwrap();
        assert_eq!(result.hyperedges().len(), 1);
        assert_eq!(result.hyperedges()[0].label, "edge2");
    }
}
