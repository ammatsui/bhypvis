// implements contexts
// rewrite rule application

use crate::hypergraph::Hypergraph;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DpoiRewrite {
    pub lhs: Hypergraph,
    pub rhs: Hypergraph,
    pub interface: Hypergraph,
    pub policy: Vec<String>,
}

impl DpoiRewrite {
    pub fn new(lhs: Hypergraph, rhs: Hypergraph, interface: Hypergraph, policy: Vec<String>) -> Self {
        Self {
            lhs,
            rhs,
            interface,
            policy,
        }
    }

    pub fn apply(&self, host: &Hypergraph) -> Result<Hypergraph, String> {
        self.lhs.safety_check()?;
        self.rhs.safety_check()?;
        host.safety_check()?;

        let mut rewritten = host.clone();
        for edge in &self.lhs.hyperedges().to_vec() {
            rewritten.remove_hyperedge_matching(|candidate| {
                candidate.label == edge.label && candidate.ports == edge.ports
            });
        }

        for edge in &self.rhs.hyperedges().to_vec() {
            rewritten.push_hyperedge(edge.clone());
        }

        if !self.policy.is_empty() {
            rewritten = Self::enforce_policy(&rewritten, &self.policy)?;
        }

        rewritten.safety_check()?;
        Ok(rewritten)
    }

    fn enforce_policy(graph: &Hypergraph, policy: &[String]) -> Result<Hypergraph, String> {
        let result = graph.clone();
        for rule in policy {
            if rule == "keep-interfaces" {
                for edge in result.hyperedges() {
                    if edge.label.is_empty() {
                        return Err("empty edge label found in policy enforcement".to_string());
                    }
                }
            }
        }
        Ok(result)
    }
}

pub fn rewrite_via_dpoi(
    host: &Hypergraph,
    lhs: &Hypergraph,
    rhs: &Hypergraph,
    interface: &Hypergraph,
    policy: Vec<String>,
) -> Result<Hypergraph, String> {
    let rewrite = DpoiRewrite::new(lhs.clone(), rhs.clone(), interface.clone(), policy);
    rewrite.apply(host)
}

#[cfg(test)]
mod tests {
    use super::DpoiRewrite;
    use crate::hypergraph::Hypergraph;

    #[test]
    fn dpoi_rewrite_applies_policy() {
        let mut lhs = Hypergraph::new();
        let a = lhs.add_node();
        let b = lhs.add_node();
        lhs.add_hyperedge("edge", vec![a, b]);

        let mut rhs = Hypergraph::new();
        let c = rhs.add_node();
        let d = rhs.add_node();
        rhs.add_hyperedge("edge2", vec![c, d]);

        let mut host = Hypergraph::new();
        let p = host.add_node();
        let q = host.add_node();
        host.add_hyperedge("edge", vec![p, q]);

        let rewrite = DpoiRewrite::new(lhs, rhs, Hypergraph::from_nodes(vec![0, 1]), vec!["keep-interfaces".to_string()]);
        let result = rewrite.apply(&host).unwrap();
        assert_eq!(result.hyperedges().len(), 1);
        assert_eq!(result.hyperedges()[0].label, "edge2");
    }
}
