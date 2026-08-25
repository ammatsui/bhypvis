use crate::hypergraph::Hypergraph;

pub fn to_dot(graph: &Hypergraph) -> String {
    let mut output = String::from("digraph hypergraph {\n");

    for node in graph.node_ids() {
        output.push_str(&format!("  n{node} [shape=circle];\n"));
    }

    for edge in graph.hyperedges() {
        let label = edge.label.replace('"', "\\\"");
        let ports = edge
            .ports
            .iter()
            .map(|port| format!("n{port}"))
            .collect::<Vec<_>>()
            .join(" ");

        output.push_str(&format!("  e{0} [label=\"{label}\", shape=box];\n", edge.id));
        if !ports.is_empty() {
            output.push_str(&format!("  {ports} -> e{0};\n", edge.id));
        }
    }

    output.push_str("}\n");
    output
}

pub fn write_dot(graph: &Hypergraph, file_path: &str) -> Result<(), std::io::Error> {
    std::fs::write(file_path, to_dot(graph))
}

#[cfg(test)]
mod tests {
    use super::to_dot;
    use crate::hypergraph::Hypergraph;

    #[test]
    fn dot_output_contains_nodes_and_edges() {
        let mut graph = Hypergraph::new();
        let a = graph.add_node();
        let b = graph.add_node();
        graph.add_hyperedge("f", vec![a, b]);

        let dot = to_dot(&graph);
        assert!(dot.contains("n0"));
        assert!(dot.contains("n1"));
        assert!(dot.contains("label=\"f\""));
    }
}
