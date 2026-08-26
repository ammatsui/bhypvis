//! DOT language visualization for Hypergraphs with Binding
//! 
//! This module provides functions to generate GraphViz DOT format output
//! for visualizing BHyp and BHyp_with_interface structures.

use std::fmt::Write;
use std::collections::HashSet;

use crate::bhyp::{BHyp, BHyp_with_interface, Label, NodeId, EdgeId, SourceWithBinding};

/// Configuration options for DOT visualization
#[derive(Debug, Clone)]
pub struct DotConfig {
    /// Whether to show edge labels
    pub show_labels: bool,
    /// Whether to show node IDs
    pub show_node_ids: bool,
    /// Whether to use rankdir LR (left-to-right) or TB (top-to-bottom)
    pub left_to_right: bool,
    /// Color for input interface nodes
    pub input_color: String,
    /// Color for output interface nodes
    pub output_color: String,
    /// Color for internal nodes
    pub internal_color: String,
    /// Color for bound nodes
    pub bound_color: String,
    /// Color for binding connections
    pub binding_edge_color: String,
    /// Color for metaedges
    pub metaedge_color: String,
    /// Font name
    pub font_name: String,
    /// Font size
    pub font_size: u32,
}

impl Default for DotConfig {
    fn default() -> Self {
        DotConfig {
            show_labels: true,
            show_node_ids: false,
            left_to_right: true,
            input_color: "green".to_string(),
            output_color: "red".to_string(),
            internal_color: "black".to_string(),
            bound_color: "blue".to_string(),
            binding_edge_color: "blue".to_string(),
            metaedge_color: "orange".to_string(),
            font_name: "Helvetica".to_string(),
            font_size: 12,
        }
    }
}

impl DotConfig {
    /// Create a config for unlabeled visualization
    pub fn unlabeled() -> Self {
        DotConfig {
            show_labels: false,
            ..Default::default()
        }
    }

    /// Create a config showing node IDs
    pub fn with_node_ids() -> Self {
        DotConfig {
            show_node_ids: true,
            ..Default::default()
        }
    }
}

/// Generate DOT representation for a BHyp
pub fn bhyp_to_dot(bhyp: &BHyp, config: &DotConfig) -> String {
    bhyp_to_dot_with_name(bhyp, "G", config)
}

/// Generate DOT representation for a BHyp with a custom graph name
pub fn bhyp_to_dot_with_name(bhyp: &BHyp, name: &str, config: &DotConfig) -> String {
    let mut dot = String::new();

    // Graph header
    writeln!(dot, "digraph {} {{", name).unwrap();
    writeln!(dot, "  fontname=\"{}\"", config.font_name).unwrap();
    writeln!(dot, "  fontsize={}", config.font_size).unwrap();
    if config.left_to_right {
        writeln!(dot, "  rankdir=LR;").unwrap();
    }
    writeln!(dot, "  node [fontname=\"{}\", fontsize={}];", config.font_name, config.font_size).unwrap();
    writeln!(dot, "  edge [fontname=\"{}\", fontsize={}];", config.font_name, config.font_size).unwrap();
    writeln!(dot).unwrap();

    // Collect bound nodes for special coloring
    let bound_nodes: HashSet<NodeId> = bhyp.edges().iter()
        .filter_map(|&e| bhyp.get_sources_with_binding(e))
        .flat_map(|swbs| swbs.iter())
        .flat_map(|swb| swb.bound.iter().copied())
        .collect();

    // Generate nodes
    writeln!(dot, "  // Nodes").unwrap();
    for &node in bhyp.nodes() {
        let node_label = if config.show_node_ids {
            format!("{}", node.0)
        } else {
            "".to_string()
        };

        let color = if bound_nodes.contains(&node) {
            &config.bound_color
        } else {
            &config.internal_color
        };

        writeln!(
            dot,
            "  n{} [label=\"{}\", shape=circle, style=filled, fillcolor=white, color=\"{}\", width=0.2, height=0.2, fixedsize=true];",
            node.0, node_label, color
        ).unwrap();
    }
    writeln!(dot).unwrap();

    // Generate edge nodes (hyperedges are represented as boxes)
    writeln!(dot, "  // Hyperedges").unwrap();
    for &edge in bhyp.edges() {
        let is_meta = bhyp.is_metaedge(edge);
        let label = if config.show_labels {
            bhyp.get_label(edge)
                .map(|l| format_label(l))
                .unwrap_or_else(|| "".to_string())
        } else {
            "".to_string()
        };

        let (shape, color) = if is_meta {
            ("ellipse", &config.metaedge_color)
        } else {
            ("box", &config.internal_color)
        };

        writeln!(
            dot,
            "  e{} [label=\"{}\", shape={}, style=rounded, color=\"{}\"];",
            edge.0, label, shape, color
        ).unwrap();
    }
    writeln!(dot).unwrap();

    // Generate edges (connections between nodes and hyperedges)
    writeln!(dot, "  // Source connections").unwrap();
    for &edge in bhyp.edges() {
        if let Some(swbs) = bhyp.get_sources_with_binding(edge) {
            for (i, swb) in swbs.iter().enumerate() {
                // Source -> Edge connection
                let source_label = if swbs.len() > 1 {
                    format!("{}", i)
                } else {
                    "".to_string()
                };
                writeln!(
                    dot,
                    "  n{} -> e{} [label=\"{}\"];",
                    swb.source.0, edge.0, source_label
                ).unwrap();

                // Binding connections (dashed, going to bound nodes)
                for (j, &bound) in swb.bound.iter().enumerate() {
                    writeln!(
                        dot,
                        "  n{} -> e{} [style=dashed, color=\"{}\", constraint=false, label=\"b{},{}\"];",
                        bound.0, edge.0, config.binding_edge_color, i, j
                    ).unwrap();
                }
            }
        }
    }
    writeln!(dot).unwrap();

    writeln!(dot, "  // Target connections").unwrap();
    for &edge in bhyp.edges() {
        if let Some(targets) = bhyp.get_targets(edge) {
            for (i, &target) in targets.iter().enumerate() {
                let target_label = if targets.len() > 1 {
                    format!("{}", i)
                } else {
                    "".to_string()
                };
                writeln!(
                    dot,
                    "  e{} -> n{} [label=\"{}\"];",
                    edge.0, target.0, target_label
                ).unwrap();
            }
        }
    }

    writeln!(dot, "}}").unwrap();
    dot
}

/// Generate DOT representation for a BHyp_with_interface as a cospan diagram
pub fn bhyp_with_interface_to_dot(bhyp_i: &BHyp_with_interface, config: &DotConfig) -> String {
    let mut dot = String::new();

    writeln!(dot, "digraph BHypWithInterface {{").unwrap();
    writeln!(dot, "  fontname=\"{}\"", config.font_name).unwrap();
    writeln!(dot, "  fontsize={}", config.font_size).unwrap();
    writeln!(dot, "  compound=true;").unwrap();
    if config.left_to_right {
        writeln!(dot, "  rankdir=LR;").unwrap();
    }
    writeln!(dot, "  node [fontname=\"{}\", fontsize={}];", config.font_name, config.font_size).unwrap();
    writeln!(dot, "  edge [fontname=\"{}\", fontsize={}];", config.font_name, config.font_size).unwrap();
    writeln!(dot).unwrap();

    // Subgraph for input interface (I_G)
    writeln!(dot, "  subgraph cluster_input {{").unwrap();
    writeln!(dot, "    label=\"I_G\";").unwrap();
    writeln!(dot, "    style=dashed;").unwrap();
    writeln!(dot, "    color=\"{}\";", config.input_color).unwrap();
    for &node in bhyp_i.input_interface().nodes() {
        let label = if config.show_node_ids {
            format!("i{}", node.0)
        } else {
            "".to_string()
        };
        writeln!(
            dot,
            "    i{} [label=\"{}\", shape=circle, style=filled, fillcolor=\"{}\", width=0.3, height=0.3, fixedsize=true];",
            node.0, label, config.input_color
        ).unwrap();
    }
    writeln!(dot, "  }}").unwrap();
    writeln!(dot).unwrap();

    // Subgraph for the main hypergraph (G)
    writeln!(dot, "  subgraph cluster_main {{").unwrap();
    writeln!(dot, "    label=\"G\";").unwrap();
    writeln!(dot, "    style=solid;").unwrap();
    
    let input_nodes = bhyp_i.input_interface_nodes();
    let output_nodes = bhyp_i.output_interface_nodes();
    let bound_nodes: HashSet<NodeId> = bhyp_i.bhyp().edges().iter()
        .filter_map(|&e| bhyp_i.bhyp().get_sources_with_binding(e))
        .flat_map(|swbs| swbs.iter())
        .flat_map(|swb| swb.bound.iter().copied())
        .collect();

    // Nodes in main graph
    for &node in bhyp_i.nodes() {
        let label = if config.show_node_ids {
            format!("{}", node.0)
        } else {
            "".to_string()
        };

        let color = if input_nodes.contains(&node) && output_nodes.contains(&node) {
            "purple" // Both input and output
        } else if input_nodes.contains(&node) {
            &config.input_color
        } else if output_nodes.contains(&node) {
            &config.output_color
        } else if bound_nodes.contains(&node) {
            &config.bound_color
        } else {
            &config.internal_color
        };

        writeln!(
            dot,
            "    n{} [label=\"{}\", shape=circle, style=filled, fillcolor=white, color=\"{}\", width=0.2, height=0.2, fixedsize=true];",
            node.0, label, color
        ).unwrap();
    }

    // Hyperedges
    for &edge in bhyp_i.edges() {
        let is_meta = bhyp_i.bhyp().is_metaedge(edge);
        let label = if config.show_labels {
            bhyp_i.get_label(edge)
                .map(|l| format_label(l))
                .unwrap_or_else(|| "".to_string())
        } else {
            "".to_string()
        };

        let (shape, color) = if is_meta {
            ("ellipse", &config.metaedge_color)
        } else {
            ("box", &config.internal_color)
        };

        writeln!(
            dot,
            "    e{} [label=\"{}\", shape={}, style=rounded, color=\"{}\"];",
            edge.0, label, shape, color
        ).unwrap();
    }

    // Source and target connections within main graph
    for &edge in bhyp_i.edges() {
        if let Some(swbs) = bhyp_i.get_sources_with_binding(edge) {
            for (i, swb) in swbs.iter().enumerate() {
                let source_label = if swbs.len() > 1 { format!("{}", i) } else { "".to_string() };
                writeln!(dot, "    n{} -> e{} [label=\"{}\"];", swb.source.0, edge.0, source_label).unwrap();

                for (j, &bound) in swb.bound.iter().enumerate() {
                    writeln!(
                        dot,
                        "    n{} -> e{} [style=dashed, color=\"{}\", constraint=false, label=\"b{},{}\"];",
                        bound.0, edge.0, config.binding_edge_color, i, j
                    ).unwrap();
                }
            }
        }
        if let Some(targets) = bhyp_i.get_targets(edge) {
            for (i, &target) in targets.iter().enumerate() {
                let target_label = if targets.len() > 1 { format!("{}", i) } else { "".to_string() };
                writeln!(dot, "    e{} -> n{} [label=\"{}\"];", edge.0, target.0, target_label).unwrap();
            }
        }
    }
    writeln!(dot, "  }}").unwrap();
    writeln!(dot).unwrap();

    // Subgraph for output interface (O_G)
    writeln!(dot, "  subgraph cluster_output {{").unwrap();
    writeln!(dot, "    label=\"O_G\";").unwrap();
    writeln!(dot, "    style=dashed;").unwrap();
    writeln!(dot, "    color=\"{}\";", config.output_color).unwrap();
    for &node in bhyp_i.output_interface().nodes() {
        let label = if config.show_node_ids {
            format!("o{}", node.0)
        } else {
            "".to_string()
        };
        writeln!(
            dot,
            "    o{} [label=\"{}\", shape=circle, style=filled, fillcolor=\"{}\", width=0.3, height=0.3, fixedsize=true];",
            node.0, label, config.output_color
        ).unwrap();
    }
    writeln!(dot, "  }}").unwrap();
    writeln!(dot).unwrap();

    // Interface morphisms (I_G -> G and O_G -> G)
    writeln!(dot, "  // Interface morphisms").unwrap();
    for (iface_node, &bhyp_node) in bhyp_i.input_map() {
        writeln!(
            dot,
            "  i{} -> n{} [style=dotted, color=\"{}\", label=\"\", lhead=cluster_main];",
            iface_node.0, bhyp_node.0, config.input_color
        ).unwrap();
    }
    for (iface_node, &bhyp_node) in bhyp_i.output_map() {
        writeln!(
            dot,
            "  n{} -> o{} [style=dotted, color=\"{}\", label=\"\", ltail=cluster_main];",
            bhyp_node.0, iface_node.0, config.output_color
        ).unwrap();
    }

    writeln!(dot, "}}").unwrap();
    dot
}

/// Generate a simple DOT representation showing the cospan structure
pub fn bhyp_with_interface_cospan_to_dot(bhyp_i: &BHyp_with_interface, config: &DotConfig) -> String {
    let mut dot = String::new();

    writeln!(dot, "digraph Cospan {{").unwrap();
    writeln!(dot, "  fontname=\"{}\"", config.font_name).unwrap();
    writeln!(dot, "  rankdir=LR;").unwrap();
    writeln!(dot).unwrap();

    // Three boxes for I_G, G, O_G
    writeln!(dot, "  I_G [label=\"I_G\\n({} nodes)\", shape=box, style=filled, fillcolor=lightgreen];",
             bhyp_i.input_interface().nodes().len()).unwrap();
    writeln!(dot, "  G [label=\"G\\n({} nodes, {} edges)\", shape=box, style=filled, fillcolor=lightblue];",
             bhyp_i.nodes().len(), bhyp_i.edges().len()).unwrap();
    writeln!(dot, "  O_G [label=\"O_G\\n({} nodes)\", shape=box, style=filled, fillcolor=lightcoral];",
             bhyp_i.output_interface().nodes().len()).unwrap();

    // Arrows representing the cospan
    writeln!(dot, "  I_G -> G [label=\"\"];").unwrap();
    writeln!(dot, "  O_G -> G [label=\"\", dir=back];").unwrap();

    writeln!(dot, "}}").unwrap();
    dot
}

/// Generate DOT for a discrete BHyp (just nodes)
pub fn discrete_bhyp_to_dot(bhyp: &BHyp, name: &str, config: &DotConfig) -> String {
    let mut dot = String::new();

    writeln!(dot, "digraph {} {{", name).unwrap();
    writeln!(dot, "  fontname=\"{}\"", config.font_name).unwrap();
    writeln!(dot, "  label=\"{} (discrete, {} nodes)\";", name, bhyp.nodes().len()).unwrap();
    if config.left_to_right {
        writeln!(dot, "  rankdir=LR;").unwrap();
    }
    writeln!(dot).unwrap();

    for &node in bhyp.nodes() {
        let label = if config.show_node_ids {
            format!("{}", node.0)
        } else {
            "".to_string()
        };
        writeln!(
            dot,
            "  n{} [label=\"{}\", shape=circle, style=filled, fillcolor=white, width=0.2, height=0.2, fixedsize=true];",
            node.0, label
        ).unwrap();
    }

    writeln!(dot, "}}").unwrap();
    dot
}

/// Convenience function to generate labeled DOT
pub fn bhyp_to_dot_labeled(bhyp: &BHyp) -> String {
    bhyp_to_dot(bhyp, &DotConfig::default())
}

/// Convenience function to generate unlabeled DOT
pub fn bhyp_to_dot_unlabeled(bhyp: &BHyp) -> String {
    bhyp_to_dot(bhyp, &DotConfig::unlabeled())
}

/// Convenience function for BHyp_with_interface labeled
pub fn bhyp_with_interface_to_dot_labeled(bhyp_i: &BHyp_with_interface) -> String {
    bhyp_with_interface_to_dot(bhyp_i, &DotConfig::default())
}

/// Convenience function for BHyp_with_interface unlabeled
pub fn bhyp_with_interface_to_dot_unlabeled(bhyp_i: &BHyp_with_interface) -> String {
    bhyp_with_interface_to_dot(bhyp_i, &DotConfig::unlabeled())
}

fn format_label(label: &Label) -> String {
    match label {
        Label::Symbol(s) => s.clone(),
        Label::Meta(name, arity) => format!("{}:{}", name, arity),
    }
}

#[cfg(test)]
mod dot_tests {
    use super::*;

    #[test]
    fn test_simple_bhyp_dot() {
        let mut g = BHyp::new();
        let n1 = g.add_node();
        let n2 = g.add_node();
        g.add_edge(
            vec![SourceWithBinding { source: n1, bound: vec![] }],
            vec![n2],
            Some(Label::Symbol("f".to_string())),
        ).unwrap();

        let dot = bhyp_to_dot_labeled(&g);
        assert!(dot.contains("digraph"));
        assert!(dot.contains("n0"));
        assert!(dot.contains("n1"));
        assert!(dot.contains("e0"));
        assert!(dot.contains("\"f\""));
        println!("{}", dot);
    }

    #[test]
    fn test_lambda_binding_dot() {
        let mut g = BHyp::new();
        let x = g.add_node();      // bound variable
        let f_out = g.add_node();  // output of f(x)
        let lambda_out = g.add_node(); // output

        // f(x)
        g.add_edge(
            vec![SourceWithBinding { source: x, bound: vec![] }],
            vec![f_out],
            Some(Label::Symbol("f".to_string())),
        ).unwrap();

        // λx binds x
        g.add_edge(
            vec![SourceWithBinding { source: f_out, bound: vec![x] }],
            vec![lambda_out],
            Some(Label::Symbol("λ".to_string())),
        ).unwrap();

        let dot = bhyp_to_dot_labeled(&g);
        assert!(dot.contains("style=dashed")); // binding connection
        assert!(dot.contains("\"λ\""));
        println!("{}", dot);
    }

    #[test]
    fn test_metaedge_dot() {
        let mut g = BHyp::new();
        let n1 = g.add_node();
        let n2 = g.add_node();
        g.add_edge(
            vec![SourceWithBinding { source: n1, bound: vec![] }],
            vec![n2],
            Some(Label::Meta("M".to_string(), 1)),
        ).unwrap();

        let dot = bhyp_to_dot_labeled(&g);
        assert!(dot.contains("ellipse")); // metaedges are ellipses
        assert!(dot.contains("M:1"));
        println!("{}", dot);
    }

    #[test]
    fn test_bhyp_with_interface_dot() {
        let mut g = BHyp_with_interface::new();
        let n1 = g.add_node();
        let n2 = g.add_node();
        g.add_edge(
            vec![SourceWithBinding { source: n1, bound: vec![] }],
            vec![n2],
            Some(Label::Symbol("f".to_string())),
        ).unwrap();

        let dot = bhyp_with_interface_to_dot_labeled(&g);
        assert!(dot.contains("cluster_input"));
        assert!(dot.contains("cluster_main"));
        assert!(dot.contains("cluster_output"));
        assert!(dot.contains("I_G"));
        assert!(dot.contains("O_G"));
        println!("{}", dot);
    }

    #[test]
    fn test_cospan_diagram() {
        let mut g = BHyp_with_interface::new();
        let n1 = g.add_node();
        let n2 = g.add_node();
        g.add_edge(
            vec![SourceWithBinding { source: n1, bound: vec![] }],
            vec![n2],
            None,
        ).unwrap();

        let dot = bhyp_with_interface_cospan_to_dot(&g, &DotConfig::default());
        assert!(dot.contains("I_G"));
        assert!(dot.contains("O_G"));
        assert!(dot.contains("->"));
        println!("{}", dot);
    }

    #[test]
    fn test_discrete_bhyp_dot() {
        let mut g = BHyp::new();
        g.add_nodes(3);

        let dot = discrete_bhyp_to_dot(&g, "Discrete", &DotConfig::with_node_ids());
        assert!(dot.contains("discrete"));
        assert!(dot.contains("3 nodes"));
        println!("{}", dot);
    }

    #[test]
    fn test_unlabeled_dot() {
        let mut g = BHyp::new();
        let n1 = g.add_node();
        let n2 = g.add_node();
        g.add_edge(
            vec![SourceWithBinding { source: n1, bound: vec![] }],
            vec![n2],
            Some(Label::Symbol("should_not_appear".to_string())),
        ).unwrap();

        let dot = bhyp_to_dot_unlabeled(&g);
        assert!(!dot.contains("should_not_appear"));
        println!("{}", dot);
    }

    #[test]
    fn test_example_3_2_from_paper() {
        // Example 3.2 from the paper: 3 edges, 5 vertices
        // t(1)={b}, t(2)={d}, t(3)={e}
        // s(1)={a}, s(2)=∅, s(3)={c}
        // b(1)={∅}, b(2)=∅, b(3)={{a}}
        
        let mut g = BHyp::new();
        let a = g.add_node(); // 0
        let b = g.add_node(); // 1
        let c = g.add_node(); // 2
        let d = g.add_node(); // 3
        let e = g.add_node(); // 4

        // Edge 1: s={a}, t={b}, b={∅}
        g.add_edge(
            vec![SourceWithBinding { source: a, bound: vec![] }],
            vec![b],
            Some(Label::Symbol("1".to_string())),
        ).unwrap();

        // Edge 2: s=∅, t={d}, b=∅
        g.add_edge(
            vec![],
            vec![d],
            Some(Label::Symbol("2".to_string())),
        ).unwrap();

        // Edge 3: s={c}, t={e}, b={{a}} - a is bound at source c
        g.add_edge(
            vec![SourceWithBinding { source: c, bound: vec![a] }],
            vec![e],
            Some(Label::Symbol("3".to_string())),
        ).unwrap();

        let dot = bhyp_to_dot(&g, &DotConfig::with_node_ids());
        println!("Example 3.2 from paper:\n{}", dot);
        
        // The binding from edge 3 to node a should appear as dashed
        assert!(dot.contains("style=dashed"));
    }
}