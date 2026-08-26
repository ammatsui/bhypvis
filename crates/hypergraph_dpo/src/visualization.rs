//! DOT language visualization for Hypergraphs with Binding
//! 
//! This module provides functions to generate GraphViz DOT format output
//! for visualizing BHyp and BHyp_with_interface structures.

use std::fmt::Write;
use std::collections::HashSet;

use crate::bhyp::{BHyp, BHyp_with_interface, Label, NodeId, EdgeId, SourceWithBinding};
use crate::categorical::{BHypMorphism, PushoutResult, DPOResult};

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

// ============================================================================
// Categorical Visualization: Morphisms, Pushouts, and DPO
// ============================================================================

/// Generate DOT representation for a morphism between two BHyp objects
/// Shows domain and codomain as side-by-side subgraphs with mapping arrows
pub fn morphism_to_dot(morphism: &BHypMorphism, config: &DotConfig) -> String {
    let mut dot = String::new();

    writeln!(dot, "digraph Morphism {{").unwrap();
    writeln!(dot, "  fontname=\"{}\"", config.font_name).unwrap();
    writeln!(dot, "  rankdir=LR;").unwrap();
    writeln!(dot, "  compound=true;").unwrap();
    writeln!(dot).unwrap();

    // Left subgraph: Domain
    writeln!(dot, "  subgraph cluster_domain {{").unwrap();
    writeln!(dot, "    label=\"Domain\";").unwrap();
    writeln!(dot, "    style=filled;").unwrap();
    writeln!(dot, "    fillcolor=lightblue;").unwrap();
    writeln!(dot, "    node [fontname=\"{}\", fontsize={}];", config.font_name, config.font_size).unwrap();

    let domain = morphism.domain();
    for &node in domain.nodes() {
        let label = format!("d{}", node.0);
        writeln!(
            dot,
            "    d{} [label=\"{}\", shape=circle, style=filled, fillcolor=white, width=0.3, height=0.3, fixedsize=true];",
            node.0, label
        ).unwrap();
    }

    for &edge in domain.edges() {
        let label = domain.get_label(edge)
            .map(|l| format_label(l))
            .unwrap_or_else(|| format!("e{}", edge.0));
        writeln!(
            dot,
            "    de{} [label=\"{}\", shape=box, style=rounded];",
            edge.0, label
        ).unwrap();
    }

    for &edge in domain.edges() {
        if let Some(swbs) = domain.get_sources_with_binding(edge) {
            for swb in swbs {
                writeln!(dot, "    d{} -> de{};", swb.source.0, edge.0).unwrap();
            }
        }
        if let Some(targets) = domain.get_targets(edge) {
            for t in targets {
                writeln!(dot, "    de{} -> d{};", edge.0, t.0).unwrap();
            }
        }
    }

    writeln!(dot, "  }}").unwrap();
    writeln!(dot).unwrap();

    // Right subgraph: Codomain
    writeln!(dot, "  subgraph cluster_codomain {{").unwrap();
    writeln!(dot, "    label=\"Codomain\";").unwrap();
    writeln!(dot, "    style=filled;").unwrap();
    writeln!(dot, "    fillcolor=lightcoral;").unwrap();
    writeln!(dot, "    node [fontname=\"{}\", fontsize={}];", config.font_name, config.font_size).unwrap();

    let codomain = morphism.codomain();
    for &node in codomain.nodes() {
        let label = format!("c{}", node.0);
        writeln!(
            dot,
            "    c{} [label=\"{}\", shape=circle, style=filled, fillcolor=white, width=0.3, height=0.3, fixedsize=true];",
            node.0, label
        ).unwrap();
    }

    for &edge in codomain.edges() {
        let label = codomain.get_label(edge)
            .map(|l| format_label(l))
            .unwrap_or_else(|| format!("e{}", edge.0));
        writeln!(
            dot,
            "    ce{} [label=\"{}\", shape=box, style=rounded];",
            edge.0, label
        ).unwrap();
    }

    for &edge in codomain.edges() {
        if let Some(swbs) = codomain.get_sources_with_binding(edge) {
            for swb in swbs {
                writeln!(dot, "    c{} -> ce{};", swb.source.0, edge.0).unwrap();
            }
        }
        if let Some(targets) = codomain.get_targets(edge) {
            for t in targets {
                writeln!(dot, "    ce{} -> c{};", edge.0, t.0).unwrap();
            }
        }
    }

    writeln!(dot, "  }}").unwrap();
    writeln!(dot).unwrap();

    // Mapping arrows
    writeln!(dot, "  // Function arrows (node mappings)").unwrap();
    for (&domain_node, &codomain_node) in morphism.on_nodes() {
        writeln!(
            dot,
            "  d{} -> c{} [style=dashed, color=green, ltail=cluster_domain, lhead=cluster_codomain];",
            domain_node.0, codomain_node.0
        ).unwrap();
    }

    writeln!(dot, "}}").unwrap();
    dot
}

/// Generate DOT representation for a pushout square
/// Shows the four objects and four morphisms in a square arrangement
pub fn pushout_to_dot(
    c: &BHyp,
    a: &BHyp,
    b: &BHyp,
    pushout_result: &PushoutResult,
    config: &DotConfig,
) -> String {
    let mut dot = String::new();

    writeln!(dot, "digraph PushoutSquare {{").unwrap();
    writeln!(dot, "  fontname=\"{}\"", config.font_name).unwrap();
    writeln!(dot, "  rankdir=LR;").unwrap();
    writeln!(dot, "  compound=true;").unwrap();
    writeln!(dot, "  node [fontname=\"{}\", fontsize={}];", config.font_name, config.font_size).unwrap();
    writeln!(dot).unwrap();

    // Define graph clusters for each object
    let graph_clusters = vec![
        ("C (pullback)", c, "lightgreen", 0),
        ("A", a, "lightblue", 1),
        ("B", b, "lightyellow", 2),
        ("P (pushout)", &pushout_result.pushout, "lightcoral", 3),
    ];

    for (name, bhyp, color, idx) in graph_clusters {
        writeln!(dot, "  subgraph cluster_{} {{", idx).unwrap();
        writeln!(dot, "    label=\"{}\";", name).unwrap();
        writeln!(dot, "    style=filled;").unwrap();
        writeln!(dot, "    fillcolor={};", color).unwrap();
        writeln!(dot, "    node [shape=circle, style=filled, fillcolor=white];").unwrap();

        for &node in bhyp.nodes() {
            writeln!(dot, "    n{}_{} [label=\"\"];", idx, node.0).unwrap();
        }

        writeln!(dot, "  }}").unwrap();
        writeln!(dot).unwrap();
    }

    // Morphism arrows
    writeln!(dot, "  // Morphisms").unwrap();
    writeln!(dot, "  n0_0 -> n1_0 [label=\"f: C→A\"];").unwrap();
    writeln!(dot, "  n0_0 -> n2_0 [label=\"g: C→B\"];").unwrap();
    writeln!(dot, "  n1_0 -> n3_0 [label=\"f': A→P\"];").unwrap();
    writeln!(dot, "  n2_0 -> n3_0 [label=\"g': B→P\"];").unwrap();

    writeln!(dot, "}}").unwrap();
    dot
}

/// Generate DOT representation for a DPO (Double Pushout) rewriting step
/// Shows the five-object configuration: L, K, R, G, D, H
pub fn dpo_to_dot(
    left: &BHyp,
    interface: &BHyp,
    right: &BHyp,
    host: &BHyp,
    dpo_result: &DPOResult,
    config: &DotConfig,
) -> String {
    let mut dot = String::new();

    writeln!(dot, "digraph DPO {{").unwrap();
    writeln!(dot, "  fontname=\"{}\"", config.font_name).unwrap();
    writeln!(dot, "  rankdir=LR;").unwrap();
    writeln!(dot, "  compound=true;").unwrap();
    writeln!(dot, "  node [fontname=\"{}\", fontsize={}];", config.font_name, config.font_size).unwrap();
    writeln!(dot).unwrap();

    // Arrange objects: top row (L, K, R), bottom row (G, D, H)
    let objects = vec![
        ("L (LHS)", left, "lightblue", "cluster_L", 0, 0),
        ("K (Interface)", interface, "lightgreen", "cluster_K", 1, 0),
        ("R (RHS)", right, "lightcyan", "cluster_R", 2, 0),
        ("G (Host)", host, "lightyellow", "cluster_G", 0, 1),
        ("D (Complement)", &dpo_result.complement, "lightcoral", "cluster_D", 1, 1),
        ("H (Result)", &dpo_result.result, "plum", "cluster_H", 2, 1),
    ];

    for (name, bhyp, color, cluster, _, _) in &objects {
        writeln!(dot, "  subgraph {} {{", cluster).unwrap();
        writeln!(dot, "    label=\"{}\";", name).unwrap();
        writeln!(dot, "    style=filled;").unwrap();
        writeln!(dot, "    fillcolor={};", color).unwrap();
        writeln!(dot, "    node [shape=circle, style=filled, fillcolor=white];").unwrap();

        for &node in bhyp.nodes() {
            writeln!(dot, "    n{} [label=\"\"];", node.0).unwrap();
        }

        writeln!(dot, "  }}").unwrap();
        writeln!(dot).unwrap();
    }

    // Morphism arrows
    writeln!(dot, "  // Left interface embedding (l: K → L)").unwrap();
    writeln!(dot, "  n0_0 -> n1_0 [label=\"l\"];").unwrap();

    writeln!(dot, "  // Right interface embedding (r: K → R)").unwrap();
    writeln!(dot, "  n2_0 -> n1_0 [label=\"r\", constraint=false];").unwrap();

    writeln!(dot, "  // Match morphism (match: L → G)").unwrap();
    writeln!(dot, "  n0_0 -> n3_0 [label=\"match\"];").unwrap();

    writeln!(dot, "  // Pushout complement (d: K → D)").unwrap();
    writeln!(dot, "  n1_0 -> n4_0 [label=\"d\"];").unwrap();

    writeln!(dot, "  // Pushout: complement to result (K → D → H)").unwrap();
    writeln!(dot, "  n4_0 -> n5_0 [label=\"d'\"];").unwrap();

    writeln!(dot, "  // Right morphism to result (r': R → H)").unwrap();
    writeln!(dot, "  n2_0 -> n5_0 [label=\"r'\"];").unwrap();

    writeln!(dot, "  // Intermediate (G → D)").unwrap();
    writeln!(dot, "  n3_0 -> n4_0 [label=\"g_D\", style=dashed];").unwrap();

    writeln!(dot, "}}").unwrap();
    dot
}

/// Generate a simplified DPO diagram showing just the cospan structure
pub fn dpo_cospan_to_dot(
    left: &BHyp,
    interface: &BHyp,
    right: &BHyp,
    host: &BHyp,
    result: &BHyp,
) -> String {
    let mut dot = String::new();

    writeln!(dot, "digraph DPOCospan {{").unwrap();
    writeln!(dot, "  rankdir=LR;").unwrap();
    writeln!(dot, "  node [shape=box, style=filled];").unwrap();
    writeln!(dot).unwrap();

    // Five boxes representing the objects
    writeln!(
        dot,
        "  L [label=\"L\\n({} nodes, {} edges)\", fillcolor=lightblue];",
        left.nodes().len(),
        left.edges().len()
    ).unwrap();
    writeln!(
        dot,
        "  K [label=\"K (interface)\\n({} nodes)\", fillcolor=lightgreen];",
        interface.nodes().len()
    ).unwrap();
    writeln!(
        dot,
        "  R [label=\"R\\n({} nodes, {} edges)\", fillcolor=lightcyan];",
        right.nodes().len(),
        right.edges().len()
    ).unwrap();
    writeln!(
        dot,
        "  G [label=\"G (host)\\n({} nodes, {} edges)\", fillcolor=lightyellow];",
        host.nodes().len(),
        host.edges().len()
    ).unwrap();
    writeln!(
        dot,
        "  H [label=\"H (result)\\n({} nodes, {} edges)\", fillcolor=plum];",
        result.nodes().len(),
        result.edges().len()
    ).unwrap();

    writeln!(dot).unwrap();

    // Rule: K → L ← K → R (or L ← K → R)
    writeln!(dot, "  K -> L [label=\"l\"];").unwrap();
    writeln!(dot, "  K -> R [label=\"r\"];").unwrap();

    // Rewriting: L → G and R → H (via intermediate D)
    writeln!(dot, "  L -> G [label=\"match\"];").unwrap();
    writeln!(dot, "  R -> H [label=\"\", style=dashed];").unwrap();
    writeln!(dot, "  G -> H [label=\"result\", style=dotted];").unwrap();

    writeln!(dot, "}}").unwrap();
    dot
}

/// Convenience function to generate morphism DOT
pub fn morphism_to_dot_labeled(morphism: &BHypMorphism) -> String {
    morphism_to_dot(morphism, &DotConfig::default())
}

/// Convenience function to generate pushout DOT
pub fn pushout_to_dot_labeled(
    c: &BHyp,
    a: &BHyp,
    b: &BHyp,
    pushout_result: &PushoutResult,
) -> String {
    pushout_to_dot(c, a, b, pushout_result, &DotConfig::default())
}

/// Convenience function to generate DPO DOT
pub fn dpo_to_dot_labeled(
    left: &BHyp,
    interface: &BHyp,
    right: &BHyp,
    host: &BHyp,
    dpo_result: &DPOResult,
) -> String {
    dpo_to_dot(left, interface, right, host, dpo_result, &DotConfig::default())
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