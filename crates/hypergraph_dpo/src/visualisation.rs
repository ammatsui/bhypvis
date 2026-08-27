//! DOT language visualization for Hypergraphs with Binding
//! 
//! This module provides functions to generate GraphViz DOT format output
//! for visualizing BHyp and BHyp_with_interface structures.

use std::fmt::Write;
use std::collections::HashSet;

use crate::bhyp::{BHyp, BHyp_with_interface, Label, NodeId};
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
    /// Create a config for unlabelled visualization
    pub fn unlabelled() -> Self {
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

/// Convenience function to generate labelled DOT
pub fn bhyp_to_dot_labelled(bhyp: &BHyp) -> String {
    bhyp_to_dot(bhyp, &DotConfig::default())
}

/// Convenience function to generate unlabelled DOT
pub fn bhyp_to_dot_unlabelled(bhyp: &BHyp) -> String {
    bhyp_to_dot(bhyp, &DotConfig::unlabelled())
}

/// Convenience function for BHyp_with_interface labelled
pub fn bhyp_with_interface_to_dot_labelled(bhyp_i: &BHyp_with_interface) -> String {
    bhyp_with_interface_to_dot(bhyp_i, &DotConfig::default())
}

/// Convenience function for BHyp_with_interface unlabelled
pub fn bhyp_with_interface_to_dot_unlabelled(bhyp_i: &BHyp_with_interface) -> String {
    bhyp_with_interface_to_dot(bhyp_i, &DotConfig::unlabelled())
}

// ============================================================================
// Categorical Visualization: Morphisms, Pushouts, and DPO
// ============================================================================

/// Helper: Generate DOT for a BHyp as a subgraph/cluster with prefixed IDs
fn bhyp_to_subgraph(
    bhyp: &BHyp,
    cluster_name: &str,
    label: &str,
    fill_color: &str,
    id_prefix: &str,
    config: &DotConfig,
) -> String {
    let mut dot = String::new();

    writeln!(dot, "  subgraph cluster_{} {{", cluster_name).unwrap();
    writeln!(dot, "    label=\"{}\";", label).unwrap();
    writeln!(dot, "    style=filled;").unwrap();
    writeln!(dot, "    fillcolor=\"{}\";", fill_color).unwrap();
    writeln!(dot, "    fontname=\"{}\";", config.font_name).unwrap();
    writeln!(dot, "    fontsize={};", config.font_size).unwrap();
    writeln!(dot).unwrap();

    // Collect bound nodes
    let bound_nodes: HashSet<NodeId> = bhyp.edges().iter()
        .filter_map(|&e| bhyp.get_sources_with_binding(e))
        .flat_map(|swbs| swbs.iter())
        .flat_map(|swb| swb.bound.iter().copied())
        .collect();

    // Nodes
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
            "    {}_n{} [label=\"{}\", shape=circle, style=filled, fillcolor=white, color=\"{}\", width=0.2, height=0.2, fixedsize=true];",
            id_prefix, node.0, node_label, color
        ).unwrap();
    }

    // Hyperedges
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
            "    {}_e{} [label=\"{}\", shape={}, style=rounded, color=\"{}\"];",
            id_prefix, edge.0, label, shape, color
        ).unwrap();
    }

    // Internal edges (source -> hyperedge -> target)
    for &edge in bhyp.edges() {
        if let Some(swbs) = bhyp.get_sources_with_binding(edge) {
            for (i, swb) in swbs.iter().enumerate() {
                let source_label = if swbs.len() > 1 { format!("{}", i) } else { "".to_string() };
                writeln!(
                    dot,
                    "    {}_n{} -> {}_e{} [label=\"{}\"];",
                    id_prefix, swb.source.0, id_prefix, edge.0, source_label
                ).unwrap();

                for (j, &bound) in swb.bound.iter().enumerate() {
                    writeln!(
                        dot,
                        "    {}_n{} -> {}_e{} [style=dashed, color=\"{}\", constraint=false, label=\"b{},{}\"];",
                        id_prefix, bound.0, id_prefix, edge.0, config.binding_edge_color, i, j
                    ).unwrap();
                }
            }
        }
        if let Some(targets) = bhyp.get_targets(edge) {
            for (i, &target) in targets.iter().enumerate() {
                let target_label = if targets.len() > 1 { format!("{}", i) } else { "".to_string() };
                writeln!(
                    dot,
                    "    {}_e{} -> {}_n{} [label=\"{}\"];",
                    id_prefix, edge.0, id_prefix, target.0, target_label
                ).unwrap();
            }
        }
    }

    // Add an invisible anchor node for cluster-level edges
    writeln!(
        dot,
        "    {}_anchor [shape=point, width=0, height=0, style=invis];",
        id_prefix
    ).unwrap();

    writeln!(dot, "  }}").unwrap();
    dot
}

/// Generate DOT representation for a morphism between two BHyp objects
/// Shows domain and codomain as side-by-side subgraphs with mapping arrows
pub fn morphism_to_dot(morphism: &BHypMorphism, config: &DotConfig) -> String {
    let mut dot = String::new();

    writeln!(dot, "digraph Morphism {{").unwrap();
    writeln!(dot, "  fontname=\"{}\"", config.font_name).unwrap();
    writeln!(dot, "  fontsize={}", config.font_size).unwrap();
    writeln!(dot, "  rankdir=LR;").unwrap();
    writeln!(dot, "  compound=true;").unwrap();
    writeln!(dot, "  newrank=true;").unwrap();
    writeln!(dot).unwrap();

    // Domain subgraph
    dot.push_str(&bhyp_to_subgraph(
        morphism.domain(),
        "domain",
        "Domain (A)",
        "lightblue",
        "dom",
        config,
    ));
    writeln!(dot).unwrap();

    // Codomain subgraph
    dot.push_str(&bhyp_to_subgraph(
        morphism.codomain(),
        "codomain",
        "Codomain (B)",
        "lightcoral",
        "cod",
        config,
    ));
    writeln!(dot).unwrap();

    // Morphism arrows (node mappings)
    writeln!(dot, "  // Morphism: node mappings").unwrap();
    for (&domain_node, &codomain_node) in morphism.on_nodes() {
        writeln!(
            dot,
            "  dom_n{} -> cod_n{} [style=dashed, color=forestgreen, penwidth=1.5, constraint=false];",
            domain_node.0, codomain_node.0
        ).unwrap();
    }

    // Edge mappings (if available)
    writeln!(dot, "  // Morphism: edge mappings").unwrap();
    for (&domain_edge, &codomain_edge) in morphism.on_edges() {
        writeln!(
            dot,
            "  dom_e{} -> cod_e{} [style=dashed, color=purple, penwidth=1.5, constraint=false];",
            domain_edge.0, codomain_edge.0
        ).unwrap();
    }

    // Overall morphism arrow between clusters
    writeln!(dot).unwrap();
    writeln!(dot, "  // Cluster-level morphism arrow").unwrap();
    writeln!(
        dot,
        "  dom_anchor -> cod_anchor [lhead=cluster_codomain, ltail=cluster_domain, style=bold, color=black, label=\"f\", penwidth=2];",
    ).unwrap();

    writeln!(dot, "}}").unwrap();
    dot
}

/// Generate DOT representation for a pushout square
/// Renders: C → A, C → B, A → P, B → P with each object as a visualized BHyp
pub fn pushout_to_dot(
    c: &BHyp,           // The common "corner" (pullback object in the span)
    a: &BHyp,           // First leg
    b: &BHyp,           // Second leg
    pushout_result: &PushoutResult,
    config: &DotConfig,
) -> String {
    let mut dot = String::new();

    writeln!(dot, "digraph PushoutSquare {{").unwrap();
    writeln!(dot, "  fontname=\"{}\"", config.font_name).unwrap();
    writeln!(dot, "  fontsize={}", config.font_size).unwrap();
    writeln!(dot, "  compound=true;").unwrap();
    writeln!(dot, "  newrank=true;").unwrap();
    writeln!(dot, "  splines=ortho;").unwrap();
    writeln!(dot).unwrap();

    // Position clusters in a 2x2 grid using subgraphs with rank
    // Top row: C, A
    // Bottom row: B, P

    writeln!(dot, "  // Top row").unwrap();
    writeln!(dot, "  subgraph top_row {{").unwrap();
    writeln!(dot, "    rank=same;").unwrap();
    dot.push_str(&bhyp_to_subgraph(c, "C", "C (span apex)", "lightgreen", "c", config));
    dot.push_str(&bhyp_to_subgraph(a, "A", "A", "lightblue", "a", config));
    writeln!(dot, "  }}").unwrap();
    writeln!(dot).unwrap();

    writeln!(dot, "  // Bottom row").unwrap();
    writeln!(dot, "  subgraph bottom_row {{").unwrap();
    writeln!(dot, "    rank=same;").unwrap();
    dot.push_str(&bhyp_to_subgraph(b, "B", "B", "lightyellow", "b", config));
    dot.push_str(&bhyp_to_subgraph(
        &pushout_result.pushout,
        "P",
        "P (pushout)",
        "lightcoral",
        "p",
        config,
    ));
    writeln!(dot, "  }}").unwrap();
    writeln!(dot).unwrap();

    // Morphism arrows between clusters (forming the square)
    writeln!(dot, "  // Pushout square morphisms").unwrap();

    // C → A (f)
    writeln!(
        dot,
        "  c_anchor -> a_anchor [ltail=cluster_C, lhead=cluster_A, label=\"f\", style=bold, penwidth=2];",
    ).unwrap();

    // C → B (g)
    writeln!(
        dot,
        "  c_anchor -> b_anchor [ltail=cluster_C, lhead=cluster_B, label=\"g\", style=bold, penwidth=2];",
    ).unwrap();

    // A → P (f')
    writeln!(
        dot,
        "  a_anchor -> p_anchor [ltail=cluster_A, lhead=cluster_P, label=\"f'\", style=bold, penwidth=2];",
    ).unwrap();

    // B → P (g')
    writeln!(
        dot,
        "  b_anchor -> p_anchor [ltail=cluster_B, lhead=cluster_P, label=\"g'\", style=bold, penwidth=2];",
    ).unwrap();

    // Optional: Show node mappings within the morphisms
    writeln!(dot).unwrap();
    writeln!(dot, "  // Detailed node mappings (f': A → P)").unwrap();
    for (&a_node, &p_node) in &pushout_result.first_to_pushout_nodes {
        writeln!(
            dot,
            "  a_n{} -> p_n{} [style=dotted, color=blue, constraint=false];",
            a_node.0, p_node.0
        ).unwrap();
    }

    writeln!(dot, "  // Detailed node mappings (g': B → P)").unwrap();
    for (&b_node, &p_node) in &pushout_result.second_to_pushout_nodes {
        writeln!(
            dot,
            "  b_n{} -> p_n{} [style=dotted, color=orange, constraint=false];",
            b_node.0, p_node.0
        ).unwrap();
    }

    writeln!(dot, "}}").unwrap();
    dot
}

/// Generate DOT representation for a pullback square
/// Renders: P → A, P → B, A → C, B → C with each object as a visualized BHyp
pub fn pullback_to_dot(
    c: &BHyp,           // The common "corner" (pushout object in the cospan)
    a: &BHyp,           // First leg
    b: &BHyp,           // Second leg
    pullback: &BHyp,    // The pullback object
    morphism_p_to_a: &BHypMorphism,
    morphism_p_to_b: &BHypMorphism,
    config: &DotConfig,
) -> String {
    let mut dot = String::new();

    writeln!(dot, "digraph PullbackSquare {{").unwrap();
    writeln!(dot, "  fontname=\"{}\"", config.font_name).unwrap();
    writeln!(dot, "  fontsize={}", config.font_size).unwrap();
    writeln!(dot, "  compound=true;").unwrap();
    writeln!(dot, "  newrank=true;").unwrap();
    writeln!(dot, "  splines=ortho;").unwrap();
    writeln!(dot).unwrap();

    // Position clusters in a 2x2 grid
    // Top row: P (pullback), A
    // Bottom row: B, C

    writeln!(dot, "  // Top row").unwrap();
    writeln!(dot, "  subgraph top_row {{").unwrap();
    writeln!(dot, "    rank=same;").unwrap();
    dot.push_str(&bhyp_to_subgraph(pullback, "P", "P (pullback)", "lightcoral", "p", config));
    dot.push_str(&bhyp_to_subgraph(a, "A", "A", "lightblue", "a", config));
    writeln!(dot, "  }}").unwrap();
    writeln!(dot).unwrap();

    writeln!(dot, "  // Bottom row").unwrap();
    writeln!(dot, "  subgraph bottom_row {{").unwrap();
    writeln!(dot, "    rank=same;").unwrap();
    dot.push_str(&bhyp_to_subgraph(b, "B", "B", "lightyellow", "b", config));
    dot.push_str(&bhyp_to_subgraph(c, "C", "C (cospan apex)", "lightgreen", "c", config));
    writeln!(dot, "  }}").unwrap();
    writeln!(dot).unwrap();

    // Morphism arrows between clusters (forming the square)
    writeln!(dot, "  // Pullback square morphisms").unwrap();

    // P → A (π₁)
    writeln!(
        dot,
        "  p_anchor -> a_anchor [ltail=cluster_P, lhead=cluster_A, label=\"π₁\", style=bold, penwidth=2];",
    ).unwrap();

    // P → B (π₂)
    writeln!(
        dot,
        "  p_anchor -> b_anchor [ltail=cluster_P, lhead=cluster_B, label=\"π₂\", style=bold, penwidth=2];",
    ).unwrap();

    // A → C (f)
    writeln!(
        dot,
        "  a_anchor -> c_anchor [ltail=cluster_A, lhead=cluster_C, label=\"f\", style=bold, penwidth=2];",
    ).unwrap();

    // B → C (g)
    writeln!(
        dot,
        "  b_anchor -> c_anchor [ltail=cluster_B, lhead=cluster_C, label=\"g\", style=bold, penwidth=2];",
    ).unwrap();

    // Detailed node mappings
    writeln!(dot).unwrap();
    writeln!(dot, "  // Detailed node mappings (π₁: P → A)").unwrap();
    for (&p_node, &a_node) in morphism_p_to_a.on_nodes() {
        writeln!(
            dot,
            "  p_n{} -> a_n{} [style=dotted, color=blue, constraint=false];",
            p_node.0, a_node.0
        ).unwrap();
    }

    writeln!(dot, "  // Detailed node mappings (π₂: P → B)").unwrap();
    for (&p_node, &b_node) in morphism_p_to_b.on_nodes() {
        writeln!(
            dot,
            "  p_n{} -> b_n{} [style=dotted, color=orange, constraint=false];",
            p_node.0, b_node.0
        ).unwrap();
    }

    writeln!(dot, "}}").unwrap();
    dot
}

/// Generate DOT representation for a pushout complement
/// Given L ← K → G, find D such that L → D ← K and D → G form a pushout
pub fn pushout_complement_to_dot(
    l: &BHyp,           // Left object
    k: &BHyp,           // Interface
    g: &BHyp,           // Host graph
    d: &BHyp,           // Pushout complement (context)
    _morphism_k_to_l: &BHypMorphism,
    _morphism_k_to_d: &BHypMorphism,
    _morphism_l_to_g: &BHypMorphism,
    _morphism_d_to_g: &BHypMorphism,
    config: &DotConfig,
) -> String {
    let mut dot = String::new();

    writeln!(dot, "digraph PushoutComplement {{").unwrap();
    writeln!(dot, "  fontname=\"{}\"", config.font_name).unwrap();
    writeln!(dot, "  fontsize={}", config.font_size).unwrap();
    writeln!(dot, "  compound=true;").unwrap();
    writeln!(dot, "  newrank=true;").unwrap();
    writeln!(dot, "  splines=ortho;").unwrap();
    writeln!(dot, "  label=\"Pushout Complement Construction\";").unwrap();
    writeln!(dot, "  labelloc=t;").unwrap();
    writeln!(dot).unwrap();

    // Position: K at top-left, L at top-right, D at bottom-left, G at bottom-right
    writeln!(dot, "  // Top row: K → L").unwrap();
    writeln!(dot, "  subgraph top_row {{").unwrap();
    writeln!(dot, "    rank=same;").unwrap();
    dot.push_str(&bhyp_to_subgraph(k, "K", "K (interface)", "lightgreen", "k", config));
    dot.push_str(&bhyp_to_subgraph(l, "L", "L (pattern)", "lightblue", "l", config));
    writeln!(dot, "  }}").unwrap();
    writeln!(dot).unwrap();

    writeln!(dot, "  // Bottom row: D → G").unwrap();
    writeln!(dot, "  subgraph bottom_row {{").unwrap();
    writeln!(dot, "    rank=same;").unwrap();
    dot.push_str(&bhyp_to_subgraph(d, "D", "D (complement)", "lightyellow", "d", config));
    dot.push_str(&bhyp_to_subgraph(g, "G", "G (host)", "lightcoral", "g", config));
    writeln!(dot, "  }}").unwrap();
    writeln!(dot).unwrap();

    // Morphism arrows
    writeln!(dot, "  // Pushout complement square").unwrap();

    // K → L (l)
    writeln!(
        dot,
        "  k_anchor -> l_anchor [ltail=cluster_K, lhead=cluster_L, label=\"l\", style=bold, penwidth=2];",
    ).unwrap();

    // K → D (d)
    writeln!(
        dot,
        "  k_anchor -> d_anchor [ltail=cluster_K, lhead=cluster_D, label=\"d\", style=bold, penwidth=2];",
    ).unwrap();

    // L → G (m: match)
    writeln!(
        dot,
        "  l_anchor -> g_anchor [ltail=cluster_L, lhead=cluster_G, label=\"m\", style=bold, penwidth=2];",
    ).unwrap();

    // D → G (d')
    writeln!(
        dot,
        "  d_anchor -> g_anchor [ltail=cluster_D, lhead=cluster_G, label=\"d'\", style=bold, penwidth=2];",
    ).unwrap();

    // Pushout indicator
    writeln!(dot).unwrap();
    writeln!(dot, "  // Pushout symbol").unwrap();
    writeln!(
        dot,
        "  po_symbol [label=\"PO\", shape=none, fontsize=10, fontcolor=gray];",
    ).unwrap();

    writeln!(dot, "}}").unwrap();
    dot
}

/// Generate DOT representation for a DPO (Double Pushout) rewriting step
/// Shows: L ← K → R (rule) applied to G, producing H via complement D
pub fn dpo_to_dot(
    l: &BHyp,           // Left-hand side of rule
    k: &BHyp,           // Interface (preserved part)
    r: &BHyp,           // Right-hand side of rule
    g: &BHyp,           // Host graph
    dpo_result: &DPOResult,
    config: &DotConfig,
) -> String {
    let mut dot = String::new();

    writeln!(dot, "digraph DPO {{").unwrap();
    writeln!(dot, "  fontname=\"{}\"", config.font_name).unwrap();
    writeln!(dot, "  fontsize={}", config.font_size).unwrap();
    writeln!(dot, "  compound=true;").unwrap();
    writeln!(dot, "  newrank=true;").unwrap();
    writeln!(dot, "  label=\"Double Pushout Rewriting\";").unwrap();
    writeln!(dot, "  labelloc=t;").unwrap();
    writeln!(dot).unwrap();

    // Layout: 3 columns x 2 rows
    // Row 1: L, K, R (the rule)
    // Row 2: G, D, H (the rewriting)

    // Top row: Rule span L ← K → R
    writeln!(dot, "  // Rule: L ← K → R").unwrap();
    writeln!(dot, "  subgraph rule_row {{").unwrap();
    writeln!(dot, "    rank=same;").unwrap();
    dot.push_str(&bhyp_to_subgraph(l, "L", "L (LHS)", "lightblue", "l", config));
    dot.push_str(&bhyp_to_subgraph(k, "K", "K (interface)", "lightgreen", "k", config));
    dot.push_str(&bhyp_to_subgraph(r, "R", "R (RHS)", "lightcyan", "r", config));
    writeln!(dot, "  }}").unwrap();
    writeln!(dot).unwrap();

    // Bottom row: Rewriting G → D → H
    writeln!(dot, "  // Rewriting: G, D, H").unwrap();
    writeln!(dot, "  subgraph rewrite_row {{").unwrap();
    writeln!(dot, "    rank=same;").unwrap();
    dot.push_str(&bhyp_to_subgraph(g, "G", "G (host)", "lightyellow", "g", config));
    dot.push_str(&bhyp_to_subgraph(&dpo_result.complement, "D", "D (context)", "lightcoral", "d", config));
    dot.push_str(&bhyp_to_subgraph(&dpo_result.result, "H", "H (result)", "plum", "h", config));
    writeln!(dot, "  }}").unwrap();
    writeln!(dot).unwrap();

    // Morphism arrows
    writeln!(dot, "  // Rule morphisms").unwrap();

    // K → L (l: left inclusion)
    writeln!(
        dot,
        "  k_anchor -> l_anchor [ltail=cluster_K, lhead=cluster_L, label=\"l\", style=bold, penwidth=2, dir=back];",
    ).unwrap();

    // K → R (r: right inclusion)
    writeln!(
        dot,
        "  k_anchor -> r_anchor [ltail=cluster_K, lhead=cluster_R, label=\"r\", style=bold, penwidth=2];",
    ).unwrap();

    writeln!(dot, "  // Vertical morphisms (pushout squares)").unwrap();

    // L → G (match)
    writeln!(
        dot,
        "  l_anchor -> g_anchor [ltail=cluster_L, lhead=cluster_G, label=\"m\", style=bold, penwidth=2, color=blue];",
    ).unwrap();

    // K → D
    writeln!(
        dot,
        "  k_anchor -> d_anchor [ltail=cluster_K, lhead=cluster_D, label=\"d\", style=bold, penwidth=2, color=green];",
    ).unwrap();

    // R → H
    writeln!(
        dot,
        "  r_anchor -> h_anchor [ltail=cluster_R, lhead=cluster_H, label=\"n\", style=bold, penwidth=2, color=purple];",
    ).unwrap();

    writeln!(dot, "  // Bottom row morphisms").unwrap();

    // G ← D (derived from pushout complement)
    writeln!(
        dot,
        "  d_anchor -> g_anchor [ltail=cluster_D, lhead=cluster_G, label=\"\", style=bold, penwidth=2, dir=back];",
    ).unwrap();

    // D → H (pushout)
    writeln!(
        dot,
        "  d_anchor -> h_anchor [ltail=cluster_D, lhead=cluster_H, label=\"\", style=bold, penwidth=2];",
    ).unwrap();

    // Pushout indicators
    writeln!(dot).unwrap();
    writeln!(dot, "  // Pushout symbols").unwrap();
    writeln!(dot, "  po1 [label=\"PO\", shape=none, fontsize=10, fontcolor=gray];").unwrap();
    writeln!(dot, "  po2 [label=\"PO\", shape=none, fontsize=10, fontcolor=gray];").unwrap();

    writeln!(dot, "}}").unwrap();
    dot
}

/// Generate a simplified DPO diagram showing just boxes with statistics
pub fn dpo_cospan_to_dot(
    l: &BHyp,
    k: &BHyp,
    r: &BHyp,
    g: &BHyp,
    result: &BHyp,
) -> String {
    let mut dot = String::new();

    writeln!(dot, "digraph DPOCospan {{").unwrap();
    writeln!(dot, "  rankdir=TB;").unwrap();
    writeln!(dot, "  node [shape=box, style=filled, fontname=Helvetica];").unwrap();
    writeln!(dot, "  edge [fontname=Helvetica];").unwrap();
    writeln!(dot).unwrap();

    // Top row: Rule
    writeln!(dot, "  subgraph rule {{").unwrap();
    writeln!(dot, "    rank=same;").unwrap();
    writeln!(
        dot,
        "    L [label=\"L (LHS)\\n{} nodes, {} edges\", fillcolor=lightblue];",
        l.nodes().len(), l.edges().len()
    ).unwrap();
    writeln!(
        dot,
        "    K [label=\"K (interface)\\n{} nodes\", fillcolor=lightgreen];",
        k.nodes().len()
    ).unwrap();
    writeln!(
        dot,
        "    R [label=\"R (RHS)\\n{} nodes, {} edges\", fillcolor=lightcyan];",
        r.nodes().len(), r.edges().len()
    ).unwrap();
    writeln!(dot, "  }}").unwrap();
    writeln!(dot).unwrap();

    // Bottom row: Rewriting
    writeln!(dot, "  subgraph rewrite {{").unwrap();
    writeln!(dot, "    rank=same;").unwrap();
    writeln!(
        dot,
        "    G [label=\"G (host)\\n{} nodes, {} edges\", fillcolor=lightyellow];",
        g.nodes().len(), g.edges().len()
    ).unwrap();
    writeln!(dot, "    D [label=\"D (context)\", fillcolor=lightcoral];").unwrap();
    writeln!(
        dot,
        "    H [label=\"H (result)\\n{} nodes, {} edges\", fillcolor=plum];",
        result.nodes().len(), result.edges().len()
    ).unwrap();
    writeln!(dot, "  }}").unwrap();
    writeln!(dot).unwrap();

    // Rule span
    writeln!(dot, "  K -> L [label=\"l\", dir=back];").unwrap();
    writeln!(dot, "  K -> R [label=\"r\"];").unwrap();

    // Vertical morphisms
    writeln!(dot, "  L -> G [label=\"match\", style=dashed];").unwrap();
    writeln!(dot, "  K -> D [style=dashed];").unwrap();
    writeln!(dot, "  R -> H [style=dashed];").unwrap();

    // Bottom span
    writeln!(dot, "  D -> G [dir=back];").unwrap();
    writeln!(dot, "  D -> H;").unwrap();

    writeln!(dot, "}}").unwrap();
    dot
}

// Convenience functions

/// Convenience function to generate morphism DOT with default config
pub fn morphism_to_dot_labelled(morphism: &BHypMorphism) -> String {
    morphism_to_dot(morphism, &DotConfig::default())
}

/// Convenience function to generate pushout DOT with default config
pub fn pushout_to_dot_labelled(
    c: &BHyp,
    a: &BHyp,
    b: &BHyp,
    pushout_result: &PushoutResult,
) -> String {
    pushout_to_dot(c, a, b, pushout_result, &DotConfig::default())
}

/// Convenience function to generate pullback DOT with default config
pub fn pullback_to_dot_labelled(
    c: &BHyp,
    a: &BHyp,
    b: &BHyp,
    pullback: &BHyp,
    morphism_p_to_a: &BHypMorphism,
    morphism_p_to_b: &BHypMorphism,
) -> String {
    pullback_to_dot(c, a, b, pullback, morphism_p_to_a, morphism_p_to_b, &DotConfig::default())
}

/// Convenience function to generate pushout complement DOT with default config
pub fn pushout_complement_to_dot_labelled(
    l: &BHyp,
    k: &BHyp,
    g: &BHyp,
    d: &BHyp,
    morphism_k_to_l: &BHypMorphism,
    morphism_k_to_d: &BHypMorphism,
    morphism_l_to_g: &BHypMorphism,
    morphism_d_to_g: &BHypMorphism,
) -> String {
    pushout_complement_to_dot(
        l, k, g, d,
        morphism_k_to_l, morphism_k_to_d,
        morphism_l_to_g, morphism_d_to_g,
        &DotConfig::default(),
    )
}

/// Convenience function to generate DPO DOT with default config
pub fn dpo_to_dot_labelled(
    l: &BHyp,
    k: &BHyp,
    r: &BHyp,
    g: &BHyp,
    dpo_result: &DPOResult,
) -> String {
    dpo_to_dot(l, k, r, g, dpo_result, &DotConfig::default())
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

        let dot = bhyp_to_dot_labelled(&g);
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

        let dot = bhyp_to_dot_labelled(&g);
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

        let dot = bhyp_to_dot_labelled(&g);
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

        let dot = bhyp_with_interface_to_dot_labelled(&g);
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
    fn test_unlabelled_dot() {
        let mut g = BHyp::new();
        let n1 = g.add_node();
        let n2 = g.add_node();
        g.add_edge(
            vec![SourceWithBinding { source: n1, bound: vec![] }],
            vec![n2],
            Some(Label::Symbol("should_not_appear".to_string())),
        ).unwrap();

        let dot = bhyp_to_dot_unlabelled(&g);
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