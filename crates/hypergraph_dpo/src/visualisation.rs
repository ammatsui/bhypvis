// DOT language visualization for Hypergraphs with Binding
// 
// This module provides functions to generate GraphViz DOT format output
// for visualizing BHyp and BHyp_with_interface structures, as well as
// categorical constructions like morphisms, pushouts, pullbacks, and
// pushout complements.

use std::fmt::Write;
use std::collections::HashSet;

use crate::bhyp::{BHyp, BHyp_with_interface, Label, NodeId};
use crate::categorical::{BHypMorphism, PushoutResult, PullbackResult, PushoutComplementResult};

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
    /// Whether to show detailed mappings in categorical diagrams
    pub show_detailed_mappings: bool,
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
            show_detailed_mappings: true,
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

    /// Create a config without detailed mappings (cleaner categorical diagrams)
    pub fn without_detailed_mappings() -> Self {
        DotConfig {
            show_detailed_mappings: false,
            ..Default::default()
        }
    }
}

/// Format a label for display
pub fn format_label(label: &Label) -> String {
    match label {
        Label::Symbol(s) => s.clone(),
        Label::Meta(name, arity) => format!("{}:{}", name, arity),
    }
}

// ============================================================================
// Basic BHyp Visualization
// ============================================================================

/// Generate DOT representation for a BHyp
pub fn bhyp_to_dot(bhyp: &BHyp, config: &DotConfig) -> String {
    bhyp_to_dot_with_name(bhyp, "G", config)
}

/// Generate DOT representation for a BHyp with a custom graph name
pub fn bhyp_to_dot_with_name(bhyp: &BHyp, name: &str, config: &DotConfig) -> String {
    let mut dot = String::new();

    writeln!(dot, "digraph {} {{", name).unwrap();
    writeln!(dot, "  fontname=\"{}\"", config.font_name).unwrap();
    writeln!(dot, "  fontsize={}", config.font_size).unwrap();
    if config.left_to_right {
        writeln!(dot, "  rankdir=LR;").unwrap();
    }
    writeln!(dot, "  node [fontname=\"{}\", fontsize={}];", config.font_name, config.font_size).unwrap();
    writeln!(dot, "  edge [fontname=\"{}\", fontsize={}];", config.font_name, config.font_size).unwrap();
    writeln!(dot).unwrap();

    let bound_nodes: HashSet<NodeId> = bhyp.edges().iter()
        .filter_map(|&e| bhyp.get_sources_with_binding(e))
        .flat_map(|swbs| swbs.iter())
        .flat_map(|swb| swb.bound.iter().copied())
        .collect();

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

    writeln!(dot, "  // Source connections").unwrap();
    for &edge in bhyp.edges() {
        if let Some(swbs) = bhyp.get_sources_with_binding(edge) {
            for (i, swb) in swbs.iter().enumerate() {
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

    // Input interface subgraph
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

    // Main hypergraph subgraph
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

    for &node in bhyp_i.nodes() {
        let label = if config.show_node_ids {
            format!("{}", node.0)
        } else {
            "".to_string()
        };

        let color = if input_nodes.contains(&node) && output_nodes.contains(&node) {
            "purple"
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

    // Output interface subgraph
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

    // Interface morphisms
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

    writeln!(dot, "  I_G [label=\"I_G\\n({} nodes)\", shape=box, style=filled, fillcolor=lightgreen];",
             bhyp_i.input_interface().nodes().len()).unwrap();
    writeln!(dot, "  G [label=\"G\\n({} nodes, {} edges)\", shape=box, style=filled, fillcolor=lightblue];",
             bhyp_i.nodes().len(), bhyp_i.edges().len()).unwrap();
    writeln!(dot, "  O_G [label=\"O_G\\n({} nodes)\", shape=box, style=filled, fillcolor=lightcoral];",
             bhyp_i.output_interface().nodes().len()).unwrap();

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

// ============================================================================
// Categorical Visualization: Core Building Blocks
// ============================================================================

/// Helper: Generate DOT for a BHyp as a subgraph/cluster with prefixed IDs
/// This is the core reusable component for categorical diagrams
pub fn bhyp_to_subgraph(
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

    // Internal edges
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

    // Invisible anchor node for cluster-level edges
    writeln!(
        dot,
        "    {}_anchor [shape=point, width=0, height=0, style=invis];",
        id_prefix
    ).unwrap();

    writeln!(dot, "  }}").unwrap();
    dot
}

/// Helper: Generate DOT edges for morphism mappings between two subgraphs
/// Reusable component for drawing morphism arrows
fn morphism_mappings_to_dot(
    morphism: &BHypMorphism,
    from_prefix: &str,
    to_prefix: &str,
    node_color: &str,
    edge_color: &str,
    config: &DotConfig,
) -> String {
    let mut dot = String::new();

    if !config.show_detailed_mappings {
        return dot;
    }

    // Node mappings
    for (&from_node, &to_node) in morphism.on_nodes() {
        writeln!(
            dot,
            "  {}_n{} -> {}_n{} [style=dotted, color={}, constraint=false];",
            from_prefix, from_node.0, to_prefix, to_node.0, node_color
        ).unwrap();
    }

    // Edge mappings
    for (&from_edge, &to_edge) in morphism.on_edges() {
        writeln!(
            dot,
            "  {}_e{} -> {}_e{} [style=dotted, color={}, constraint=false];",
            from_prefix, from_edge.0, to_prefix, to_edge.0, edge_color
        ).unwrap();
    }

    dot
}

// ============================================================================
// Morphism Visualization
// ============================================================================

/// Generate DOT representation for a morphism between two BHyp objects
/// Shows domain and codomain as side-by-side subgraphs with mapping arrows
pub fn morphism_to_dot(morphism: &BHypMorphism, config: &DotConfig) -> String {
    morphism_to_dot_with_labels(
        morphism,
        "Domain (A)",
        "Codomain (B)",
        "f",
        config,
    )
}

/// Generate DOT representation for a morphism with custom labels
pub fn morphism_to_dot_with_labels(
    morphism: &BHypMorphism,
    domain_label: &str,
    codomain_label: &str,
    morphism_label: &str,
    config: &DotConfig,
) -> String {
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
        domain_label,
        "lightblue",
        "dom",
        config,
    ));
    writeln!(dot).unwrap();

    // Codomain subgraph
    dot.push_str(&bhyp_to_subgraph(
        morphism.codomain(),
        "codomain",
        codomain_label,
        "lightcoral",
        "cod",
        config,
    ));
    writeln!(dot).unwrap();

    // Morphism mappings
    writeln!(dot, "  // Morphism mappings").unwrap();
    dot.push_str(&morphism_mappings_to_dot(
        morphism,
        "dom",
        "cod",
        "forestgreen",
        "purple",
        config,
    ));

    // Cluster-level morphism arrow
    writeln!(dot).unwrap();
    writeln!(dot, "  // Cluster-level morphism arrow").unwrap();
    writeln!(
        dot,
        "  dom_anchor -> cod_anchor [lhead=cluster_codomain, ltail=cluster_domain, style=bold, color=black, label=\"{}\", penwidth=2];",
        morphism_label
    ).unwrap();

    writeln!(dot, "}}").unwrap();
    dot
}

// ============================================================================
// Pushout Visualization
// ============================================================================

/// Configuration for a single object in a categorical square diagram
struct SquareObjectConfig<'a> {
    bhyp: &'a BHyp,
    cluster_name: &'a str,
    label: &'a str,
    fill_color: &'a str,
    id_prefix: &'a str,
}

/// Generate the header for a categorical square diagram
fn categorical_square_header(title: &str, config: &DotConfig) -> String {
    let mut dot = String::new();

    writeln!(dot, "digraph CategoricalSquare {{").unwrap();
    writeln!(dot, "  fontname=\"{}\"", config.font_name).unwrap();
    writeln!(dot, "  fontsize={}", config.font_size).unwrap();
    writeln!(dot, "  compound=true;").unwrap();
    writeln!(dot, "  newrank=true;").unwrap();
    writeln!(dot, "  splines=ortho;").unwrap();
    if !title.is_empty() {
        writeln!(dot, "  label=\"{}\";", title).unwrap();
        writeln!(dot, "  labelloc=t;").unwrap();
    }
    writeln!(dot).unwrap();

    dot
}

/// Generate DOT representation for a pushout square using the new categorical result types
///
/// ```text
///     A ---f---> B
///     |          |
///     g          g'
///     |          |
///     v          v
///     C ---f'--> D (pushout)
/// ```
pub fn pushout_to_dot(
    f: &BHypMorphism,  // f: A -> B
    g: &BHypMorphism,  // g: A -> C
    result: &PushoutResult,
    config: &DotConfig,
) -> String {
    let mut dot = categorical_square_header("Pushout Square", config);

    let a = f.domain();  // Common domain
    let b = f.codomain();
    let c = g.codomain();
    let d = &result.pushout;

    // Top row: A, B
    writeln!(dot, "  // Top row").unwrap();
    writeln!(dot, "  subgraph top_row {{").unwrap();
    writeln!(dot, "    rank=same;").unwrap();
    dot.push_str(&bhyp_to_subgraph(a, "A", "A (span apex)", "lightgreen", "a", config));
    dot.push_str(&bhyp_to_subgraph(b, "B", "B", "lightblue", "b", config));
    writeln!(dot, "  }}").unwrap();
    writeln!(dot).unwrap();

    // Bottom row: C, D
    writeln!(dot, "  // Bottom row").unwrap();
    writeln!(dot, "  subgraph bottom_row {{").unwrap();
    writeln!(dot, "    rank=same;").unwrap();
    dot.push_str(&bhyp_to_subgraph(c, "C", "C", "lightyellow", "c", config));
    dot.push_str(&bhyp_to_subgraph(d, "D", "D (pushout)", "lightcoral", "d", config));
    writeln!(dot, "  }}").unwrap();
    writeln!(dot).unwrap();

    // Square morphism arrows
    writeln!(dot, "  // Pushout square morphisms").unwrap();

    // A → B (f)
    writeln!(
        dot,
        "  a_anchor -> b_anchor [ltail=cluster_A, lhead=cluster_B, label=\"f\", style=bold, penwidth=2];",
    ).unwrap();

    // A → C (g)
    writeln!(
        dot,
        "  a_anchor -> c_anchor [ltail=cluster_A, lhead=cluster_C, label=\"g\", style=bold, penwidth=2];",
    ).unwrap();

    // B → D (g')
    writeln!(
        dot,
        "  b_anchor -> d_anchor [ltail=cluster_B, lhead=cluster_D, label=\"g'\", style=bold, penwidth=2];",
    ).unwrap();

    // C → D (f')
    writeln!(
        dot,
        "  c_anchor -> d_anchor [ltail=cluster_C, lhead=cluster_D, label=\"f'\", style=bold, penwidth=2];",
    ).unwrap();

    // Detailed mappings using the morphisms from the result
    if config.show_detailed_mappings {
        writeln!(dot).unwrap();
        writeln!(dot, "  // Detailed mappings (f: A -> B)").unwrap();
        dot.push_str(&morphism_mappings_to_dot(f, "a", "b", "blue", "purple", config));

        writeln!(dot, "  // Detailed mappings (g: A -> C)").unwrap();
        dot.push_str(&morphism_mappings_to_dot(g, "a", "c", "green", "purple", config));

        writeln!(dot, "  // Detailed mappings (g': B -> D)").unwrap();
        dot.push_str(&morphism_mappings_to_dot(&result.morphism_from_b, "b", "d", "orange", "purple", config));

        writeln!(dot, "  // Detailed mappings (f': C -> D)").unwrap();
        dot.push_str(&morphism_mappings_to_dot(&result.morphism_from_c, "c", "d", "brown", "purple", config));
    }

    // Pushout symbol
    writeln!(dot).unwrap();
    writeln!(dot, "  po_symbol [label=\"PO\", shape=none, fontsize=10, fontcolor=gray];").unwrap();

    writeln!(dot, "}}").unwrap();
    dot
}

// ============================================================================
// Pullback Visualization
// ============================================================================

/// Generate DOT representation for a pullback square using the new categorical result types
///
/// ```text
///     P ---π₁---> B
///     |           |
///     π₂          f
///     |           |
///     v           v
///     C ---g----> D (cospan apex)
/// ```
pub fn pullback_to_dot(
    f: &BHypMorphism,  // f: B -> D
    g: &BHypMorphism,  // g: C -> D
    result: &PullbackResult,
    config: &DotConfig,
) -> String {
    let mut dot = categorical_square_header("Pullback Square", config);

    let b = f.domain();
    let c = g.domain();
    let d = f.codomain();  // Common codomain
    let p = &result.pullback;

    // Top row: P, B
    writeln!(dot, "  // Top row").unwrap();
    writeln!(dot, "  subgraph top_row {{").unwrap();
    writeln!(dot, "    rank=same;").unwrap();
    dot.push_str(&bhyp_to_subgraph(p, "P", "P (pullback)", "lightcoral", "p", config));
    dot.push_str(&bhyp_to_subgraph(b, "B", "B", "lightblue", "b", config));
    writeln!(dot, "  }}").unwrap();
    writeln!(dot).unwrap();

    // Bottom row: C, D
    writeln!(dot, "  // Bottom row").unwrap();
    writeln!(dot, "  subgraph bottom_row {{").unwrap();
    writeln!(dot, "    rank=same;").unwrap();
    dot.push_str(&bhyp_to_subgraph(c, "C", "C", "lightyellow", "c", config));
    dot.push_str(&bhyp_to_subgraph(d, "D", "D (cospan apex)", "lightgreen", "d", config));
    writeln!(dot, "  }}").unwrap();
    writeln!(dot).unwrap();

    // Square morphism arrows
    writeln!(dot, "  // Pullback square morphisms").unwrap();

    // P → B (π₁)
    writeln!(
        dot,
        "  p_anchor -> b_anchor [ltail=cluster_P, lhead=cluster_B, label=\"π₁\", style=bold, penwidth=2];",
    ).unwrap();

    // P → C (π₂)
    writeln!(
        dot,
        "  p_anchor -> c_anchor [ltail=cluster_P, lhead=cluster_C, label=\"π₂\", style=bold, penwidth=2];",
    ).unwrap();

    // B → D (f)
    writeln!(
        dot,
        "  b_anchor -> d_anchor [ltail=cluster_B, lhead=cluster_D, label=\"f\", style=bold, penwidth=2];",
    ).unwrap();

    // C → D (g)
    writeln!(
        dot,
        "  c_anchor -> d_anchor [ltail=cluster_C, lhead=cluster_D, label=\"g\", style=bold, penwidth=2];",
    ).unwrap();

    // Detailed mappings
    if config.show_detailed_mappings {
        writeln!(dot).unwrap();
        writeln!(dot, "  // Detailed mappings (π₁: P -> B)").unwrap();
        dot.push_str(&morphism_mappings_to_dot(&result.morphism_to_b, "p", "b", "blue", "purple", config));

        writeln!(dot, "  // Detailed mappings (π₂: P -> C)").unwrap();
        dot.push_str(&morphism_mappings_to_dot(&result.morphism_to_c, "p", "c", "orange", "purple", config));

        writeln!(dot, "  // Detailed mappings (f: B -> D)").unwrap();
        dot.push_str(&morphism_mappings_to_dot(f, "b", "d", "green", "purple", config));

        writeln!(dot, "  // Detailed mappings (g: C -> D)").unwrap();
        dot.push_str(&morphism_mappings_to_dot(g, "c", "d", "brown", "purple", config));
    }

    // Pullback symbol
    writeln!(dot).unwrap();
    writeln!(dot, "  pb_symbol [label=\"PB\", shape=none, fontsize=10, fontcolor=gray];").unwrap();

    writeln!(dot, "}}").unwrap();
    dot
}

// ============================================================================
// Pushout Complement Visualization
// ============================================================================

/// Generate DOT representation for a pushout complement square
///
/// Given l: K -> L and m: L -> G, the pushout complement is:
/// ```text
///     K ---l---> L
///     |          |
///     k          m
///     |          |
///     v          v
///     C -------> G
/// ```
/// where the square is a pushout
pub fn pushout_complement_to_dot(
    l: &BHypMorphism,  // l: K -> L
    m: &BHypMorphism,  // m: L -> G
    result: &PushoutComplementResult,
    config: &DotConfig,
) -> String {
    let mut dot = categorical_square_header("Pushout Complement Construction", config);

    let k = l.domain();
    let l_bhyp = l.codomain();
    let g = m.codomain();
    let c = &result.complement;

    // Top row: K, L
    writeln!(dot, "  // Top row: K -> L").unwrap();
    writeln!(dot, "  subgraph top_row {{").unwrap();
    writeln!(dot, "    rank=same;").unwrap();
    dot.push_str(&bhyp_to_subgraph(k, "K", "K (interface)", "lightgreen", "k", config));
    dot.push_str(&bhyp_to_subgraph(l_bhyp, "L", "L (pattern)", "lightblue", "l", config));
    writeln!(dot, "  }}").unwrap();
    writeln!(dot).unwrap();

    // Bottom row: C, G
    writeln!(dot, "  // Bottom row: C -> G").unwrap();
    writeln!(dot, "  subgraph bottom_row {{").unwrap();
    writeln!(dot, "    rank=same;").unwrap();
    dot.push_str(&bhyp_to_subgraph(c, "C", "C (complement)", "lightyellow", "c", config));
    dot.push_str(&bhyp_to_subgraph(g, "G", "G (host)", "lightcoral", "g", config));
    writeln!(dot, "  }}").unwrap();
    writeln!(dot).unwrap();

    // Square morphism arrows
    writeln!(dot, "  // Pushout complement square").unwrap();

    // K → L (l)
    writeln!(
        dot,
        "  k_anchor -> l_anchor [ltail=cluster_K, lhead=cluster_L, label=\"l\", style=bold, penwidth=2];",
    ).unwrap();

    // K → C (k)
    writeln!(
        dot,
        "  k_anchor -> c_anchor [ltail=cluster_K, lhead=cluster_C, label=\"k\", style=bold, penwidth=2];",
    ).unwrap();

    // L → G (m: match)
    writeln!(
        dot,
        "  l_anchor -> g_anchor [ltail=cluster_L, lhead=cluster_G, label=\"m\", style=bold, penwidth=2];",
    ).unwrap();

    // C → G (c)
    writeln!(
        dot,
        "  c_anchor -> g_anchor [ltail=cluster_C, lhead=cluster_G, label=\"c\", style=bold, penwidth=2];",
    ).unwrap();

    // Detailed mappings using the morphisms from the result
    if config.show_detailed_mappings {
        writeln!(dot).unwrap();
        writeln!(dot, "  // Detailed mappings (l: K -> L)").unwrap();
        dot.push_str(&morphism_mappings_to_dot(l, "k", "l", "blue", "purple", config));

        writeln!(dot, "  // Detailed mappings (k: K -> C)").unwrap();
        dot.push_str(&morphism_mappings_to_dot(&result.morphism_from_a, "k", "c", "green", "purple", config));

        writeln!(dot, "  // Detailed mappings (m: L -> G)").unwrap();
        dot.push_str(&morphism_mappings_to_dot(m, "l", "g", "orange", "purple", config));

        writeln!(dot, "  // Detailed mappings (c: C -> G)").unwrap();
        dot.push_str(&morphism_mappings_to_dot(&result.morphism_to_b, "c", "g", "brown", "purple", config));
    }

    // Pushout symbol
    writeln!(dot).unwrap();
    writeln!(dot, "  po_symbol [label=\"PO\", shape=none, fontsize=10, fontcolor=gray];").unwrap();

    writeln!(dot, "}}").unwrap();
    dot
}

// ============================================================================
// Convenience Functions
// ============================================================================

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

/// Convenience function to generate morphism DOT with default config
pub fn morphism_to_dot_labelled(morphism: &BHypMorphism) -> String {
    morphism_to_dot(morphism, &DotConfig::default())
}

/// Convenience function to generate pushout DOT with default config
pub fn pushout_to_dot_labelled(
    f: &BHypMorphism,
    g: &BHypMorphism,
    result: &PushoutResult,
) -> String {
    pushout_to_dot(f, g, result, &DotConfig::default())
}

/// Convenience function to generate pullback DOT with default config
pub fn pullback_to_dot_labelled(
    f: &BHypMorphism,
    g: &BHypMorphism,
    result: &PullbackResult,
) -> String {
    pullback_to_dot(f, g, result, &DotConfig::default())
}

/// Convenience function to generate pushout complement DOT with default config
pub fn pushout_complement_to_dot_labelled(
    l: &BHypMorphism,
    m: &BHypMorphism,
    result: &PushoutComplementResult,
) -> String {
    pushout_complement_to_dot(l, m, result, &DotConfig::default())
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bhyp::SourceWithBinding;
    use crate::categorical::{identity_morphism, compute_pushout, compute_pullback, compute_pushout_complement};
    use std::collections::HashMap;

    fn create_simple_graph() -> BHyp {
        let mut g = BHyp::new();
        let n1 = g.add_node();
        let n2 = g.add_node();
        g.add_edge(
            vec![SourceWithBinding { source: n1, bound: vec![] }],
            vec![n2],
            Some(Label::Symbol("f".to_string())),
        ).unwrap();
        g
    }

    #[test]
    fn test_simple_bhyp_dot() {
        let g = create_simple_graph();
        let dot = bhyp_to_dot_labelled(&g);
        assert!(dot.contains("digraph"));
        assert!(dot.contains("n0"));
        assert!(dot.contains("n1"));
        assert!(dot.contains("e0"));
        assert!(dot.contains("\"f\""));
    }

    #[test]
    fn test_morphism_dot() {
        let g = create_simple_graph();
        let id = identity_morphism(&g);
        let dot = morphism_to_dot_labelled(&id);
        
        assert!(dot.contains("digraph Morphism"));
        assert!(dot.contains("cluster_domain"));
        assert!(dot.contains("cluster_codomain"));
        assert!(dot.contains("dom_n"));
        assert!(dot.contains("cod_n"));
    }

    #[test]
    fn test_pushout_dot() {
        // Create a span A <- K -> B
        let mut k = BHyp::new();
        let k_node = k.add_node();

        let mut a = BHyp::new();
        let a_node = a.add_node();
        let _a_node2 = a.add_node();

        let mut b = BHyp::new();
        let b_node = b.add_node();
        let _b_node2 = b.add_node();

        let f = BHypMorphism::new(
            k.clone(),
            a,
            [(k_node, a_node)].into_iter().collect(),
            HashMap::new(),
        ).unwrap();

        let g = BHypMorphism::new(
            k,
            b,
            [(k_node, b_node)].into_iter().collect(),
            HashMap::new(),
        ).unwrap();

        let result = compute_pushout(&f, &g).unwrap();
        let dot = pushout_to_dot_labelled(&f, &g, &result);

        assert!(dot.contains("digraph CategoricalSquare"));
        assert!(dot.contains("cluster_A"));
        assert!(dot.contains("cluster_B"));
        assert!(dot.contains("cluster_C"));
        assert!(dot.contains("cluster_D"));
        assert!(dot.contains("PO"));
    }

    #[test]
    fn test_pullback_dot() {
        // Create a cospan B -> D <- C
        let mut d = BHyp::new();
        let d_node = d.add_node();

        let mut b = BHyp::new();
        let b_node = b.add_node();

        let mut c = BHyp::new();
        let c_node = c.add_node();

        let f = BHypMorphism::new(
            b,
            d.clone(),
            [(b_node, d_node)].into_iter().collect(),
            HashMap::new(),
        ).unwrap();

        let g = BHypMorphism::new(
            c,
            d,
            [(c_node, d_node)].into_iter().collect(),
            HashMap::new(),
        ).unwrap();

        let result = compute_pullback(&f, &g).unwrap();
        let dot = pullback_to_dot_labelled(&f, &g, &result);

        assert!(dot.contains("digraph CategoricalSquare"));
        assert!(dot.contains("cluster_P"));
        assert!(dot.contains("cluster_B"));
        assert!(dot.contains("cluster_C"));
        assert!(dot.contains("cluster_D"));
        assert!(dot.contains("PB"));
    }

    #[test]
    fn test_pushout_complement_dot() {
        // K -> L -> G
        let mut k = BHyp::new();
        let k_node = k.add_node();

        let mut l = BHyp::new();
        let l_node = l.add_node();

        let mut g = BHyp::new();
        let g_node1 = g.add_node();
        let _g_node2 = g.add_node();

        let l_morph = BHypMorphism::new(
            k,
            l.clone(),
            [(k_node, l_node)].into_iter().collect(),
            HashMap::new(),
        ).unwrap();

        let m_morph = BHypMorphism::new(
            l,
            g,
            [(l_node, g_node1)].into_iter().collect(),
            HashMap::new(),
        ).unwrap();

        let result = compute_pushout_complement(&l_morph, &m_morph).unwrap();
        let dot = pushout_complement_to_dot_labelled(&l_morph, &m_morph, &result);

        assert!(dot.contains("digraph CategoricalSquare"));
        assert!(dot.contains("cluster_K"));
        assert!(dot.contains("cluster_L"));
        assert!(dot.contains("cluster_C"));
        assert!(dot.contains("cluster_G"));
        assert!(dot.contains("PO"));
    }

    #[test]
    fn test_config_without_detailed_mappings() {
        let g = create_simple_graph();
        let id = identity_morphism(&g);
        
        let config = DotConfig::without_detailed_mappings();
        let dot = morphism_to_dot(&id, &config);
        
        // Should not contain dotted mapping arrows
        assert!(!dot.contains("style=dotted"));
    }

    #[test]
    fn test_bhyp_to_subgraph_reusability() {
        let g = create_simple_graph();
        
        // Test that bhyp_to_subgraph produces valid DOT content
        let subgraph = bhyp_to_subgraph(&g, "test", "Test Graph", "lightblue", "t", &DotConfig::default());
        
        assert!(subgraph.contains("subgraph cluster_test"));
        assert!(subgraph.contains("t_n0"));
        assert!(subgraph.contains("t_n1"));
        assert!(subgraph.contains("t_e0"));
        assert!(subgraph.contains("t_anchor"));
    }
}