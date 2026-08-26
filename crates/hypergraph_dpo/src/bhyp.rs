// Hypergraph with Binding (BHyp) implementation in Rust
// definiton, body, safety check,
// copying, glueing

use std::collections::{HashMap, HashSet};
use std::fmt;

/// A node identifier in the hypergraph
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct NodeId(pub usize);

/// An edge identifier in the hypergraph
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct EdgeId(pub usize);

/// A label for edges (can be function symbols or metavariables)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Label {
    /// Function symbol from the signature
    Symbol(String),
    /// Metavariable for substitution
    Meta(String, usize), // name and arity
}

/// Binding signature: maps function symbols to their binding arities
#[derive(Debug, Clone)]
pub struct Signature {
    /// Maps symbol names to their binding arities (list of number of bound vars per argument)
    pub symbols: HashMap<String, Vec<usize>>,
}

impl Signature {
    pub fn new() -> Self {
        Signature {
            symbols: HashMap::new(),
        }
    }

    /// Add a function symbol with its binding arity
    /// e.g., λ has arity [1] (binds 1 variable in its argument)
    pub fn add_symbol(&mut self, name: String, binding_arity: Vec<usize>) {
        self.symbols.insert(name, binding_arity);
    }

    /// Check if a symbol exists in the signature
    pub fn has_symbol(&self, name: &str) -> bool {
        self.symbols.contains_key(name)
    }

    /// Get the binding arity for a symbol
    pub fn get_arity(&self, name: &str) -> Option<&Vec<usize>> {
        self.symbols.get(name)
    }
}

impl Default for Signature {
    fn default() -> Self {
        Self::new()
    }
}

/// Represents a source with its associated bound variables
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceWithBinding {
    /// The source node
    pub source: NodeId,
    /// Nodes bound at this source
    pub bound: Vec<NodeId>,
}

/// A hypergraph with binding (Definition 3.1 from the paper)
#[derive(Debug, Clone)]
pub struct BHyp {
    /// Set of nodes (vertices)
    nodes: HashSet<NodeId>,
    /// Set of edges (hyperedges)
    edges: HashSet<EdgeId>,
    /// Target function: maps edges to lists of target nodes
    targets: HashMap<EdgeId, Vec<NodeId>>,
    /// Source and binding function combined: maps edges to (source, bound) pairs
    sources_with_binding: HashMap<EdgeId, Vec<SourceWithBinding>>,
    /// Edge labels (optional)
    labels: HashMap<EdgeId, Label>,
    /// Optional signature
    signature: Option<Signature>,
    /// Counters for generating new IDs
    next_node_id: usize,
    next_edge_id: usize,
}

impl BHyp {
    /// Create a new empty hypergraph with binding
    pub fn new() -> Self {
        BHyp {
            nodes: HashSet::new(),
            edges: HashSet::new(),
            targets: HashMap::new(),
            sources_with_binding: HashMap::new(),
            labels: HashMap::new(),
            signature: None,
            next_node_id: 0,
            next_edge_id: 0,
        }
    }

    /// Create a new hypergraph with a signature
    pub fn with_signature(sig: Signature) -> Self {
        BHyp {
            nodes: HashSet::new(),
            edges: HashSet::new(),
            targets: HashMap::new(),
            sources_with_binding: HashMap::new(),
            labels: HashMap::new(),
            signature: Some(sig),
            next_node_id: 0,
            next_edge_id: 0,
        }
    }

    /// Add a new node and return its ID
    pub fn add_node(&mut self) -> NodeId {
        let id = NodeId(self.next_node_id);
        self.next_node_id += 1;
        self.nodes.insert(id);
        id
    }

    /// Add multiple nodes at once
    pub fn add_nodes(&mut self, count: usize) -> Vec<NodeId> {
        (0..count).map(|_| self.add_node()).collect()
    }

    /// Add an edge with sources (with binding) and targets
    pub fn add_edge(
        &mut self,
        sources: Vec<SourceWithBinding>,
        targets: Vec<NodeId>,
        label: Option<Label>,
    ) -> Result<EdgeId, String> {
        // Validate that all referenced nodes exist
        for swb in &sources {
            if !self.nodes.contains(&swb.source) {
                return Err(format!("Source node {:?} does not exist", swb.source));
            }
            for bound in &swb.bound {
                if !self.nodes.contains(bound) {
                    return Err(format!("Bound node {:?} does not exist", bound));
                }
            }
        }
        for target in &targets {
            if !self.nodes.contains(target) {
                return Err(format!("Target node {:?} does not exist", target));
            }
        }

        // Validate label against signature if present
        if let Some(sig) = &self.signature {
            if let Some(Label::Symbol(name)) = &label {
                if !sig.has_symbol(name) {
                    return Err(format!("Symbol '{}' not in signature", name));
                }
                // Check arity matches
                if let Some(arity) = sig.get_arity(name) {
                    if arity.len() != sources.len() {
                        return Err(format!(
                            "Symbol '{}' expects {} sources, got {}",
                            name,
                            arity.len(),
                            sources.len()
                        ));
                    }
                    for (i, (expected, actual)) in arity.iter().zip(sources.iter()).enumerate() {
                        if *expected != actual.bound.len() {
                            return Err(format!(
                                "Source {} of '{}' expects {} bound variables, got {}",
                                i,
                                name,
                                expected,
                                actual.bound.len()
                            ));
                        }
                    }
                }
            }
        }

        let id = EdgeId(self.next_edge_id);
        self.next_edge_id += 1;
        self.edges.insert(id);
        self.sources_with_binding.insert(id, sources);
        self.targets.insert(id, targets);
        if let Some(l) = label {
            self.labels.insert(id, l);
        }
        Ok(id)
    }

    /// Get the sources of an edge (without binding information)
    pub fn get_sources(&self, edge: EdgeId) -> Option<Vec<NodeId>> {
        self.sources_with_binding
            .get(&edge)
            .map(|swbs| swbs.iter().map(|swb| swb.source).collect())
    }

    /// Get the sources with binding information for an edge
    pub fn get_sources_with_binding(&self, edge: EdgeId) -> Option<&Vec<SourceWithBinding>> {
        self.sources_with_binding.get(&edge)
    }

    /// Get the targets of an edge
    pub fn get_targets(&self, edge: EdgeId) -> Option<&Vec<NodeId>> {
        self.targets.get(&edge)
    }

    /// Get bound variables for a specific source of an edge
    pub fn get_bound_at_source(&self, edge: EdgeId, source_idx: usize) -> Option<&Vec<NodeId>> {
        self.sources_with_binding
            .get(&edge)
            .and_then(|swbs| swbs.get(source_idx))
            .map(|swb| &swb.bound)
    }

    /// Get the label of an edge
    pub fn get_label(&self, edge: EdgeId) -> Option<&Label> {
        self.labels.get(&edge)
    }

    /// Get the arity of an edge (number of sources)
    pub fn get_arity(&self, edge: EdgeId) -> Option<usize> {
        self.sources_with_binding.get(&edge).map(|s| s.len())
    }

    /// Get the coarity of an edge (number of targets)
    pub fn get_coarity(&self, edge: EdgeId) -> Option<usize> {
        self.targets.get(&edge).map(|t| t.len())
    }

    /// Check if an edge is a metaedge (labeled with a metavariable)
    pub fn is_metaedge(&self, edge: EdgeId) -> bool {
        matches!(self.get_label(edge), Some(Label::Meta(_, _)))
    }

    /// Get all nodes in the hypergraph
    pub fn nodes(&self) -> &HashSet<NodeId> {
        &self.nodes
    }

    /// Get all edges in the hypergraph
    pub fn edges(&self) -> &HashSet<EdgeId> {
        &self.edges
    }

    /// Get the signature if present
    pub fn signature(&self) -> Option<&Signature> {
        self.signature.as_ref()
    }

    /// Compute in-degree of a node (how many edges have it as target)
    pub fn in_degree(&self, node: NodeId) -> usize {
        self.targets
            .values()
            .filter(|targets| targets.contains(&node))
            .count()
    }

    /// Compute out-degree of a node (how many edges have it as source)
    pub fn out_degree(&self, node: NodeId) -> usize {
        self.sources_with_binding
            .values()
            .filter(|swbs| swbs.iter().any(|swb| swb.source == node))
            .count()
    }

    /// Compute in-binding degree (inb): how many times a node appears as bound
    pub fn in_binding_degree(&self, node: NodeId) -> usize {
        self.sources_with_binding
            .values()
            .flat_map(|swbs| swbs.iter())
            .filter(|swb| swb.bound.contains(&node))
            .count()
    }

    /// Compute out-binding degree (outb): how many edges have this node as source with binding
    pub fn out_binding_degree(&self, node: NodeId) -> usize {
        self.sources_with_binding
            .values()
            .filter(|swbs| swbs.iter().any(|swb| swb.source == node && !swb.bound.is_empty()))
            .count()
    }

    pub fn is_discrete(&self) -> bool {
        self.edges.is_empty()
    }

    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty() && self.edges.is_empty()
    }

    pub fn is_first_order(&self) -> bool {
        self.sources_with_binding
            .values()
            .flat_map(|swbs| swbs.iter())
            .all(|swb| swb.bound.is_empty())
    }

    /// Compute the body (trace) of bound variables for an edge at a specific source index
    /// This implements Construction 3.6 from the paper
    pub fn compute_body(&self, edge: EdgeId, source_idx: usize) -> Option<HashSet<NodeId>> {
        let swbs = self.sources_with_binding.get(&edge)?;
        let swb = swbs.get(source_idx)?;

        if swb.bound.is_empty() {
            return None;
        }

        let mut body = HashSet::new();
        let source_node = swb.source;

        // Add all bound vertices
        for &bound_node in &swb.bound {
            body.insert(bound_node);
        }

        // Trace through edges: add edges whose sources intersect the body
        // and are not the binding source itself
        let mut changed = true;
        while changed {
            changed = false;
            for &e in &self.edges {
                if let Some(e_sources) = self.get_sources(e) {
                    // Check if any source of e is in the body, but not the source_node itself
                    let has_source_in_body = e_sources
                        .iter()
                        .any(|s| body.contains(s) && *s != source_node);

                    if has_source_in_body {
                        // Add targets of this edge to the body
                        if let Some(e_targets) = self.get_targets(e) {
                            for &t in e_targets {
                                if body.insert(t) {
                                    changed = true;
                                }
                            }
                        }
                    }
                }
            }
        }

        Some(body)
    }

    /// Get edges in the body at a specific source
    pub fn compute_body_edges(&self, edge: EdgeId, source_idx: usize) -> Option<HashSet<EdgeId>> {
        let body_nodes = self.compute_body(edge, source_idx)?;
        let source_node = self.get_sources(edge)?[source_idx];

        let mut body_edges = HashSet::new();

        for &e in &self.edges {
            if let Some(e_sources) = self.get_sources(e) {
                let has_source_in_body = e_sources
                    .iter()
                    .any(|s| body_nodes.contains(s) && *s != source_node);

                if has_source_in_body {
                    body_edges.insert(e);
                }
            }
        }

        Some(body_edges)
    }
}

impl Default for BHyp {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Display for BHyp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Hypergraph with Binding:")?;
        writeln!(f, "  Nodes: {} nodes", self.nodes.len())?;
        writeln!(f, "  Edges: {} edges", self.edges.len())?;

        for edge in &self.edges {
            write!(f, "  Edge {:?}", edge)?;
            if let Some(label) = self.get_label(*edge) {
                write!(f, " [{}]", format_label(label))?;
            }
            writeln!(f, ":")?;

            if let Some(swbs) = self.get_sources_with_binding(*edge) {
                write!(f, "    Sources: ")?;
                for (i, swb) in swbs.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{:?}", swb.source)?;
                    if !swb.bound.is_empty() {
                        write!(f, " (binding: {:?})", swb.bound)?;
                    }
                }
                writeln!(f)?;
            }

            if let Some(targets) = self.get_targets(*edge) {
                writeln!(f, "    Targets: {:?}", targets)?;
            }
        }

        Ok(())
    }
}

/// A hypergraph with binding with interface (cospan I_G → G ← O_G)
/// The interface is automatically computed based on in/out degrees and binding
#[derive(Debug, Clone)]
pub struct BHyp_with_interface {
    /// The underlying hypergraph with binding
    bhyp: BHyp,
    /// Input interface: discrete BHyp with nodes where in(v) = 0 and in_b(v) = 0
    input_interface: BHyp,
    /// Output interface: discrete BHyp with nodes where out(v) = 0
    output_interface: BHyp,
    /// Maps input interface node IDs to the corresponding node IDs in bhyp
    input_map: HashMap<NodeId, NodeId>,
    /// Maps output interface node IDs to the corresponding node IDs in bhyp
    output_map: HashMap<NodeId, NodeId>,
}

impl BHyp_with_interface {
    /// Create a new empty hypergraph with binding with interface
    pub fn new() -> Self {
        let mut result = BHyp_with_interface {
            bhyp: BHyp::new(),
            input_interface: BHyp::new(),
            output_interface: BHyp::new(),
            input_map: HashMap::new(),
            output_map: HashMap::new(),
        };
        result.recompute_interface();
        result
    }

    /// Create a new hypergraph with a signature
    pub fn with_signature(sig: Signature) -> Self {
        let mut result = BHyp_with_interface {
            bhyp: BHyp::with_signature(sig),
            input_interface: BHyp::new(),
            output_interface: BHyp::new(),
            input_map: HashMap::new(),
            output_map: HashMap::new(),
        };
        result.recompute_interface();
        result
    }

    /// Create from an existing BHyp, computing the interface
    pub fn from_bhyp(bhyp: BHyp) -> Self {
        let mut result = BHyp_with_interface {
            bhyp,
            input_interface: BHyp::new(),
            output_interface: BHyp::new(),
            input_map: HashMap::new(),
            output_map: HashMap::new(),
        };
        result.recompute_interface();
        result
    }

    /// Recompute the interface based on current graph structure
    /// Input: vertices v where in(v) = 0 AND in_b(v) = 0
    /// Output: vertices v where out(v) = 0
    pub fn recompute_interface(&mut self) {
        // Clear existing interfaces
        self.input_interface = BHyp::new();
        self.output_interface = BHyp::new();
        self.input_map.clear();
        self.output_map.clear();

        for &node in self.bhyp.nodes() {
            let in_deg = self.bhyp.in_degree(node);
            let in_b_deg = self.bhyp.in_binding_degree(node);
            let out_deg = self.bhyp.out_degree(node);

            // Input interface: no incoming edges and not bound anywhere
            if in_deg == 0 && in_b_deg == 0 {
                let interface_node = self.input_interface.add_node();
                self.input_map.insert(interface_node, node);
            }

            // Output interface: no outgoing edges
            if out_deg == 0 {
                let interface_node = self.output_interface.add_node();
                self.output_map.insert(interface_node, node);
            }
        }
    }

    /// Add a new node and return its ID, recomputing interface
    pub fn add_node(&mut self) -> NodeId {
        let id = self.bhyp.add_node();
        self.recompute_interface();
        id
    }

    /// Add multiple nodes at once, recomputing interface once at the end
    pub fn add_nodes(&mut self, count: usize) -> Vec<NodeId> {
        let ids = self.bhyp.add_nodes(count);
        self.recompute_interface();
        ids
    }

    /// Add an edge with sources (with binding) and targets, recomputing interface
    pub fn add_edge(
        &mut self,
        sources: Vec<SourceWithBinding>,
        targets: Vec<NodeId>,
        label: Option<Label>,
    ) -> Result<EdgeId, String> {
        let result = self.bhyp.add_edge(sources, targets, label)?;
        self.recompute_interface();
        Ok(result)
    }

    /// Remove a node if it exists and is not referenced by any edge
    /// Returns Ok(()) if the node was removed
    pub fn remove_node(&mut self, node: NodeId) -> Result<(), String> {
        // Check if node exists
        if !self.bhyp.nodes.contains(&node) {
            return Err(format!("Node {:?} does not exist", node));
        }

        // Check if node is referenced by any edge
        if self.bhyp.in_degree(node) > 0 {
            return Err(format!("Node {:?} is a target of some edge", node));
        }
        if self.bhyp.out_degree(node) > 0 {
            return Err(format!("Node {:?} is a source of some edge", node));
        }
        if self.bhyp.in_binding_degree(node) > 0 {
            return Err(format!("Node {:?} is bound by some edge", node));
        }

        self.bhyp.nodes.remove(&node);
        self.recompute_interface();
        Ok(())
    }

    /// Remove an edge if it exists
    pub fn remove_edge(&mut self, edge: EdgeId) -> Result<(), String> {
        if !self.bhyp.edges.contains(&edge) {
            return Err(format!("Edge {:?} does not exist", edge));
        }

        self.bhyp.edges.remove(&edge);
        self.bhyp.sources_with_binding.remove(&edge);
        self.bhyp.targets.remove(&edge);
        self.bhyp.labels.remove(&edge);
        self.recompute_interface();
        Ok(())
    }

    /// Get the input interface as a discrete BHyp
    pub fn input_interface(&self) -> &BHyp {
        &self.input_interface
    }

    /// Get the output interface as a discrete BHyp
    pub fn output_interface(&self) -> &BHyp {
        &self.output_interface
    }

    /// Get the input interface nodes as a set of NodeIds (from the main bhyp)
    pub fn input_interface_nodes(&self) -> HashSet<NodeId> {
        self.input_map.values().copied().collect()
    }

    /// Get the output interface nodes as a set of NodeIds (from the main bhyp)
    pub fn output_interface_nodes(&self) -> HashSet<NodeId> {
        self.output_map.values().copied().collect()
    }

    /// Get the mapping from input interface nodes to bhyp nodes
    pub fn input_map(&self) -> &HashMap<NodeId, NodeId> {
        &self.input_map
    }

    /// Get the mapping from output interface nodes to bhyp nodes
    pub fn output_map(&self) -> &HashMap<NodeId, NodeId> {
        &self.output_map
    }

    /// Map an input interface node to its corresponding node in the main bhyp
    pub fn map_input_node(&self, interface_node: NodeId) -> Option<NodeId> {
        self.input_map.get(&interface_node).copied()
    }

    /// Map an output interface node to its corresponding node in the main bhyp
    pub fn map_output_node(&self, interface_node: NodeId) -> Option<NodeId> {
        self.output_map.get(&interface_node).copied()
    }

    /// Get a reference to the underlying BHyp
    pub fn bhyp(&self) -> &BHyp {
        &self.bhyp
    }

    /// Get a mutable reference to the underlying BHyp
    /// WARNING: After using this, you should call recompute_interface()
    pub fn bhyp_mut(&mut self) -> &mut BHyp {
        &mut self.bhyp
    }

    /// Check if a node (in the main bhyp) is in the input interface
    pub fn is_input(&self, node: NodeId) -> bool {
        self.input_map.values().any(|&n| n == node)
    }

    /// Check if a node (in the main bhyp) is in the output interface
    pub fn is_output(&self, node: NodeId) -> bool {
        self.output_map.values().any(|&n| n == node)
    }

    /// Check if a node is internal (neither input nor output)
    pub fn is_internal(&self, node: NodeId) -> bool {
        !self.is_input(node) && !self.is_output(node)
    }

    // Delegate read-only methods to underlying BHyp

    pub fn nodes(&self) -> &HashSet<NodeId> {
        self.bhyp.nodes()
    }

    pub fn edges(&self) -> &HashSet<EdgeId> {
        self.bhyp.edges()
    }

    pub fn get_sources(&self, edge: EdgeId) -> Option<Vec<NodeId>> {
        self.bhyp.get_sources(edge)
    }

    pub fn get_sources_with_binding(&self, edge: EdgeId) -> Option<&Vec<SourceWithBinding>> {
        self.bhyp.get_sources_with_binding(edge)
    }

    pub fn get_targets(&self, edge: EdgeId) -> Option<&Vec<NodeId>> {
        self.bhyp.get_targets(edge)
    }

    pub fn get_label(&self, edge: EdgeId) -> Option<&Label> {
        self.bhyp.get_label(edge)
    }

    pub fn in_degree(&self, node: NodeId) -> usize {
        self.bhyp.in_degree(node)
    }

    pub fn out_degree(&self, node: NodeId) -> usize {
        self.bhyp.out_degree(node)
    }

    pub fn in_binding_degree(&self, node: NodeId) -> usize {
        self.bhyp.in_binding_degree(node)
    }

    pub fn out_binding_degree(&self, node: NodeId) -> usize {
        self.bhyp.out_binding_degree(node)
    }

    pub fn is_discrete(&self) -> bool {
        self.bhyp.is_discrete()
    }

    pub fn is_empty(&self) -> bool {
        self.bhyp.is_empty()
    }

    pub fn is_first_order(&self) -> bool {
        self.bhyp.is_first_order()
    }

    pub fn signature(&self) -> Option<&Signature> {
        self.bhyp.signature()
    }
}

impl Default for BHyp_with_interface {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Display for BHyp_with_interface {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Hypergraph with Binding with Interface:")?;
        writeln!(f, "  Input interface: {} nodes (discrete)", self.input_interface.nodes().len())?;
        write!(f, "    Maps: ")?;
        for (iface_node, bhyp_node) in &self.input_map {
            write!(f, "{:?}->{:?} ", iface_node, bhyp_node)?;
        }
        writeln!(f)?;
        writeln!(f, "  Output interface: {} nodes (discrete)", self.output_interface.nodes().len())?;
        write!(f, "    Maps: ")?;
        for (iface_node, bhyp_node) in &self.output_map {
            write!(f, "{:?}->{:?} ", iface_node, bhyp_node)?;
        }
        writeln!(f)?;
        writeln!(f)?;
        write!(f, "{}", self.bhyp)?;
        Ok(())
    }
}

#[cfg(test)]
mod interface_tests {
    use super::*;

    #[test]
    fn test_empty_interface() {
        let g = BHyp_with_interface::new();
        assert!(g.input_interface().is_discrete());
        assert!(g.input_interface().is_empty());
        assert!(g.output_interface().is_discrete());
        assert!(g.output_interface().is_empty());
    }

    #[test]
    fn test_isolated_node_is_both_input_and_output() {
        let mut g = BHyp_with_interface::new();
        let n = g.add_node();
        
        // An isolated node has in=0, in_b=0, out=0
        // So it's both input and output
        assert!(g.is_input(n));
        assert!(g.is_output(n));
        
        // Check interface hypergraphs are discrete
        assert!(g.input_interface().is_discrete());
        assert!(g.output_interface().is_discrete());
        assert_eq!(g.input_interface().nodes().len(), 1);
        assert_eq!(g.output_interface().nodes().len(), 1);
    }

    #[test]
    fn test_simple_edge_interface() {
        let mut g = BHyp_with_interface::new();
        
        let n1 = g.add_node(); // will be source
        let n2 = g.add_node(); // will be target
        
        g.add_edge(
            vec![SourceWithBinding { source: n1, bound: vec![] }],
            vec![n2],
            Some(Label::Symbol("f".to_string())),
        ).unwrap();
        
        // n1: in=0, in_b=0, out=1 → input only
        // n2: in=1, in_b=0, out=0 → output only
        assert!(g.is_input(n1));
        assert!(!g.is_output(n1));
        
        assert!(!g.is_input(n2));
        assert!(g.is_output(n2));
        
        // Check discrete interfaces
        assert!(g.input_interface().is_discrete());
        assert!(g.output_interface().is_discrete());
        assert_eq!(g.input_interface().nodes().len(), 1);
        assert_eq!(g.output_interface().nodes().len(), 1);
        
        // Check mappings
        assert!(g.input_interface_nodes().contains(&n1));
        assert!(g.output_interface_nodes().contains(&n2));
    }

    #[test]
    fn test_bound_node_not_in_input() {
        let mut g = BHyp_with_interface::new();
        
        let x = g.add_node();      // bound variable
        let body = g.add_node();   // body of lambda
        let out = g.add_node();    // output
        
        // Lambda binding x in the body
        g.add_edge(
            vec![SourceWithBinding { source: body, bound: vec![x] }],
            vec![out],
            Some(Label::Symbol("λ".to_string())),
        ).unwrap();
        
        // x: in=0, in_b=1, out=0 → NOT input (because in_b > 0), IS output
        assert!(!g.is_input(x), "Bound variable should not be in input interface");
        assert!(g.is_output(x));
        
        // body: in=0, in_b=0, out=1 → input only
        assert!(g.is_input(body));
        assert!(!g.is_output(body));
        
        // out: in=1, in_b=0, out=0 → output only
        assert!(!g.is_input(out));
        assert!(g.is_output(out));
        
        // Check interface sizes
        assert_eq!(g.input_interface().nodes().len(), 1); // only body
        assert_eq!(g.output_interface().nodes().len(), 2); // x and out
    }

    #[test]
    fn test_lambda_with_application() {
        // λx. f(x) - the bound variable is used
        let mut g = BHyp_with_interface::new();
        
        let x = g.add_node();        // bound variable
        let f_out = g.add_node();    // output of f(x)
        let lambda_out = g.add_node(); // output of whole expression
        
        // f(x)
        g.add_edge(
            vec![SourceWithBinding { source: x, bound: vec![] }],
            vec![f_out],
            Some(Label::Symbol("f".to_string())),
        ).unwrap();
        
        // λx binds x, takes f_out as body
        g.add_edge(
            vec![SourceWithBinding { source: f_out, bound: vec![x] }],
            vec![lambda_out],
            Some(Label::Symbol("λ".to_string())),
        ).unwrap();
        
        // x: in=0, in_b=1, out=1 → neither input (in_b>0) nor output (out>0)
        assert!(!g.is_input(x));
        assert!(!g.is_output(x));
        assert!(g.is_internal(x));
        
        // f_out: in=1, in_b=0, out=1 → neither
        assert!(!g.is_input(f_out));
        assert!(!g.is_output(f_out));
        
        // lambda_out: in=1, in_b=0, out=0 → output only
        assert!(!g.is_input(lambda_out));
        assert!(g.is_output(lambda_out));
        
        // Check interfaces are discrete
        assert!(g.input_interface().is_discrete());
        assert!(g.output_interface().is_discrete());
        
        // Check interface sizes
        assert!(g.input_interface().is_empty());
        assert_eq!(g.output_interface().nodes().len(), 1);
        assert!(g.output_interface_nodes().contains(&lambda_out));
    }

    #[test]
    fn test_remove_edge_updates_interface() {
        let mut g = BHyp_with_interface::new();
        
        let n1 = g.add_node();
        let n2 = g.add_node();
        
        let e = g.add_edge(
            vec![SourceWithBinding { source: n1, bound: vec![] }],
            vec![n2],
            None,
        ).unwrap();
        
        assert!(g.is_input(n1));
        assert!(!g.is_input(n2));
        assert_eq!(g.input_interface().nodes().len(), 1);
        assert_eq!(g.output_interface().nodes().len(), 1);
        
        // Remove edge
        g.remove_edge(e).unwrap();
        
        // Now both nodes are isolated
        assert!(g.is_input(n1));
        assert!(g.is_output(n1));
        assert!(g.is_input(n2));
        assert!(g.is_output(n2));
        
        // Both should be in both interfaces
        assert_eq!(g.input_interface().nodes().len(), 2);
        assert_eq!(g.output_interface().nodes().len(), 2);
    }
    
    #[test]
    fn test_interface_mapping() {
        let mut g = BHyp_with_interface::new();
        
        let n1 = g.add_node();
        let n2 = g.add_node();
        
        g.add_edge(
            vec![SourceWithBinding { source: n1, bound: vec![] }],
            vec![n2],
            None,
        ).unwrap();
        
        // Check that we can map from interface nodes back to bhyp nodes
        let input_nodes: Vec<_> = g.input_interface().nodes().iter().copied().collect();
        assert_eq!(input_nodes.len(), 1);
        let mapped = g.map_input_node(input_nodes[0]).unwrap();
        assert_eq!(mapped, n1);
        
        let output_nodes: Vec<_> = g.output_interface().nodes().iter().copied().collect();
        assert_eq!(output_nodes.len(), 1);
        let mapped = g.map_output_node(output_nodes[0]).unwrap();
        assert_eq!(mapped, n2);
    }
}



fn format_label(label: &Label) -> String {
    match label {
        Label::Symbol(s) => s.clone(),
        Label::Meta(name, arity) => format!("{}:{}", name, arity)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_hypergraph() {
        let mut g = BHyp::new();

        let n1 = g.add_node();
        let n2 = g.add_node();
        let n3 = g.add_node();

        let e = g
            .add_edge(
                vec![SourceWithBinding {
                    source: n1,
                    bound: vec![],
                }],
                vec![n2, n3],
                Some(Label::Symbol("f".to_string())),
            )
            .unwrap();

        assert_eq!(g.get_arity(e), Some(1));
        assert_eq!(g.get_coarity(e), Some(2));
    }

    #[test]
    fn test_lambda_binding() {
        // Example: λx. f(x) from the paper
        let mut g = BHyp::new();

        let x = g.add_node(); // the bound variable
        let f_node = g.add_node(); // output of λ
        let lambda_out = g.add_node(); // output of the whole expression

        // f edge with x as source
        let _f_edge = g
            .add_edge(
                vec![SourceWithBinding {
                    source: x,
                    bound: vec![],
                }],
                vec![f_node],
                Some(Label::Symbol("f".to_string())),
            )
            .unwrap();

        // λ edge that binds x
        let _lambda_edge = g
            .add_edge(
                vec![SourceWithBinding {
                    source: f_node,
                    bound: vec![x],
                }],
                vec![lambda_out],
                Some(Label::Lambda),
            )
            .unwrap();

        assert_eq!(g.in_binding_degree(x), 1);
        assert_eq!(g.out_degree(x), 1);
    }

    #[test]
    fn test_signature_validation() {
        let mut sig = Signature::new();
        sig.add_symbol("λ".to_string(), vec![1]); // λ binds 1 variable

        let mut g = BHyp::with_signature(sig);

        let x = g.add_node();
        let body = g.add_node();
        let out = g.add_node();

        // This should succeed
        let result = g.add_edge(
            vec![SourceWithBinding {
                source: body,
                bound: vec![x],
            }],
            vec![out],
            Some(Label::Symbol("λ".to_string())),
        );

        assert!(result.is_ok());

        // This should fail (wrong number of bound variables)
        let result = g.add_edge(
            vec![SourceWithBinding {
                source: body,
                bound: vec![], // Should have 1 bound variable
            }],
            vec![out],
            Some(Label::Symbol("λ".to_string())),
        );

        assert!(result.is_err());
    }
}