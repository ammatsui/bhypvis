// implementation for categorical constructions
// morphisms,
// pushout complements, pushouts, DPO, etc.


use std::collections::{HashMap, HashSet};
use std::fmt;

// Assuming these are imported from the bhyp module
use crate::bhyp::{BHyp, BHyp_with_interface, EdgeId, Label, NodeId, SourceWithBinding};

/// Error types for morphism construction
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MorphismError {
    MissingNodeMapping(NodeId),
    MissingEdgeMapping(EdgeId),
    IncompatibleSources(EdgeId),
    IncompatibleTargets(EdgeId),
    IncompatibleLabels(EdgeId),
    IncompatibleBinding(EdgeId),
    TargetNodeNotFound(NodeId),
    TargetEdgeNotFound(EdgeId),
    DomainMismatch,
}

impl fmt::Display for MorphismError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MorphismError::MissingNodeMapping(n) => write!(f, "Node {:?} has no mapping", n),
            MorphismError::MissingEdgeMapping(e) => write!(f, "Edge {:?} has no mapping", e),
            MorphismError::IncompatibleSources(e) => {
                write!(f, "Edge {:?} mapping doesn't preserve sources", e)
            }
            MorphismError::IncompatibleTargets(e) => {
                write!(f, "Edge {:?} mapping doesn't preserve targets", e)
            }
            MorphismError::IncompatibleLabels(e) => {
                write!(f, "Edge {:?} mapping doesn't preserve labels", e)
            }
            MorphismError::IncompatibleBinding(e) => {
                write!(f, "Edge {:?} mapping doesn't preserve binding", e)
            }
            MorphismError::TargetNodeNotFound(n) => {
                write!(f, "Target node {:?} not in codomain", n)
            }
            MorphismError::TargetEdgeNotFound(e) => {
                write!(f, "Target edge {:?} not in codomain", e)
            }
            MorphismError::DomainMismatch => {
                write!(f, "Morphisms cannot be composed")
            }
        }
    }
}

/// Error types for categorical constructions
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CategoricalError {
    MorphismError(MorphismError),
    /// Pushout complement doesn't exist (gluing condition violated)
    GluingConditionViolated(String),
    /// Identification condition violated
    IdentificationConditionViolated(String),
    /// Dangling condition violated
    DanglingConditionViolated(String),
    /// Morphisms don't share the same domain
    DomainMismatch,
    /// Morphisms don't share the same codomain
    CodomainMismatch,
    /// General construction failure
    ConstructionFailed(String),
}

impl fmt::Display for CategoricalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CategoricalError::MorphismError(e) => write!(f, "Morphism error: {}", e),
            CategoricalError::GluingConditionViolated(s) => {
                write!(f, "Gluing condition violated: {}", s)
            }
            CategoricalError::IdentificationConditionViolated(s) => {
                write!(f, "Identification condition violated: {}", s)
            }
            CategoricalError::DanglingConditionViolated(s) => {
                write!(f, "Dangling condition violated: {}", s)
            }
            CategoricalError::DomainMismatch => write!(f, "Morphisms don't share the same domain"),
            CategoricalError::CodomainMismatch => {
                write!(f, "Morphisms don't share the same codomain")
            }
            CategoricalError::ConstructionFailed(s) => write!(f, "Construction failed: {}", s),
        }
    }
}

impl From<MorphismError> for CategoricalError {
    fn from(e: MorphismError) -> Self {
        CategoricalError::MorphismError(e)
    }
}

/// A morphism between two BHyp instances
#[derive(Debug, Clone)]
pub struct BHypMorphism {
    /// The domain hypergraph (owned)
    domain: BHyp,
    /// The codomain hypergraph (owned)
    codomain: BHyp,
    /// Mapping from domain nodes to codomain nodes
    on_nodes: HashMap<NodeId, NodeId>,
    /// Mapping from domain edges to codomain edges
    on_edges: HashMap<EdgeId, EdgeId>,
}

impl BHypMorphism {
    /// Create a new morphism with validation
    pub fn new(
        domain: BHyp,
        codomain: BHyp,
        on_nodes: HashMap<NodeId, NodeId>,
        on_edges: HashMap<EdgeId, EdgeId>,
    ) -> Result<Self, MorphismError> {
        let morphism = BHypMorphism {
            domain,
            codomain,
            on_nodes,
            on_edges,
        };
        morphism.validate()?;
        Ok(morphism)
    }

    /// Create a morphism without validation (unsafe)
    pub fn new_unchecked(
        domain: BHyp,
        codomain: BHyp,
        on_nodes: HashMap<NodeId, NodeId>,
        on_edges: HashMap<EdgeId, EdgeId>,
    ) -> Self {
        BHypMorphism {
            domain,
            codomain,
            on_nodes,
            on_edges,
        }
    }

    /// Validate that this is a valid morphism
    pub fn validate(&self) -> Result<(), MorphismError> {
        // Check all domain nodes are mapped
        for &node in self.domain.nodes() {
            if !self.on_nodes.contains_key(&node) {
                return Err(MorphismError::MissingNodeMapping(node));
            }
            let target = self.on_nodes[&node];
            if !self.codomain.nodes().contains(&target) {
                return Err(MorphismError::TargetNodeNotFound(target));
            }
        }

        // Check all domain edges are mapped
        for &edge in self.domain.edges() {
            if !self.on_edges.contains_key(&edge) {
                return Err(MorphismError::MissingEdgeMapping(edge));
            }
            let target_edge = self.on_edges[&edge];
            if !self.codomain.edges().contains(&target_edge) {
                return Err(MorphismError::TargetEdgeNotFound(target_edge));
            }

            // Check source preservation
            if let (Some(dom_swbs), Some(cod_swbs)) = (
                self.domain.get_sources_with_binding(edge),
                self.codomain.get_sources_with_binding(target_edge),
            ) {
                if dom_swbs.len() != cod_swbs.len() {
                    return Err(MorphismError::IncompatibleSources(edge));
                }

                for (dom_swb, cod_swb) in dom_swbs.iter().zip(cod_swbs.iter()) {
                    if self.on_nodes[&dom_swb.source] != cod_swb.source {
                        return Err(MorphismError::IncompatibleSources(edge));
                    }
                    if dom_swb.bound.len() != cod_swb.bound.len() {
                        return Err(MorphismError::IncompatibleBinding(edge));
                    }
                    for (dom_bound, cod_bound) in dom_swb.bound.iter().zip(cod_swb.bound.iter()) {
                        if self.on_nodes[dom_bound] != *cod_bound {
                            return Err(MorphismError::IncompatibleBinding(edge));
                        }
                    }
                }
            }

            // Check target preservation
            if let (Some(dom_targets), Some(cod_targets)) = (
                self.domain.get_targets(edge),
                self.codomain.get_targets(target_edge),
            ) {
                if dom_targets.len() != cod_targets.len() {
                    return Err(MorphismError::IncompatibleTargets(edge));
                }
                for (dom_t, cod_t) in dom_targets.iter().zip(cod_targets.iter()) {
                    if self.on_nodes[dom_t] != *cod_t {
                        return Err(MorphismError::IncompatibleTargets(edge));
                    }
                }
            }

            // Check label preservation
            match (
                self.domain.get_label(edge),
                self.codomain.get_label(target_edge),
            ) {
                (Some(l1), Some(l2)) if l1 != l2 => {
                    return Err(MorphismError::IncompatibleLabels(edge));
                }
                (Some(_), None) | (None, Some(_)) => {
                    return Err(MorphismError::IncompatibleLabels(edge));
                }
                _ => {}
            }
        }

        Ok(())
    }

    pub fn domain(&self) -> &BHyp {
        &self.domain
    }

    pub fn codomain(&self) -> &BHyp {
        &self.codomain
    }

    pub fn on_nodes(&self) -> &HashMap<NodeId, NodeId> {
        &self.on_nodes
    }

    pub fn on_edges(&self) -> &HashMap<EdgeId, EdgeId> {
        &self.on_edges
    }

    pub fn map_node(&self, node: NodeId) -> Option<NodeId> {
        self.on_nodes.get(&node).copied()
    }

    pub fn map_edge(&self, edge: EdgeId) -> Option<EdgeId> {
        self.on_edges.get(&edge).copied()
    }

    pub fn node_image(&self) -> HashSet<NodeId> {
        self.on_nodes.values().copied().collect()
    }

    pub fn edge_image(&self) -> HashSet<EdgeId> {
        self.on_edges.values().copied().collect()
    }

    /// Check if this morphism is a monomorphism (injective on nodes and edges)
    pub fn is_monomorphism(&self) -> bool {
        let node_values: Vec<_> = self.on_nodes.values().collect();
        let node_set: HashSet<_> = node_values.iter().collect();
        if node_values.len() != node_set.len() {
            return false;
        }

        let edge_values: Vec<_> = self.on_edges.values().collect();
        let edge_set: HashSet<_> = edge_values.iter().collect();
        edge_values.len() == edge_set.len()
    }

    /// Check if this morphism is an epimorphism (surjective on nodes and edges)
    pub fn is_epimorphism(&self) -> bool {
        let node_image = self.node_image();
        if node_image != *self.codomain.nodes() {
            return false;
        }

        let edge_image = self.edge_image();
        edge_image == *self.codomain.edges()
    }

    /// Check if this morphism is an isomorphism (bijective)
    pub fn is_isomorphism(&self) -> bool {
        self.is_monomorphism() && self.is_epimorphism()
    }

    /// Check if this is the identity morphism
    pub fn is_identity(&self) -> bool {
        // Check same structure
        if self.domain.nodes().len() != self.codomain.nodes().len() {
            return false;
        }
        if self.domain.edges().len() != self.codomain.edges().len() {
            return false;
        }
        self.on_nodes.iter().all(|(k, v)| k == v) && self.on_edges.iter().all(|(k, v)| k == v)
    }

    /// Compose two morphisms: self ∘ other (first apply other, then self)
    pub fn compose(&self, other: &BHypMorphism) -> Result<BHypMorphism, MorphismError> {
        // Check that other's codomain matches self's domain
        if other.codomain.nodes() != self.domain.nodes()
            || other.codomain.edges() != self.domain.edges()
        {
            return Err(MorphismError::DomainMismatch);
        }

        let composed_nodes: HashMap<NodeId, NodeId> = other
            .on_nodes
            .iter()
            .map(|(&n, &m)| (n, self.on_nodes[&m]))
            .collect();

        let composed_edges: HashMap<EdgeId, EdgeId> = other
            .on_edges
            .iter()
            .map(|(&e, &f)| (e, self.on_edges[&f]))
            .collect();

        BHypMorphism::new(
            other.domain.clone(),
            self.codomain.clone(),
            composed_nodes,
            composed_edges,
        )
    }

    
}

impl PartialEq for BHypMorphism {
    fn eq(&self, other: &Self) -> bool {
        // Check that domains are equal (same nodes and edges)
        if self.domain.nodes() != other.domain.nodes() {
            return false;
        }
        if self.domain.edges() != other.domain.edges() {
            return false;
        }

        // Check that codomains are equal (same nodes and edges)
        if self.codomain.nodes() != other.codomain.nodes() {
            return false;
        }
        if self.codomain.edges() != other.codomain.edges() {
            return false;
        }

        // Check that every node in the domain maps to the same node in both morphisms
        for &node in self.domain.nodes() {
            match (self.on_nodes.get(&node), other.on_nodes.get(&node)) {
                (Some(&n1), Some(&n2)) if n1 != n2 => return false,
                (Some(_), None) | (None, Some(_)) => return false,
                _ => {}
            }
        }

        // Check that every edge in the domain maps to the same edge in both morphisms
        for &edge in self.domain.edges() {
            match (self.on_edges.get(&edge), other.on_edges.get(&edge)) {
                (Some(&e1), Some(&e2)) if e1 != e2 => return false,
                (Some(_), None) | (None, Some(_)) => return false,
                _ => {}
            }
        }

        true
    }
}

/// Create the identity morphism on a BHyp
pub fn identity_morphism(bhyp: &BHyp) -> BHypMorphism {
    let on_nodes: HashMap<_, _> = bhyp.nodes().iter().map(|&n| (n, n)).collect();
    let on_edges: HashMap<_, _> = bhyp.edges().iter().map(|&e| (e, e)).collect();
    BHypMorphism::new_unchecked(bhyp.clone(), bhyp.clone(), on_nodes, on_edges)
}

pub fn combined_interface_to_bhyp_morphism(
    bhyp: &BHyp_with_interface,
) -> Result<BHypMorphism, MorphismError> {
    let mut combined_interface = BHyp::new();
    let mut node_map: HashMap<NodeId, NodeId> = HashMap::new();

    // These are nodes of the underlying BHyp that are either input or output.
    let combined_nodes = bhyp.combined_interface_nodes();

    for h_node in combined_nodes {
        let interface_node = combined_interface.add_node();
        node_map.insert(interface_node, h_node);
    }

    BHypMorphism::new(
        combined_interface,
        bhyp.bhyp().clone(),
        node_map,
        HashMap::new(), // interface is discrete, so no edge map
    )
}

/// Span and CoSpan structs
#[derive(Debug, Clone)]
pub struct Span {
    /// left-hand side
    pub left: BHyp,
    /// middle
    pub middle: BHyp,
    /// right-hand side 
    pub right: BHyp,
    /// morphisms
    pub to_l: BHypMorphism,
    pub to_r: BHypMorphism
}

#[derive(Debug, Clone)]
pub struct CoSpan {
    /// left-hand side
    pub left: BHyp,
    /// middle
    pub middle: BHyp,
    /// right-hand side 
    pub right: BHyp,
    /// morphisms
    pub from_l: BHypMorphism,
    pub from_r: BHypMorphism
}



// ============================================================================
// Pushout and Pushout Complement
// ============================================================================

// ============================================================================
// Result Types
// ============================================================================

/// Result of a pushout computation
#[derive(Debug, Clone)]
pub struct PushoutResult {
    /// The pushout object D
    pub pushout: BHyp,
    /// Universal morphism from B to D
    pub morphism_from_b: BHypMorphism,
    /// Universal morphism from C to D  
    pub morphism_from_c: BHypMorphism,
}

/// Result of a pullback computation
#[derive(Debug, Clone)]
pub struct PullbackResult {
    /// The pullback object P
    pub pullback: BHyp,
    /// Universal morphism from P to B
    pub morphism_to_b: BHypMorphism,
    /// Universal morphism from P to C
    pub morphism_to_c: BHypMorphism,
}

/// Result of a pushout complement computation
#[derive(Debug, Clone)]
pub struct PushoutComplementResult {
    /// The pushout complement object C
    pub complement: BHyp,
    /// Morphism from K to C
    pub morphism_from_k: BHypMorphism,
    /// Morphism from C to G
    pub morphism_to_g: BHypMorphism,
}

///////////////////
/// morphisms and inclusions
/// ///////////////
//// i think that could be moved to categorical.rs

/// Finds all monomorphic inclusions (occurrences) of pattern H in target G.
pub fn find_all_occurrences(pattern: &BHyp, target: &BHyp) -> Vec<BHypMorphism> {
    let mut results = Vec::new();
    let pattern_edges: Vec<EdgeId> = pattern.edges().iter().copied().collect();
    
    let mut node_map = HashMap::new();
    let mut edge_map = HashMap::new();
    
    backtrack_match(
        0,
        &pattern_edges,
        pattern,
        target,
        &mut node_map,
        &mut edge_map,
        &mut results,
    );
    
    results
}

fn backtrack_match(
    edge_idx: usize,
    pattern_edges: &[EdgeId],
    pattern: &BHyp,
    target: &BHyp,
    current_node_map: &mut HashMap<NodeId, NodeId>,
    current_edge_map: &mut HashMap<EdgeId, EdgeId>,
    results: &mut Vec<BHypMorphism>,
) {
    // Base Case: All edges matched
    if edge_idx == pattern_edges.len() {
        // (Assuming no isolated nodes in H. If H has isolated nodes, you'd 
        // need a secondary loop here to map remaining unmapped nodes in pattern.nodes())
        if let Ok(m) = BHypMorphism::new(
            pattern.clone(), 
            target.clone(), 
            current_node_map.clone(), 
            current_edge_map.clone()
        ) {
            results.push(m);
        }
        return;
    }

    let p_edge = pattern_edges[edge_idx];
    
    for &t_edge in target.edges() {
        // 1. Check Label
        if pattern.get_label(p_edge) != target.get_label(t_edge) { continue; }
        
        // 2. Prevent mapping multiple pattern edges to the same target edge
        if current_edge_map.values().any(|&e| e == t_edge) { continue; }
        
        let p_sources = pattern.get_sources_with_binding(p_edge).unwrap();
        let p_targets = pattern.get_targets(p_edge).unwrap();
        
        let t_sources = target.get_sources_with_binding(t_edge).unwrap();
        let t_targets = target.get_targets(t_edge).unwrap();
        
        // 3. Arity and Co-arity must match
        if p_sources.len() != t_sources.len() || p_targets.len() != t_targets.len() { continue; }
        
        let mut local_node_additions = Vec::new();
        let mut valid = true;
        
        // Helper to enforce injectivity while mapping nodes
        let mut try_map_node = |p_n: NodeId, t_n: NodeId| -> bool {
            if let Some(&existing) = current_node_map.get(&p_n) {
                existing == t_n // Must agree with previous mappings
            } else {
                // Must be injective: target node can't already be mapped to a different pattern node
                if current_node_map.values().any(|&n| n == t_n) {
                    return false;
                }
                current_node_map.insert(p_n, t_n);
                local_node_additions.push(p_n);
                true
            }
        };
        
        // 4. Map Targets
        for (i, &p_n) in p_targets.iter().enumerate() {
            if !try_map_node(p_n, t_targets[i]) { valid = false; break; }
        }
        
        // 5. Map Sources and Bindings
        if valid {
            for (i, p_swb) in p_sources.iter().enumerate() {
                let t_swb = &t_sources[i];
                if p_swb.bound.len() != t_swb.bound.len() { valid = false; break; }
                
                if !try_map_node(p_swb.source, t_swb.source) { valid = false; break; }
                
                for (j, &p_b) in p_swb.bound.iter().enumerate() {
                    if !try_map_node(p_b, t_swb.bound[j]) { valid = false; break; }
                }
                if !valid { break; }
            }
        }
        
        // 6. Recurse if valid
        if valid {
            current_edge_map.insert(p_edge, t_edge);
            backtrack_match(edge_idx + 1, pattern_edges, pattern, target, current_node_map, current_edge_map, results);
            current_edge_map.remove(&p_edge);
        }
        
        // 7. Backtrack (undo local mappings)
        for p_n in local_node_additions {
            current_node_map.remove(&p_n);
        }
    }
}


/// Check if T is a subhypergraph of G, and if so return the inclusion morphism
pub fn find_subhypergraph_inclusion(t: &BHyp, g: &BHyp) -> Option<BHypMorphism> {
    // T can only be a subhypergraph if it has at most as many nodes and edges as G
    if t.nodes().len() > g.nodes().len() || t.edges().len() > g.edges().len() {
        return None;
    }

    let t_nodes: Vec<NodeId> = t.nodes().iter().copied().collect();
    let g_nodes: Vec<NodeId> = g.nodes().iter().copied().collect();

    // Empty T is always a subhypergraph of G
    if t_nodes.is_empty() && t.edges().is_empty() {
        return Some(BHypMorphism::new(
            t.clone(), g.clone(), HashMap::new(), HashMap::new()
        ).unwrap());
    }

    // For small graphs, try all possible injective mappings from T to G
    fn try_inclusion(
        t: &BHyp,
        g: &BHyp,
        t_nodes: &[NodeId],
        g_nodes: &[NodeId],
        node_map: &mut HashMap<NodeId, NodeId>,
        idx: usize,
        used: &mut HashSet<NodeId>,
    ) -> Option<HashMap<EdgeId, EdgeId>> {
        if idx == t_nodes.len() {
            // Check if this node mapping induces a valid edge inclusion
            let mut edge_map: HashMap<EdgeId, EdgeId> = HashMap::new();

            for &e_t in t.edges() {
                let mut found = false;
                for &e_g in g.edges() {
                    if edge_map.values().any(|&e| e == e_g) {
                        continue;
                    }

                    // Check compatibility
                    let swbs_t = t.get_sources_with_binding(e_t).unwrap();
                    let swbs_g = g.get_sources_with_binding(e_g).unwrap();
                    let targets_t = t.get_targets(e_t).unwrap();
                    let targets_g = g.get_targets(e_g).unwrap();

                    if swbs_t.len() != swbs_g.len() || targets_t.len() != targets_g.len() {
                        continue;
                    }

                    let mut compatible = true;

                    // Check sources and bindings
                    for (s_t, s_g) in swbs_t.iter().zip(swbs_g.iter()) {
                        if node_map[&s_t.source] != s_g.source {
                            compatible = false;
                            break;
                        }
                        if s_t.bound.len() != s_g.bound.len() {
                            compatible = false;
                            break;
                        }
                        for (b_t, b_g) in s_t.bound.iter().zip(s_g.bound.iter()) {
                            if node_map[b_t] != *b_g {
                                compatible = false;
                                break;
                            }
                        }
                        if !compatible {
                            break;
                        }
                    }

                    if !compatible {
                        continue;
                    }

                    // Check targets
                    for (t_t, t_g) in targets_t.iter().zip(targets_g.iter()) {
                        if node_map[t_t] != *t_g {
                            compatible = false;
                            break;
                        }
                    }

                    if !compatible {
                        continue;
                    }

                    // Check labels
                    if t.get_label(e_t) != g.get_label(e_g) {
                        continue;
                    }

                    edge_map.insert(e_t, e_g);
                    found = true;
                    break;
                }

                if !found {
                    return None;
                }
            }

            return Some(edge_map);
        }

        let n_t = t_nodes[idx];
        for &n_g in g_nodes {
            if used.contains(&n_g) {
                continue;
            }

            node_map.insert(n_t, n_g);
            used.insert(n_g);

            if let Some(edge_map) = try_inclusion(t, g, t_nodes, g_nodes, node_map, idx + 1, used) {
                return Some(edge_map);
            }

            node_map.remove(&n_t);
            used.remove(&n_g);
        }

        None
    }

    let mut node_map = HashMap::new();
    let mut used = HashSet::new();

    if let Some(edge_map) = try_inclusion(t, g, &t_nodes, &g_nodes, &mut node_map, 0, &mut used) {
        Some(BHypMorphism::new(
            t.clone(), g.clone(), node_map, edge_map
        ).unwrap())
    } else {
        None
    }
}

/// Check if T is a subhypergraph of G (without returning the morphism)
pub fn is_subhypergraph(t: &BHyp, g: &BHyp) -> bool {
    find_subhypergraph_inclusion(t, g).is_some()
}





// hypergraph inclusion 
pub fn build_inclusion(t: &BHyp, g: &BHyp) -> Result<BHypMorphism, MorphismError> {
    if is_subhypergraph(&t, &g) {
        
        let option = find_subhypergraph_inclusion(&t, &g);

// Converts Some(bhyp) -> Ok(bhyp)
// Converts None -> Err(CopyError::InvalidSubhypergraph(...))
    let result = option.ok_or(
    MorphismError::DomainMismatch
);   
return result
    }
 
    return Err(MorphismError::DomainMismatch);

    
        // let mut node_map = HashMap::new();
        // let mut edge_map = HashMap::new();

        // // For a strict inclusion, f(v) = v
        // for &node in h1.nodes() {
        //     if h2.nodes().contains(&node) {
        //         node_map.insert(node, node);
        //     }
        // }

        // // For a strict inclusion, f(e) = e
        // for &edge in h1.edges() {
        //     if h2.edges().contains(&edge) {
        //         edge_map.insert(edge, edge);
        //     }
        // }

        // BHypMorphism::new(
        //     h1.clone(), 
        //     h2.clone(),
        //     node_map,
        //     edge_map
        // )
}


// ============================================================================
// Union-Find helpers
// ============================================================================

fn find<T: Copy + Eq + std::hash::Hash>(parent: &mut HashMap<T, T>, x: T) -> T {
    if !parent.contains_key(&x) {
        parent.insert(x, x);
        return x;
    }
    if parent[&x] == x {
        return x;
    }
    let root = find(parent, parent[&x]);
    parent.insert(x, root);
    root
}

fn union<T: Copy + Eq + std::hash::Hash>(parent: &mut HashMap<T, T>, x: T, y: T) {
    let rx = find(parent, x);
    let ry = find(parent, y);
    if rx != ry {
        parent.insert(rx, ry);
    }
}

// ============================================================================
// Pushout
// ============================================================================

/// Compute the pushout of two morphisms f: A -> B and g: A -> C
///
/// ```text
///     A ---f---> B
///     |          |
///     g          f'
///     |          |
///     v          v
///     C ---g'--> D
/// ```
///
/// The pushout D is constructed by taking the disjoint union of B and C,
/// then quotienting by the equivalence relation that identifies f(a) ~ g(a)
/// for all a in A.
pub fn compute_pushout(
    f: &BHypMorphism, // f: A -> B
    g: &BHypMorphism, // g: A -> C
) -> Result<PushoutResult, CategoricalError> {
    // Verify f and g have the same domain
    if f.domain.nodes() != g.domain.nodes() || f.domain.edges() != g.domain.edges() {
        return Err(CategoricalError::DomainMismatch);
    }

    let a = &f.domain;
    let b = &f.codomain;
    let c = &g.codomain;

    // Build equivalence classes for nodes
    // We tag nodes with their source: ('B', id) or ('C', id)
    let mut node_parent: HashMap<(char, NodeId), (char, NodeId)> = HashMap::new();

    // Initialize all nodes from B and C
    for &n in b.nodes() {
        node_parent.insert(('B', n), ('B', n));
    }
    for &n in c.nodes() {
        node_parent.insert(('C', n), ('C', n));
    }

    // For each node a in A, identify f(a) in B with g(a) in C
    for &a_n in a.nodes() {
        let b_n = f.map_node(a_n).unwrap();
        let c_n = g.map_node(a_n).unwrap();
        union(&mut node_parent, ('B', b_n), ('C', c_n));
    }

    // Build equivalence classes for edges
    let mut edge_parent: HashMap<(char, EdgeId), (char, EdgeId)> = HashMap::new();

    for &e in b.edges() {
        edge_parent.insert(('B', e), ('B', e));
    }
    for &e in c.edges() {
        edge_parent.insert(('C', e), ('C', e));
    }

    // For each edge a in A, identify f(a) in B with g(a) in C
    for &a_e in a.edges() {
        let b_e = f.map_edge(a_e).unwrap();
        let c_e = g.map_edge(a_e).unwrap();
        union(&mut edge_parent, ('B', b_e), ('C', c_e));
    }

    // Construct the pushout D
    let mut pushout = BHyp::new();

    // Create pushout nodes, one per equivalence class
    let mut class_to_pushout_node: HashMap<(char, NodeId), NodeId> = HashMap::new();
    let mut tagged_to_pushout_node: HashMap<(char, NodeId), NodeId> = HashMap::new();

    // Process B nodes
    let mut b_nodes: Vec<_> = b.nodes().iter().copied().collect();
    b_nodes.sort();

    for n in b_nodes {
        let root = find(&mut node_parent, ('B', n));
        if !class_to_pushout_node.contains_key(&root) {
            let pn = pushout.add_node();
            class_to_pushout_node.insert(root, pn);
        }
        tagged_to_pushout_node.insert(('B', n), class_to_pushout_node[&root]);
    }

    // Process C nodes
    let mut c_nodes: Vec<_> = c.nodes().iter().copied().collect();
    c_nodes.sort();

    for n in c_nodes {
        let root = find(&mut node_parent, ('C', n));
        if !class_to_pushout_node.contains_key(&root) {
            let pn = pushout.add_node();
            class_to_pushout_node.insert(root, pn);
        }
        tagged_to_pushout_node.insert(('C', n), class_to_pushout_node[&root]);
    }

    // Create pushout edges, one per equivalence class
    let mut class_to_pushout_edge: HashMap<(char, EdgeId), EdgeId> = HashMap::new();
    let mut tagged_to_pushout_edge: HashMap<(char, EdgeId), EdgeId> = HashMap::new();

    // Process B edges first (they become representatives for merged classes)
    let mut b_edges: Vec<_> = b.edges().iter().copied().collect();
    b_edges.sort();

    for e in b_edges {
        let root = find(&mut edge_parent, ('B', e));
        if !class_to_pushout_edge.contains_key(&root) {
            let swbs = b.get_sources_with_binding(e).unwrap();
            let targets = b.get_targets(e).unwrap();
            let label = b.get_label(e).cloned();

            let new_swbs: Vec<SourceWithBinding> = swbs
                .iter()
                .map(|swb| SourceWithBinding {
                    source: tagged_to_pushout_node[&('B', swb.source)],
                    bound: swb
                        .bound
                        .iter()
                        .map(|&b| tagged_to_pushout_node[&('B', b)])
                        .collect(),
                })
                .collect();

            let new_targets: Vec<NodeId> = targets
                .iter()
                .map(|&t| tagged_to_pushout_node[&('B', t)])
                .collect();

            let pe = pushout.add_edge(new_swbs, new_targets, label).unwrap();
            class_to_pushout_edge.insert(root, pe);
        }
        tagged_to_pushout_edge.insert(('B', e), class_to_pushout_edge[&root]);
    }

    // Process C edges
    let mut c_edges: Vec<_> = c.edges().iter().copied().collect();
    c_edges.sort();

    for e in c_edges {
        let root = find(&mut edge_parent, ('C', e));
        if !class_to_pushout_edge.contains_key(&root) {
            let swbs = c.get_sources_with_binding(e).unwrap();
            let targets = c.get_targets(e).unwrap();
            let label = c.get_label(e).cloned();

            let new_swbs: Vec<SourceWithBinding> = swbs
                .iter()
                .map(|swb| SourceWithBinding {
                    source: tagged_to_pushout_node[&('C', swb.source)],
                    bound: swb
                        .bound
                        .iter()
                        .map(|&b| tagged_to_pushout_node[&('C', b)])
                        .collect(),
                })
                .collect();

            let new_targets: Vec<NodeId> = targets
                .iter()
                .map(|&t| tagged_to_pushout_node[&('C', t)])
                .collect();

            let pe = pushout.add_edge(new_swbs, new_targets, label).unwrap();
            class_to_pushout_edge.insert(root, pe);
        }
        tagged_to_pushout_edge.insert(('C', e), class_to_pushout_edge[&root]);
    }

    // Build morphisms f': B -> D and g': C -> D
    let b_to_d_nodes: HashMap<NodeId, NodeId> = b
        .nodes()
        .iter()
        .map(|&n| (n, tagged_to_pushout_node[&('B', n)]))
        .collect();
    let b_to_d_edges: HashMap<EdgeId, EdgeId> = b
        .edges()
        .iter()
        .map(|&e| (e, tagged_to_pushout_edge[&('B', e)]))
        .collect();

    let c_to_d_nodes: HashMap<NodeId, NodeId> = c
        .nodes()
        .iter()
        .map(|&n| (n, tagged_to_pushout_node[&('C', n)]))
        .collect();
    let c_to_d_edges: HashMap<EdgeId, EdgeId> = c
        .edges()
        .iter()
        .map(|&e| (e, tagged_to_pushout_edge[&('C', e)]))
        .collect();

    let f_prime = BHypMorphism::new(b.clone(), pushout.clone(), b_to_d_nodes, b_to_d_edges)?;

    let g_prime = BHypMorphism::new(c.clone(), pushout.clone(), c_to_d_nodes, c_to_d_edges)?;

    Ok(PushoutResult {
        pushout,
        morphism_from_b: f_prime,
        morphism_from_c: g_prime,
    })
}

// ============================================================================
// Pullback
// ============================================================================

/// Compute the pullback of two morphisms f: B -> D and g: C -> D
///
/// ```text
///     P ---p1---> B
///     |           |
///     p2          f
///     |           |
///     v           v
///     C ---g----> D
/// ```
///
/// The pullback P consists of pairs (b, c) where f(b) = g(c).
pub fn compute_pullback(
    f: &BHypMorphism, // f: B -> D
    g: &BHypMorphism, // g: C -> D
) -> Result<PullbackResult, CategoricalError> {
    // Verify f and g have the same codomain
    if f.codomain.nodes() != g.codomain.nodes() || f.codomain.edges() != g.codomain.edges() {
        return Err(CategoricalError::CodomainMismatch);
    }

    let b = &f.domain;
    let c = &g.domain;

    let mut pullback = BHyp::new();

    // Pullback nodes: pairs (b_n, c_n) where f(b_n) = g(c_n)
    let mut pair_to_pullback_node: HashMap<(NodeId, NodeId), NodeId> = HashMap::new();

    for &b_n in b.nodes() {
        for &c_n in c.nodes() {
            if f.map_node(b_n) == g.map_node(c_n) {
                let p_n = pullback.add_node();
                pair_to_pullback_node.insert((b_n, c_n), p_n);
            }
        }
    }

    // Pullback edges: pairs (b_e, c_e) where f(b_e) = g(c_e)
    // and all sources/targets/bindings match up
    let mut p_to_b_edges: HashMap<EdgeId, EdgeId> = HashMap::new();
    let mut p_to_c_edges: HashMap<EdgeId, EdgeId> = HashMap::new();

    for &b_e in b.edges() {
        for &c_e in c.edges() {
            if f.map_edge(b_e) != g.map_edge(c_e) {
                continue;
            }

            let b_swbs = b.get_sources_with_binding(b_e).unwrap();
            let c_swbs = c.get_sources_with_binding(c_e).unwrap();
            let b_targets = b.get_targets(b_e).unwrap();
            let c_targets = c.get_targets(c_e).unwrap();

            // Lengths must match
            if b_swbs.len() != c_swbs.len() || b_targets.len() != c_targets.len() {
                continue;
            }

            // Try to construct the pullback edge
            let mut valid = true;
            let mut new_swbs = Vec::new();
            let mut new_targets = Vec::new();

            // Check sources and bindings can be paired
            for (b_swb, c_swb) in b_swbs.iter().zip(c_swbs.iter()) {
                if let Some(&p_s) = pair_to_pullback_node.get(&(b_swb.source, c_swb.source)) {
                    // Check bindings
                    if b_swb.bound.len() != c_swb.bound.len() {
                        valid = false;
                        break;
                    }

                    let mut bound = Vec::new();
                    for (&b_b, &c_b) in b_swb.bound.iter().zip(c_swb.bound.iter()) {
                        if let Some(&p_b) = pair_to_pullback_node.get(&(b_b, c_b)) {
                            bound.push(p_b);
                        } else {
                            valid = false;
                            break;
                        }
                    }

                    if !valid {
                        break;
                    }

                    new_swbs.push(SourceWithBinding { source: p_s, bound });
                } else {
                    valid = false;
                    break;
                }
            }

            if !valid {
                continue;
            }

            // Check targets can be paired
            for (&b_t, &c_t) in b_targets.iter().zip(c_targets.iter()) {
                if let Some(&p_t) = pair_to_pullback_node.get(&(b_t, c_t)) {
                    new_targets.push(p_t);
                } else {
                    valid = false;
                    break;
                }
            }

            if !valid {
                continue;
            }

            let label = b.get_label(b_e).cloned();
            let p_e = pullback.add_edge(new_swbs, new_targets, label).unwrap();
            p_to_b_edges.insert(p_e, b_e);
            p_to_c_edges.insert(p_e, c_e);
        }
    }

    // Build morphisms p1: P -> B and p2: P -> C
    let p_to_b_nodes: HashMap<NodeId, NodeId> = pair_to_pullback_node
        .iter()
        .map(|(&(b_n, _), &p_n)| (p_n, b_n))
        .collect();
    let p_to_c_nodes: HashMap<NodeId, NodeId> = pair_to_pullback_node
        .iter()
        .map(|(&(_, c_n), &p_n)| (p_n, c_n))
        .collect();

    let p1 = BHypMorphism::new(pullback.clone(), b.clone(), p_to_b_nodes, p_to_b_edges)?;

    let p2 = BHypMorphism::new(pullback.clone(), c.clone(), p_to_c_nodes, p_to_c_edges)?;

    Ok(PullbackResult {
        pullback,
        morphism_to_b: p1,
        morphism_to_c: p2,
    })
}

// ============================================================================
// Pushout Complement
// ============================================================================
pub fn compute_pushout_complement(
    l: &BHypMorphism, // l: K -> L
    m: &BHypMorphism, // m: L -> G
) -> Result<PushoutComplementResult, CategoricalError> {
    let k = &l.domain;
    let l_graph = &l.codomain;
    let g = &m.codomain;

    let l_node_image: HashSet<NodeId> = l.node_image();
    let l_edge_image: HashSet<EdgeId> = l.edge_image();

    let m_node_image: HashSet<NodeId> = m.node_image();
    let m_edge_image: HashSet<EdgeId> = m.edge_image();

    // m(l(K)) in G
    let mlk_node_image: HashSet<NodeId> = l
        .on_nodes
        .values()
        .filter_map(|&l_n| m.map_node(l_n))
        .collect();

    let mlk_edge_image: HashSet<EdgeId> = l
        .on_edges
        .values()
        .filter_map(|&l_e| m.map_edge(l_e))
        .collect();

    // ========================================================================
    // Identification condition
    // ========================================================================
    //
    // If m identifies two distinct L-elements, they must both be in l(K).
    // This is still needed. But we do NOT collapse all K-preimages merely
    // because they have the same G-image; slot construction below handles that.
    // ========================================================================

    let l_nodes: Vec<NodeId> = l_graph.nodes().iter().copied().collect();

    for (i, &l1) in l_nodes.iter().enumerate() {
        for &l2 in l_nodes.iter().skip(i + 1) {
            if m.map_node(l1) == m.map_node(l2) {
                let l1_in_lk = l_node_image.contains(&l1);
                let l2_in_lk = l_node_image.contains(&l2);

                if !l1_in_lk || !l2_in_lk {
                    return Err(CategoricalError::IdentificationConditionViolated(format!(
                        "Nodes {:?} and {:?} identified by m but not both in l(K)",
                        l1, l2
                    )));
                }
            }
        }
    }

    let l_edges: Vec<EdgeId> = l_graph.edges().iter().copied().collect();

    for (i, &e1) in l_edges.iter().enumerate() {
        for &e2 in l_edges.iter().skip(i + 1) {
            if m.map_edge(e1) == m.map_edge(e2) {
                let e1_in_lk = l_edge_image.contains(&e1);
                let e2_in_lk = l_edge_image.contains(&e2);

                if !e1_in_lk || !e2_in_lk {
                    return Err(CategoricalError::IdentificationConditionViolated(format!(
                        "Edges {:?} and {:?} identified by m but not both in l(K)",
                        e1, e2
                    )));
                }
            }
        }
    }

    // ========================================================================
    // Deleted part: m(L \ l(K))
    // ========================================================================

    let deleted_nodes: HashSet<NodeId> = l_graph
        .nodes()
        .iter()
        .filter(|&&l_n| !l_node_image.contains(&l_n))
        .filter_map(|&l_n| m.map_node(l_n))
        .collect();

    let deleted_edges: HashSet<EdgeId> = l_graph
        .edges()
        .iter()
        .filter(|&&l_e| !l_edge_image.contains(&l_e))
        .filter_map(|&l_e| m.map_edge(l_e))
        .collect();

    for g_n in &deleted_nodes {
        if mlk_node_image.contains(g_n) {
            return Err(CategoricalError::IdentificationConditionViolated(format!(
                "G-node {:?} is both deleted and preserved",
                g_n
            )));
        }
    }

    for g_e in &deleted_edges {
        if mlk_edge_image.contains(g_e) {
            return Err(CategoricalError::IdentificationConditionViolated(format!(
                "G-edge {:?} is both deleted and preserved",
                g_e
            )));
        }
    }

    // ========================================================================
    // Dangling condition
    // ========================================================================
    //
    // Any edge that remains must not touch a deleted node.
    // ========================================================================

    for &g_e in g.edges() {
        if deleted_edges.contains(&g_e) {
            continue;
        }

        if let Some(swbs) = g.get_sources_with_binding(g_e) {
            for swb in swbs {
                if deleted_nodes.contains(&swb.source) {
                    return Err(CategoricalError::DanglingConditionViolated(format!(
                        "Preserved edge {:?} has deleted source {:?}",
                        g_e, swb.source
                    )));
                }

                for &b in &swb.bound {
                    if deleted_nodes.contains(&b) {
                        return Err(CategoricalError::DanglingConditionViolated(format!(
                            "Preserved edge {:?} binds deleted node {:?}",
                            g_e, b
                        )));
                    }
                }
            }
        }

        if let Some(targets) = g.get_targets(g_e) {
            for t in targets {
                if deleted_nodes.contains(&t) {
                    return Err(CategoricalError::DanglingConditionViolated(format!(
                        "Preserved edge {:?} has deleted target {:?}",
                        g_e, t
                    )));
                }
            }
        }
    }

    // ========================================================================
    // Construct C by slots over G-elements
    // ========================================================================

    let mut complement = BHyp::new();

    // K -> C
    let mut k_to_c_nodes: HashMap<NodeId, NodeId> = HashMap::new();
    let mut k_to_c_edges: HashMap<EdgeId, EdgeId> = HashMap::new();

    // C -> G
    let mut c_to_g_nodes: HashMap<NodeId, NodeId> = HashMap::new();
    let mut c_to_g_edges: HashMap<EdgeId, EdgeId> = HashMap::new();

    // For resolving incident nodes.
    let mut g_slot_to_c_node: HashMap<(NodeId, usize), NodeId> = HashMap::new();

    // ------------------------------------------------------------------------
    // Nodes: group K-nodes by G-image, then by L-image.
    //
    // For fixed g:
    //
    //   l_a: [k_a0, k_a1, ...]
    //   l_b: [k_b0, k_b1, ...]
    //
    // k_a0 and k_b0 share slot 0.
    // k_a1 and k_b1 share slot 1.
    //
    // If there is only one L-image over g, multiple K-preimages remain distinct.
    // This is the copy case.
    // ------------------------------------------------------------------------

    let mut node_fibers: HashMap<NodeId, HashMap<NodeId, Vec<NodeId>>> =
        HashMap::new();

    let mut k_nodes: Vec<NodeId> = k.nodes().iter().copied().collect();
    k_nodes.sort();

    for k_n in k_nodes {
        let l_n = l.map_node(k_n).ok_or_else(|| {
            CategoricalError::ConstructionFailed(format!(
                "l does not map K-node {:?}",
                k_n
            ))
        })?;

        let g_n = m.map_node(l_n).ok_or_else(|| {
            CategoricalError::ConstructionFailed(format!(
                "m does not map L-node {:?}",
                l_n
            ))
        })?;

        node_fibers
            .entry(g_n)
            .or_default()
            .entry(l_n)
            .or_default()
            .push(k_n);
    }

    for by_l in node_fibers.values_mut() {
        for ks in by_l.values_mut() {
            ks.sort();
        }
    }

    // Optional but recommended: require compatible fiber sizes when distinct
    // L-nodes are identified by m.
    for (&g_n, by_l) in &node_fibers {
        if by_l.len() > 1 {
            let sizes: HashSet<usize> = by_l.values().map(|ks| ks.len()).collect();

            if sizes.len() > 1 {
                return Err(CategoricalError::IdentificationConditionViolated(format!(
                    "Incompatible node fiber sizes over G-node {:?}: {:?}",
                    g_n, sizes
                )));
            }
        }
    }

    let mut g_node_keys: Vec<NodeId> = node_fibers.keys().copied().collect();
    g_node_keys.sort();

    for g_n in g_node_keys {
        let by_l = &node_fibers[&g_n];

        let max_slots = by_l
            .values()
            .map(|ks| ks.len())
            .max()
            .unwrap_or(0);

        for slot in 0..max_slots {
            let c_n = complement.add_node();
            g_slot_to_c_node.insert((g_n, slot), c_n);
            c_to_g_nodes.insert(c_n, g_n);
        }

        for ks in by_l.values() {
            for (slot, &k_n) in ks.iter().enumerate() {
                let c_n = g_slot_to_c_node[&(g_n, slot)];
                k_to_c_nodes.insert(k_n, c_n);
            }
        }
    }

    // Add context nodes: G-nodes outside m(L).
    //
    // Nodes in m(L) but not in m(l(K)) are deleted.
    let mut g_nodes: Vec<NodeId> = g.nodes().iter().copied().collect();
    g_nodes.sort();

    for g_n in g_nodes {
        if deleted_nodes.contains(&g_n) {
            continue;
        }

        if g_slot_to_c_node.contains_key(&(g_n, 0)) {
            continue;
        }

        if m_node_image.contains(&g_n) && !mlk_node_image.contains(&g_n) {
            continue;
        }

        let c_n = complement.add_node();
        g_slot_to_c_node.insert((g_n, 0), c_n);
        c_to_g_nodes.insert(c_n, g_n);
    }

    // ========================================================================
    // Edges: same slot logic
    // ========================================================================

    let mut g_slot_to_c_edge: HashMap<(EdgeId, usize), EdgeId> = HashMap::new();

    let mut edge_fibers: HashMap<EdgeId, HashMap<EdgeId, Vec<EdgeId>>> =
        HashMap::new();

    let mut k_edges: Vec<EdgeId> = k.edges().iter().copied().collect();
    k_edges.sort();

    for k_e in k_edges {
        let l_e = l.map_edge(k_e).ok_or_else(|| {
            CategoricalError::ConstructionFailed(format!(
                "l does not map K-edge {:?}",
                k_e
            ))
        })?;

        let g_e = m.map_edge(l_e).ok_or_else(|| {
            CategoricalError::ConstructionFailed(format!(
                "m does not map L-edge {:?}",
                l_e
            ))
        })?;

        edge_fibers
            .entry(g_e)
            .or_default()
            .entry(l_e)
            .or_default()
            .push(k_e);
    }

    for by_l in edge_fibers.values_mut() {
        for es in by_l.values_mut() {
            es.sort();
        }
    }

    for (&g_e, by_l) in &edge_fibers {
        if by_l.len() > 1 {
            let sizes: HashSet<usize> = by_l.values().map(|es| es.len()).collect();

            if sizes.len() > 1 {
                return Err(CategoricalError::IdentificationConditionViolated(format!(
                    "Incompatible edge fiber sizes over G-edge {:?}: {:?}",
                    g_e, sizes
                )));
            }
        }
    }

    let mut g_edge_keys: Vec<EdgeId> = edge_fibers.keys().copied().collect();
    g_edge_keys.sort();

    for g_e in g_edge_keys {
        let by_l = &edge_fibers[&g_e];

        let max_slots = by_l
            .values()
            .map(|es| es.len())
            .max()
            .unwrap_or(0);

        for slot in 0..max_slots {
            let rep_k_e = by_l
                .values()
                .find_map(|es| es.get(slot).copied())
                .ok_or_else(|| {
                    CategoricalError::ConstructionFailed(format!(
                        "No representative K-edge for G-edge {:?}, slot {}",
                        g_e, slot
                    ))
                })?;

            let k_swbs = k.get_sources_with_binding(rep_k_e).ok_or_else(|| {
                CategoricalError::ConstructionFailed(format!(
                    "K-edge {:?} has no sources-with-binding",
                    rep_k_e
                ))
            })?;

            let k_targets = k.get_targets(rep_k_e).ok_or_else(|| {
                CategoricalError::ConstructionFailed(format!(
                    "K-edge {:?} has no targets",
                    rep_k_e
                ))
            })?;

            let label = g.get_label(g_e).cloned();

            let new_swbs: Vec<SourceWithBinding> = k_swbs
                .iter()
                .map(|swb| {
                    let source = *k_to_c_nodes.get(&swb.source).ok_or_else(|| {
                        CategoricalError::ConstructionFailed(format!(
                            "K-edge {:?} source {:?} has no C image",
                            rep_k_e, swb.source
                        ))
                    })?;

                    let bound: Result<Vec<NodeId>, CategoricalError> = swb
                        .bound
                        .iter()
                        .map(|&b| {
                            k_to_c_nodes.get(&b).copied().ok_or_else(|| {
                                CategoricalError::ConstructionFailed(format!(
                                    "K-edge {:?} bound node {:?} has no C image",
                                    rep_k_e, b
                                ))
                            })
                        })
                        .collect();

                    Ok(SourceWithBinding {
                        source,
                        bound: bound?,
                    })
                })
                .collect::<Result<Vec<_>, CategoricalError>>()?;

            let new_targets: Vec<NodeId> = k_targets
                .iter()
                .map(|&t| {
                    k_to_c_nodes.get(&t).copied().ok_or_else(|| {
                        CategoricalError::ConstructionFailed(format!(
                            "K-edge {:?} target {:?} has no C image",
                            rep_k_e, t
                        ))
                    })
                })
                .collect::<Result<Vec<_>, CategoricalError>>()?;

            let c_e = complement
                .add_edge(new_swbs, new_targets, label)
                .map_err(|e| {
                    CategoricalError::ConstructionFailed(format!(
                        "Failed to add C-edge for G-edge {:?}, slot {}: {:?}",
                        g_e, slot, e
                    ))
                })?;

            g_slot_to_c_edge.insert((g_e, slot), c_e);
            c_to_g_edges.insert(c_e, g_e);
        }

        for es in by_l.values() {
            for (slot, &k_e) in es.iter().enumerate() {
                let c_e = g_slot_to_c_edge[&(g_e, slot)];
                k_to_c_edges.insert(k_e, c_e);
            }
        }
    }

    // ========================================================================
    // Add context edges: G-edges outside m(L)
    // ========================================================================

    let mut g_edges: Vec<EdgeId> = g.edges().iter().copied().collect();
    g_edges.sort();

    for g_e in g_edges {
        if deleted_edges.contains(&g_e) {
            continue;
        }

        if m_edge_image.contains(&g_e) {
            continue;
        }

        let swbs = g.get_sources_with_binding(g_e).ok_or_else(|| {
            CategoricalError::ConstructionFailed(format!(
                "G-edge {:?} has no sources-with-binding",
                g_e
            ))
        })?;

        let targets = g.get_targets(g_e).ok_or_else(|| {
            CategoricalError::ConstructionFailed(format!(
                "G-edge {:?} has no targets",
                g_e
            ))
        })?;

        let label = g.get_label(g_e).cloned();

        let new_swbs: Vec<SourceWithBinding> = swbs
            .iter()
            .map(|swb| {
                let source = g_slot_to_c_node
                    .get(&(swb.source, 0))
                    .copied()
                    .ok_or_else(|| {
                        CategoricalError::DanglingConditionViolated(format!(
                            "Context edge {:?} has source {:?}, but no C node slot 0 exists",
                            g_e, swb.source
                        ))
                    })?;

                let bound: Result<Vec<NodeId>, CategoricalError> = swb
                    .bound
                    .iter()
                    .map(|&b| {
                        g_slot_to_c_node
                            .get(&(b, 0))
                            .copied()
                            .ok_or_else(|| {
                                CategoricalError::DanglingConditionViolated(format!(
                                    "Context edge {:?} binds {:?}, but no C node slot 0 exists",
                                    g_e, b
                                ))
                            })
                    })
                    .collect();

                Ok(SourceWithBinding {
                    source,
                    bound: bound?,
                })
            })
            .collect::<Result<Vec<_>, CategoricalError>>()?;

        let new_targets: Vec<NodeId> = targets
            .iter()
            .map(|&t| {
                g_slot_to_c_node
                    .get(&(t, 0))
                    .copied()
                    .ok_or_else(|| {
                        CategoricalError::DanglingConditionViolated(format!(
                            "Context edge {:?} has target {:?}, but no C node slot 0 exists",
                            g_e, t
                        ))
                    })
            })
            .collect::<Result<Vec<_>, CategoricalError>>()?;

        let c_e = complement
            .add_edge(new_swbs, new_targets, label)
            .map_err(|e| {
                CategoricalError::ConstructionFailed(format!(
                    "Failed to add context edge {:?}: {:?}",
                    g_e, e
                ))
            })?;

        c_to_g_edges.insert(c_e, g_e);
    }

    // ========================================================================
    // Build morphisms K -> C and C -> G
    // ========================================================================

    let k_to_c = BHypMorphism::new(
        k.clone(),
        complement.clone(),
        k_to_c_nodes,
        k_to_c_edges,
    )?;

    let c_to_g = BHypMorphism::new(
        complement.clone(),
        g.clone(),
        c_to_g_nodes,
        c_to_g_edges,
    )?;

    Ok(PushoutComplementResult {
        complement,
        morphism_from_k: k_to_c,
        morphism_to_g: c_to_g,
    })
}

/// Compute the pushout complement of morphisms l: K -> L and m: L -> G
///
/// Given:
/// ```text
///     K ---l---> L
///     |          |
///     k          m
///     |          |
///     v          v
///     C -------> G
/// ```
///
/// We find C and morphisms k: K -> C and c: C -> G such that the square
/// is a pushout. C is essentially G with the "non-interface" parts of L removed.
///
/// The pushout complement exists iff the gluing conditions are satisfied:
/// 1. Identification condition: if m identifies two elements of L, they must both be in l(K)
/// 2. Dangling condition: no edge in G \ m(L) is incident to a node in m(L \ l(K))

// pub fn compute_pushout_complement(
//     l: &BHypMorphism, // l: K -> L
//     m: &BHypMorphism, // m: L -> G
// ) -> Result<PushoutComplementResult, CategoricalError> {
//     let k = &l.domain;
//     let l_graph = &l.codomain;
//     let g = &m.codomain;

//     // Compute the images
//     let l_node_image: HashSet<NodeId> = l.node_image(); // l(K) nodes in L
//     let l_edge_image: HashSet<EdgeId> = l.edge_image(); // l(K) edges in L

//     // m(L) in G
//     let m_node_image: HashSet<NodeId> = m.node_image();
//     let m_edge_image: HashSet<EdgeId> = m.edge_image();

//     // m(l(K)) in G - the "gluing interface"
//     let mlk_node_image: HashSet<NodeId> = l
//         .on_nodes
//         .values()
//         .filter_map(|&l_n| m.map_node(l_n))
//         .collect();
//     let mlk_edge_image: HashSet<EdgeId> = l
//         .on_edges
//         .values()
//         .filter_map(|&l_e| m.map_edge(l_e))
//         .collect();

//     // ========================================================================
//     // Check Identification Condition (modified for non-injective l)
//     // ========================================================================
//     // If m identifies two nodes of L, they must both be in l(K)
//     // AND l must identify them the same way (same preimages in K)
//     let l_nodes: Vec<_> = l_graph.nodes().iter().copied().collect();
//     for (i, &l1) in l_nodes.iter().enumerate() {
//         for &l2 in l_nodes.iter().skip(i + 1) {
//             if m.map_node(l1) == m.map_node(l2) {
//                 let l1_in_lk = l_node_image.contains(&l1);
//                 let l2_in_lk = l_node_image.contains(&l2);
//                 if !l1_in_lk || !l2_in_lk {
//                     return Err(CategoricalError::IdentificationConditionViolated(format!(
//                         "Nodes {:?} and {:?} identified by m but not both in l(K)",
//                         l1, l2
//                     )));
//                 }
//             }
//         }
//     }

//     // If m identifies two edges of L, they must both be in l(K)
//     let l_edges: Vec<_> = l_graph.edges().iter().copied().collect();
//     for (i, &e1) in l_edges.iter().enumerate() {
//         for &e2 in l_edges.iter().skip(i + 1) {
//             if m.map_edge(e1) == m.map_edge(e2) {
//                 let e1_in_lk = l_edge_image.contains(&e1);
//                 let e2_in_lk = l_edge_image.contains(&e2);
//                 if !e1_in_lk || !e2_in_lk {
//                     return Err(CategoricalError::IdentificationConditionViolated(format!(
//                         "Edges {:?} and {:?} identified by m but not both in l(K)",
//                         e1, e2
//                     )));
//                 }
//             }
//         }
//     }

//     // ========================================================================
//     // Check Dangling Condition
//     // ========================================================================
//     // Nodes in m(L \ l(K)) - these are "deleted" nodes
//     let deleted_nodes: HashSet<NodeId> = l_graph
//         .nodes()
//         .iter()
//         .filter(|&l_n| !l_node_image.contains(l_n))
//         .filter_map(|&l_n| m.map_node(l_n))
//         .collect();

//     // Edges in G \ m(L) - these are "context" edges that stay
//     for &g_e in g.edges() {
//         if m_edge_image.contains(&g_e) {
//             continue; // This edge is in m(L), skip
//         }

//         // This edge is in G \ m(L), check it doesn't touch deleted nodes
//         if let Some(swbs) = g.get_sources_with_binding(g_e) {
//             for swb in swbs {
//                 if deleted_nodes.contains(&swb.source) {
//                     return Err(CategoricalError::DanglingConditionViolated(format!(
//                         "Edge {:?} in G\\m(L) has source {:?} in m(L\\l(K))",
//                         g_e, swb.source
//                     )));
//                 }
//                 for &b in &swb.bound {
//                     if deleted_nodes.contains(&b) {
//                         return Err(CategoricalError::DanglingConditionViolated(format!(
//                             "Edge {:?} in G\\m(L) binds node {:?} in m(L\\l(K))",
//                             g_e, b
//                         )));
//                     }
//                 }
//             }
//         }

//         if let Some(targets) = g.get_targets(g_e) {
//             for t in targets {
//                 if deleted_nodes.contains(&t) {
//                     return Err(CategoricalError::DanglingConditionViolated(format!(
//                         "Edge {:?} in G\\m(L) has target {:?} in m(L\\l(K))",
//                         g_e, t
//                     )));
//                 }
//             }
//         }
//     }

//     // ========================================================================
//     // Construct C with proper handling of non-injective l
//     // ========================================================================
//     // 
//     // Key insight: When l identifies multiple K-nodes to the same L-node,
//     // we need multiple copies in C to ensure K -> C is injective.
//     //
//     // Strategy:
//     // 1. For each K-node, create a corresponding C-node
//     // 2. For G-nodes outside m(L), create one C-node (context, shared)
//     // 3. For edges, similar logic applies

//     let mut complement = BHyp::new();

//     // ========================================================================
//     // Build K -> C node mapping (one C-node per K-node)
//     // ========================================================================
//     let mut k_to_c_nodes: HashMap<NodeId, NodeId> = HashMap::new();
    
//     // Track which G-nodes are "duplicated" via K
//     // g_node -> list of C-nodes that correspond to it
//     let mut g_node_to_c_nodes: HashMap<NodeId, Vec<NodeId>> = HashMap::new();

//     let mut k_nodes: Vec<_> = k.nodes().iter().copied().collect();
//     k_nodes.sort();

//     for k_n in k_nodes {
//         let l_n = l.map_node(k_n).unwrap();
//         let g_n = m.map_node(l_n).unwrap();
        
//         let c_n = complement.add_node();
//         k_to_c_nodes.insert(k_n, c_n);
//         g_node_to_c_nodes.entry(g_n).or_insert_with(Vec::new).push(c_n);
//     }

//     // ========================================================================
//     // Add context nodes (G-nodes not in m(L))
//     // ========================================================================
//     let mut g_to_c_nodes: HashMap<NodeId, NodeId> = HashMap::new();

//     let mut g_nodes: Vec<_> = g.nodes().iter().copied().collect();
//     g_nodes.sort();

//     for g_n in g_nodes {
//         if !m_node_image.contains(&g_n) {
//             // Context node - not in m(L), keep as single node
//             let c_n = complement.add_node();
//             g_to_c_nodes.insert(g_n, c_n);
//             g_node_to_c_nodes.entry(g_n).or_insert_with(Vec::new).push(c_n);
//         }
//         // Nodes in m(L) \ m(l(K)) are "deleted" - don't add to C
//         // Nodes in m(l(K)) are already added via K above
//     }

//     // ========================================================================
//     // Build K -> C edge mapping (one C-edge per K-edge)
//     // ========================================================================
//     let mut k_to_c_edges: HashMap<EdgeId, EdgeId> = HashMap::new();
    
//     // Track which G-edges are "duplicated" via K
//     let mut g_edge_to_c_edges: HashMap<EdgeId, Vec<EdgeId>> = HashMap::new();

//     let mut k_edges: Vec<_> = k.edges().iter().copied().collect();
//     k_edges.sort();

//     for k_e in k_edges {
//         let l_e = l.map_edge(k_e).unwrap();
//         let g_e = m.map_edge(l_e).unwrap();
        
//         // Get the edge structure from G
//         let swbs = g.get_sources_with_binding(g_e).unwrap();
//         let targets = g.get_targets(g_e).unwrap();
//         let label = g.get_label(g_e).cloned();

//         // Map the incident nodes through K's mapping
//         // We need to find which C-nodes correspond to this K-edge's incident nodes
//         let k_swbs = k.get_sources_with_binding(k_e).unwrap();
//         let k_targets = k.get_targets(k_e).unwrap();

//         let new_swbs: Vec<SourceWithBinding> = k_swbs
//             .iter()
//             .map(|k_swb| SourceWithBinding {
//                 source: k_to_c_nodes[&k_swb.source],
//                 bound: k_swb.bound.iter().map(|&b| k_to_c_nodes[&b]).collect(),
//             })
//             .collect();

//         let new_targets: Vec<NodeId> = k_targets
//             .iter()
//             .map(|&t| k_to_c_nodes[&t])
//             .collect();

//         let c_e = complement.add_edge(new_swbs, new_targets, label).unwrap();
//         k_to_c_edges.insert(k_e, c_e);
//         g_edge_to_c_edges.entry(g_e).or_insert_with(Vec::new).push(c_e);
//     }

//     // ========================================================================
//     // Add context edges (G-edges not in m(L))
//     // ========================================================================
//     // These edges connect to nodes that are either:
//     // - Context nodes (single copy)
//     // - Interface nodes in m(l(K)) (possibly multiple copies)
//     //
//     // For context edges touching interface nodes, we need to decide which
//     // copy they attach to. The correct approach: each context edge attaches
//     // to exactly ONE of the copies (creating the "distributed" effect).

//     let mut g_edges: Vec<_> = g.edges().iter().copied().collect();
//     g_edges.sort();

//     // Build reverse mapping: for nodes in m(l(K)), find which K-nodes map to them
//     let mut g_to_k_nodes: HashMap<NodeId, Vec<NodeId>> = HashMap::new();
//     for (&k_n, _) in &k_to_c_nodes {
//         let l_n = l.map_node(k_n).unwrap();
//         let g_n = m.map_node(l_n).unwrap();
//         g_to_k_nodes.entry(g_n).or_insert_with(Vec::new).push(k_n);
//     }

//     // Track how many times we've used each interface node for context edges
//     let mut interface_node_usage: HashMap<NodeId, usize> = HashMap::new();

//     for g_e in g_edges {
//         if m_edge_image.contains(&g_e) {
//             continue; // Edge is in m(L), already handled via K
//         }

//         // This is a context edge
//         let swbs = g.get_sources_with_binding(g_e).unwrap();
//         let targets = g.get_targets(g_e).unwrap();
//         let label = g.get_label(g_e).cloned();

//         // Map incident nodes to C
//         // For interface nodes (in mlk_node_image), pick the appropriate copy
//         let new_swbs: Vec<SourceWithBinding> = swbs
//             .iter()
//             .map(|swb| {
//                 let c_source = resolve_g_node_to_c(
//                     swb.source,
//                     &mlk_node_image,
//                     &g_to_c_nodes,
//                     &g_to_k_nodes,
//                     &k_to_c_nodes,
//                     &mut interface_node_usage,
//                 );
//                 let c_bound: Vec<NodeId> = swb
//                     .bound
//                     .iter()
//                     .map(|&b| {
//                         resolve_g_node_to_c(
//                             b,
//                             &mlk_node_image,
//                             &g_to_c_nodes,
//                             &g_to_k_nodes,
//                             &k_to_c_nodes,
//                             &mut interface_node_usage,
//                         )
//                     })
//                     .collect();
//                 SourceWithBinding {
//                     source: c_source,
//                     bound: c_bound,
//                 }
//             })
//             .collect();

//         let new_targets: Vec<NodeId> = targets
//             .iter()
//             .map(|&t| {
//                 resolve_g_node_to_c(
//                     t,
//                     &mlk_node_image,
//                     &g_to_c_nodes,
//                     &g_to_k_nodes,
//                     &k_to_c_nodes,
//                     &mut interface_node_usage,
//                 )
//             })
//             .collect();

//         let c_e = complement.add_edge(new_swbs, new_targets, label).unwrap();
//         g_edge_to_c_edges.entry(g_e).or_insert_with(Vec::new).push(c_e);
//     }

//     // ========================================================================
//     // Build morphism c: C -> G
//     // ========================================================================
//     // This is no longer injective when l was non-injective
//     let mut c_to_g_nodes: HashMap<NodeId, NodeId> = HashMap::new();
//     let mut c_to_g_edges: HashMap<EdgeId, EdgeId> = HashMap::new();

//     for (&g_n, c_nodes) in &g_node_to_c_nodes {
//         for &c_n in c_nodes {
//             c_to_g_nodes.insert(c_n, g_n);
//         }
//     }

//     for (&g_e, c_edges) in &g_edge_to_c_edges {
//         for &c_e in c_edges {
//             c_to_g_edges.insert(c_e, g_e);
//         }
//     }

//     let k_to_c = BHypMorphism::new(k.clone(), complement.clone(), k_to_c_nodes, k_to_c_edges)?;

//     let c_to_g = BHypMorphism::new(complement.clone(), g.clone(), c_to_g_nodes, c_to_g_edges)?;

//     Ok(PushoutComplementResult {
//         complement,
//         morphism_from_k: k_to_c,
//         morphism_to_g: c_to_g,
//     })
// }

/// Helper function to resolve a G-node to the appropriate C-node
/// For context nodes: direct mapping
/// For interface nodes: round-robin among copies to distribute context edges
fn resolve_g_node_to_c(
    g_n: NodeId,
    mlk_node_image: &HashSet<NodeId>,
    g_to_c_nodes: &HashMap<NodeId, NodeId>,
    g_to_k_nodes: &HashMap<NodeId, Vec<NodeId>>,
    k_to_c_nodes: &HashMap<NodeId, NodeId>,
    interface_node_usage: &mut HashMap<NodeId, usize>,
) -> NodeId {
    if mlk_node_image.contains(&g_n) {
        // Interface node - pick one of the copies
        let k_nodes = &g_to_k_nodes[&g_n];
        let usage = interface_node_usage.entry(g_n).or_insert(0);
        let idx = *usage % k_nodes.len();
        *usage += 1;
        k_to_c_nodes[&k_nodes[idx]]
    } else {
        // Context node - direct mapping
        g_to_c_nodes[&g_n]
    }
}


/// double-pushout diagram
pub fn dpo(span: &Span, g: &BHyp, m: &BHypMorphism) -> 
    Result<Span, CategoricalError> {
    let pc = compute_pushout_complement(&span.to_l, m).unwrap();
    let pc = compute_pushout_complement(&span.to_l, m).unwrap();

println!("--- pushout complement boundary check ---");
for k_node in span.middle.nodes() {
    let l_node = span.to_l.map_node(*k_node);
    let g_node = l_node.and_then(|n| m.map_node(n));
    let d_node = pc.morphism_from_k.map_node(*k_node);

    println!(
        "K {:?} -> L {:?} -> G {:?}; K -> D {:?}",
        k_node, l_node, g_node, d_node
    );
}
    let result = compute_pushout(&span.to_r, &pc.morphism_from_k).unwrap();
    
    println!("--- final pushout relations ---");
for k_node in span.middle.nodes() {
    let r_node = span.to_r.map_node(*k_node);
    let d_node = pc.morphism_from_k.map_node(*k_node);

    let h_from_r = r_node.and_then(|n| result.morphism_from_b.map_node(n));
    let h_from_d = d_node.and_then(|n| result.morphism_from_c.map_node(n));

    println!(
        "K {:?}: R {:?} -> H {:?}; D {:?} -> H {:?}",
        k_node, r_node, h_from_r, d_node, h_from_d
    );
}

    Ok(Span {
        left : g.clone(),
        middle : pc.complement.clone(),
        right: result.pushout.clone(),
        to_l: pc.morphism_to_g.clone(),
        to_r: result.morphism_from_c.clone()
    })

}


/// coproduct = pushout from the initial object
pub fn compute_coproduct(
    b: &BHyp, // f: A -> B
    c: &BHyp, // g: A -> C
) -> Result<PushoutResult, CategoricalError> {
    let i = BHyp::new();

    let f = BHypMorphism::new(i.clone(), b.clone(), HashMap::new(), HashMap::new()).unwrap();

    let g = BHypMorphism::new(i.clone(), c.clone(), HashMap::new(), HashMap::new()).unwrap();

   let coproduct = compute_pushout(&f, &g);

   coproduct

}


/// Check if two BHyp instances are isomorphic
pub fn are_isomorphic(g1: &BHyp, g2: &BHyp) -> bool {
    if g1.nodes().len() != g2.nodes().len() || g1.edges().len() != g2.edges().len() {
        return false;
    }

    // Try to find an isomorphism (brute force for small graphs)
    // This is a simplified check - for larger graphs, more sophisticated algorithms would be needed

    let g1_nodes: Vec<NodeId> = g1.nodes().iter().copied().collect();
    let g2_nodes: Vec<NodeId> = g2.nodes().iter().copied().collect();

    if g1_nodes.is_empty() && g2_nodes.is_empty() {
        return g1.edges().is_empty() && g2.edges().is_empty();
    }

    // For small graphs, try all permutations
    fn try_isomorphism(
        g1: &BHyp,
        g2: &BHyp,
        g1_nodes: &[NodeId],
        g2_nodes: &[NodeId],
        node_map: &mut HashMap<NodeId, NodeId>,
        idx: usize,
        used: &mut HashSet<NodeId>,
    ) -> bool {
        if idx == g1_nodes.len() {
            // Check if this node mapping induces a valid edge mapping
            let mut edge_map: HashMap<EdgeId, EdgeId> = HashMap::new();

            for &e1 in g1.edges() {
                let mut found = false;
                for &e2 in g2.edges() {
                    if edge_map.values().any(|&e| e == e2) {
                        continue;
                    }

                    // Check compatibility
                    let swbs1 = g1.get_sources_with_binding(e1).unwrap();
                    let swbs2 = g2.get_sources_with_binding(e2).unwrap();
                    let targets1 = g1.get_targets(e1).unwrap();
                    let targets2 = g2.get_targets(e2).unwrap();

                    if swbs1.len() != swbs2.len() || targets1.len() != targets2.len() {
                        continue;
                    }

                    let mut compatible = true;

                    for (s1, s2) in swbs1.iter().zip(swbs2.iter()) {
                        if node_map[&s1.source] != s2.source {
                            compatible = false;
                            break;
                        }
                        if s1.bound.len() != s2.bound.len() {
                            compatible = false;
                            break;
                        }
                        for (b1, b2) in s1.bound.iter().zip(s2.bound.iter()) {
                            if node_map[b1] != *b2 {
                                compatible = false;
                                break;
                            }
                        }
                    }

                    if !compatible {
                        continue;
                    }

                    for (t1, t2) in targets1.iter().zip(targets2.iter()) {
                        if node_map[t1] != *t2 {
                            compatible = false;
                            break;
                        }
                    }

                    if !compatible {
                        continue;
                    }

                    // Check labels
                    if g1.get_label(e1) != g2.get_label(e2) {
                        continue;
                    }

                    edge_map.insert(e1, e2);
                    found = true;
                    break;
                }

                if !found {
                    return false;
                }
            }

            return true;
        }

        let n1 = g1_nodes[idx];
        for &n2 in g2_nodes {
            if used.contains(&n2) {
                continue;
            }

            node_map.insert(n1, n2);
            used.insert(n2);

            if try_isomorphism(g1, g2, g1_nodes, g2_nodes, node_map, idx + 1, used) {
                return true;
            }

            node_map.remove(&n1);
            used.remove(&n2);
        }

        false
    }

    let mut node_map = HashMap::new();
    let mut used = HashSet::new();
    try_isomorphism(g1, g2, &g1_nodes, &g2_nodes, &mut node_map, 0, &mut used)
}



// ============================================================================
// Tests
// ============================================================================



#[cfg(test)]
mod tests {
    use super::*;

    

    // ========================================================================
    // Basic Morphism Tests
    // ========================================================================

    #[test]
    fn test_morphism_creation_valid() {
        let mut g1 = BHyp::new();
        let n1 = g1.add_node();
        let n2 = g1.add_node();
        g1.add_edge(
            vec![SourceWithBinding {
                source: n1,
                bound: vec![],
            }],
            vec![n2],
            Some(Label::Symbol("f".to_string())),
        )
        .unwrap();

        let id = identity_morphism(&g1);
        assert_eq!(id.map_node(n1), Some(n1));
        assert_eq!(id.map_node(n2), Some(n2));
    }

    #[test]
    fn test_id_with_binding() {
        // Create a graph with binding: λx.f(x)
        let mut g = BHyp::new();
        let x = g.add_node(); // bound variable
        let fx = g.add_node();
        let out = g.add_node(); // output

        g.add_edge(
            vec![SourceWithBinding {
                source: fx,
                bound: vec![x],
            }],
            vec![out],
            Some(Label::Symbol("λ".to_string())),
        )
        .unwrap();

        g.add_edge(
            vec![SourceWithBinding {
                source: x,
                bound: vec![],
            }],
            vec![fx],
            Some(Label::Symbol("f".to_string())),
        )
        .unwrap();

        let id = identity_morphism(&g);
        assert_eq!(id.map_node(x), Some(x));
        assert_eq!(id.map_node(fx), Some(fx));
        assert_eq!(id.map_node(out), Some(out));
    }

    #[test]
    fn test_morphism_with_binding() {
        // map lambda x. [parallel f(x)] to lambda x.f(x)
        let mut g = BHyp::new();
        let x = g.add_node(); // bound variable
        let fx = g.add_node();
        let out = g.add_node(); // output

        let lamg = g.add_edge(
            vec![SourceWithBinding {
                source: fx,
                bound: vec![x],
            }],
            vec![out],
            Some(Label::Symbol("λ".to_string())),
        )
        .unwrap();

        let f1 = g.add_edge(
            vec![SourceWithBinding {
                source: x,
                bound: vec![],
            }],
            vec![fx],
            Some(Label::Symbol("f".to_string())),
        )
        .unwrap();

        let f2 = g.add_edge(
            vec![SourceWithBinding {
                source: x,
                bound: vec![],
            }],
            vec![fx],
            Some(Label::Symbol("f".to_string())),
        )
        .unwrap();


        let mut gg = BHyp::new();
        let y = gg.add_node(); // bound variable
        let fy = gg.add_node();
        let outy = gg.add_node(); // output

        let lamgg = gg.add_edge(
            vec![SourceWithBinding {
                source: fy,
                bound: vec![y],
            }],
            vec![outy],
            Some(Label::Symbol("λ".to_string())),
        )
        .unwrap();

        let f = gg.add_edge(
            vec![SourceWithBinding {
                source: y,
                bound: vec![],
            }],
            vec![fy],
            Some(Label::Symbol("f".to_string())),
        )
        .unwrap();

 

        let map = BHypMorphism::new(
            g.clone(),
            gg.clone(),
             [(x, y), (fx, fy), (out, outy)].into_iter().collect(),
            [(lamg, lamgg), (f1, f), (f2, f)].into_iter().collect()
        )
        .unwrap();
        
        
        assert_eq!(map.map_node(x), Some(y));
        assert_eq!(map.map_node(fx), Some(fy));
        assert_eq!(map.map_node(out), Some(outy));
    }

    #[test]
    fn test_morphism_composition() {

        // two parallel f edges
        let mut g1 = BHyp::new();
        let v1 = g1.add_node();
        let v2 = g1.add_node();
        let v3 = g1.add_node();
        let v4 = g1.add_node();

        let f1 = g1.add_edge(
            vec![SourceWithBinding {
                source: v1,
                bound: vec![],
            }],
            vec![v2],
            Some(Label::Symbol("f".to_string())),
        )
        .unwrap();

        let f2 = g1.add_edge(
            vec![SourceWithBinding {
                source: v3,
                bound: vec![],
            }],
            vec![v4],
            Some(Label::Symbol("f".to_string())),
        )
        .unwrap();

        
        // two f edges with shared source
        let mut g2 = BHyp::new();
        let u1 = g2.add_node();
        let u2 = g2.add_node();
        let u4 = g2.add_node();

        let f3 = g2.add_edge(
            vec![SourceWithBinding {
                source: u1,
                bound: vec![],
            }],
            vec![u2],
            Some(Label::Symbol("f".to_string())),
        )
        .unwrap();

        let f4 = g2.add_edge(
            vec![SourceWithBinding {
                source: u1,
                bound: vec![],
            }],
            vec![u4],
            Some(Label::Symbol("f".to_string())),
        )
        .unwrap();

        // one f edge
        let mut g3 = BHyp::new();
        let x1 = g3.add_node();
        let x2 = g3.add_node();
        let f5 = g3.add_edge(
            vec![SourceWithBinding {
                source: x1,
                bound: vec![],
            }],
            vec![x2],
            Some(Label::Symbol("f".to_string())),
        )
        .unwrap();



        let h1 = BHypMorphism::new(
            g1.clone(),
            g2.clone(),
            [(v1, u1), (v2, u2), (v3, u1), (v4, u4)].into_iter().collect(),
            [(f1, f3), (f2, f4)].into_iter().collect()
        )
        .unwrap();

       let h2 = BHypMorphism::new(
            g2.clone(),
            g3.clone(),
            [(u1, x1), (u2, x2), (u4, x2)].into_iter().collect(),
            [(f3, f5), (f4, f5)].into_iter().collect()
        )
        .unwrap();
        
        let composed = h2.compose(&h1).unwrap();

        assert_eq!(composed.map_node(v2), Some(x2));
        assert_eq!(composed.map_node(v4), Some(x2));
        assert_eq!(composed.map_node(v1), Some(x1));
        assert_eq!(composed.map_node(v1), Some(x1));
        assert_eq!(composed.map_edge(f1), Some(f5));
        assert_eq!(composed.map_edge(f2), Some(f5));

       
    }

    // ========================================================================
    // Pushout Tests - First Order (No Binding)
    // ========================================================================

    #[test]
    fn test_pushout_disjoint_union() {
        // When K is empty, pushout should be disjoint union
        let k = BHyp::new();

        let mut b = BHyp::new();
        let b1 = b.add_node();
        let b2 = b.add_node();
        b.add_edge(
            vec![SourceWithBinding {
                source: b1,
                bound: vec![],
            }],
            vec![b2],
            Some(Label::Symbol("f".to_string())),
        )
        .unwrap();

        let mut c = BHyp::new();
        let c1 = c.add_node();
        let c2 = c.add_node();
        c.add_edge(
            vec![SourceWithBinding {
                source: c1,
                bound: vec![],
            }],
            vec![c2],
            Some(Label::Symbol("g".to_string())),
        )
        .unwrap();

        let f = BHypMorphism::new(k.clone(), b.clone(), HashMap::new(), HashMap::new()).unwrap();

        let g = BHypMorphism::new(k.clone(), c.clone(), HashMap::new(), HashMap::new()).unwrap();

        let result = compute_pushout(&f, &g).unwrap();

        // Pushout should have 4 nodes and 2 edges
        let mut expected = BHyp::new();
        let b1p = expected.add_node();
        let b2p = expected.add_node();
        let c1p = expected.add_node();
        let c2p = expected.add_node();

        expected.add_edge(
            vec![SourceWithBinding {
                source: b1p,
                bound: vec![],
            }],
            vec![b2p],
            Some(Label::Symbol("f".to_string())),
        )
        .unwrap();
        
        
        expected.add_edge(
            vec![SourceWithBinding {
                source: c1p,
                bound: vec![],
            }],
            vec![c2p],
            Some(Label::Symbol("g".to_string())),
        )
        .unwrap();

        assert_eq!(result.pushout.nodes().len(), 4);
        assert_eq!(result.pushout.edges().len(), 2);

        assert!(are_isomorphic(&result.pushout, &expected));

    }

    #[test]
    fn test_pushout_with_shared_node() {
        // K has one node, mapped to single nodes in B and C
        let mut k = BHyp::new();
        let k1 = k.add_node();

        let mut b = BHyp::new();
        let b1 = b.add_node();
        let b2 = b.add_node();
        b.add_edge(
            vec![SourceWithBinding {
                source: b1,
                bound: vec![],
            }],
            vec![b2],
            Some(Label::Symbol("f".to_string())),
        )
        .unwrap();

        let mut c = BHyp::new();
        let c1 = c.add_node();
        let c2 = c.add_node();
        c.add_edge(
            vec![SourceWithBinding {
                source: c1,
                bound: vec![],
            }],
            vec![c2],
            Some(Label::Symbol("g".to_string())),
        )
        .unwrap();

        // f maps k1 -> b1
        let f = BHypMorphism::new(
            k.clone(),
            b.clone(),
            [(k1, b1)].into_iter().collect(),
            HashMap::new(),
        )
        .unwrap();

        // g maps k1 -> c2
        let g = BHypMorphism::new(
            k.clone(),
            c.clone(),
            [(k1, c2)].into_iter().collect(),
            HashMap::new(),
        )
        .unwrap();

        let result = compute_pushout(&f, &g).unwrap();

        // Pushout should have 3 nodes (b1~c2 merged) and 2 edges -composition
        assert_eq!(result.pushout.nodes().len(), 3);
        assert_eq!(result.pushout.edges().len(), 2);

        // Check that both morphisms map k1's images to the same node
        let b1_in_d = result.morphism_from_b.map_node(b1).unwrap();
        let c2_in_d = result.morphism_from_c.map_node(c2).unwrap();
        assert_eq!(b1_in_d, c2_in_d);
    }

    #[test]
    fn test_pushout_with_shared_edge() {
        // K has one edge, mapped to edges in B and C
        let mut k = BHyp::new();
        let k1 = k.add_node();
        let k2 = k.add_node();
        let k_e = k
            .add_edge(
                vec![SourceWithBinding {
                    source: k1,
                    bound: vec![],
                }],
                vec![k2],
                Some(Label::Symbol("h".to_string())),
            )
            .unwrap();

        let mut b = BHyp::new();
        let b1 = b.add_node();
        let b2 = b.add_node();
        let b3 = b.add_node();
        let b_e1 = b
            .add_edge(
                vec![SourceWithBinding {
                    source: b1,
                    bound: vec![],
                }],
                vec![b2],
                Some(Label::Symbol("h".to_string())),
            )
            .unwrap();
        b.add_edge(
            vec![SourceWithBinding {
                source: b2,
                bound: vec![],
            }],
            vec![b3],
            Some(Label::Symbol("f".to_string())),
        )
        .unwrap();

        let mut c = BHyp::new();
        let c1 = c.add_node();
        let c2 = c.add_node();
        let c3 = c.add_node();
        let c_e1 = c
            .add_edge(
                vec![SourceWithBinding {
                    source: c1,
                    bound: vec![],
                }],
                vec![c2],
                Some(Label::Symbol("h".to_string())),
            )
            .unwrap();
        c.add_edge(
            vec![SourceWithBinding {
                source: c2,
                bound: vec![],
            }],
            vec![c3],
            Some(Label::Symbol("g".to_string())),
        )
        .unwrap();

        let f = BHypMorphism::new(
            k.clone(),
            b.clone(),
            [(k1, b1), (k2, b2)].into_iter().collect(),
            [(k_e, b_e1)].into_iter().collect(),
        )
        .unwrap();

        let g = BHypMorphism::new(
            k.clone(),
            c.clone(),
            [(k1, c1), (k2, c2)].into_iter().collect(),
            [(k_e, c_e1)].into_iter().collect(),
        )
        .unwrap();

        let result = compute_pushout(&f, &g).unwrap();

        // Pushout should have 4 nodes (k1~b1~c1, k2~b2~c2, b3, c3) and 3 edges (h merged, f, g)
        assert_eq!(result.pushout.nodes().len(), 4);
        assert_eq!(result.pushout.edges().len(), 3);

        let mut po = BHyp::new();
        let v1 = po.add_node();
        let v2 = po.add_node();
        let v3 = po.add_node();
        let v4 = po.add_node();
        po.add_edge(
            vec![SourceWithBinding {
                source: v1,
                bound: vec![],
            }],
            vec![v2],
            Some(Label::Symbol("h".to_string())),
        )
        .unwrap();
        po.add_edge(
            vec![SourceWithBinding {
                source: v2,
                bound: vec![],
            }],
            vec![v3],
            Some(Label::Symbol("f".to_string())),
        )
        .unwrap();
        po.add_edge(
            vec![SourceWithBinding {
                source: v2,
                bound: vec![],
            }],
            vec![v4],
            Some(Label::Symbol("g".to_string())),
        )
        .unwrap();

        assert!(are_isomorphic(&result.pushout, &po));
            
        
    }

    // ========================================================================
    // Pushout Tests - With Binding
    // ========================================================================

    #[test]
    fn test_pushout_with_binding() {

        // lambda body insertion
        let mut k = BHyp::new();
        let k1 = k.add_node();
        let k2 = k.add_node();

        // L: f(x)
        let mut b = BHyp::new();
        let b_x = b.add_node();
        let b_out = b.add_node();
        b.add_edge(
            vec![SourceWithBinding {
                source: b_x,
                bound: vec![],
            }],
            vec![b_out],
            Some(Label::Symbol("f".to_string())),
        )
        .unwrap();

        // C: λy.[]y
        let mut c = BHyp::new();
        let c_y = c.add_node();
        let c_out = c.add_node();
        let c_in = c.add_node();
        c.add_edge(
            vec![SourceWithBinding {
                source: c_in,
                bound: vec![c_y],
            }],
            vec![c_out],
            Some(Label::Symbol("λ".to_string())),
        )
        .unwrap();

        let f = 
        BHypMorphism::new(
            k.clone(), 
            b.clone(), 
            [(k1, b_x), (k2, b_out)].into_iter().collect(),
            HashMap::new(),
        ).unwrap();

        let g = BHypMorphism::new(
            k.clone(), 
            c.clone(), 
            [(k1, c_y), (k2, c_in)].into_iter().collect(), 
            HashMap::new()
        ).unwrap();

        let result = compute_pushout(&f, &g).unwrap();

        // result should be λy.f(y)
        assert_eq!(result.pushout.nodes().len(), 3);
        assert_eq!(result.pushout.edges().len(), 2);

        let mut gg = BHyp::new();
        let g_y = gg.add_node();
        let g_out = gg.add_node();
        let g_in = gg.add_node();

        gg.add_edge(
            vec![SourceWithBinding {
                source: g_in,
                bound: vec![g_y],
            }],
            vec![g_out],
            Some(Label::Symbol("λ".to_string())),
        )
        .unwrap();

        gg.add_edge(
            vec![SourceWithBinding {
                source: g_y,
                bound: vec![],
            }],
            vec![g_in],
            Some(Label::Symbol("f".to_string())),
        )
        .unwrap();

        

        assert!(are_isomorphic(&result.pushout, &gg));

    }


    

    // // ========================================================================
    // // Pullback Tests
    // // ========================================================================

    // #[test]
    // fn test_pullback_basic() {
    //     // Create a simple diamond with one node in D
    //     let mut d = BHyp::new();
    //     let d1 = d.add_node();

    //     let mut b = BHyp::new();
    //     let b1 = b.add_node();

    //     let mut c = BHyp::new();
    //     let c1 = c.add_node();

    //     let f = BHypMorphism::new(
    //         b.clone(),
    //         d.clone(),
    //         [(b1, d1)].into_iter().collect(),
    //         HashMap::new(),
    //     )
    //     .unwrap();

    //     let g = BHypMorphism::new(
    //         c.clone(),
    //         d.clone(),
    //         [(c1, d1)].into_iter().collect(),
    //         HashMap::new(),
    //     )
    //     .unwrap();

    //     let result = compute_pullback(&f, &g).unwrap();

    //     // Pullback should have 1 node (the pair (b1, c1))
    //     assert_eq!(result.pullback.nodes().len(), 1);
    //     assert_eq!(result.pullback.edges().len(), 0);
    // }

    // #[test]
    // fn test_pullback_multiple_preimages() {
    //     // D has one node, B has two nodes mapping to it, C has one
    //     let mut d = BHyp::new();
    //     let d1 = d.add_node();

    //     let mut b = BHyp::new();
    //     let b1 = b.add_node();
    //     let b2 = b.add_node();

    //     let mut c = BHyp::new();
    //     let c1 = c.add_node();

    //     let f = BHypMorphism::new(
    //         b.clone(),
    //         d.clone(),
    //         [(b1, d1), (b2, d1)].into_iter().collect(),
    //         HashMap::new(),
    //     )
    //     .unwrap();

    //     let g = BHypMorphism::new(
    //         c.clone(),
    //         d.clone(),
    //         [(c1, d1)].into_iter().collect(),
    //         HashMap::new(),
    //     )
    //     .unwrap();

    //     let result = compute_pullback(&f, &g).unwrap();

    //     // Pullback should have 2 nodes: (b1, c1) and (b2, c1)
    //     assert_eq!(result.pullback.nodes().len(), 2);
    // }

    // #[test]
    // fn test_pullback_with_binding() {
    //     // D has a lambda edge
    //     let mut d = BHyp::new();
    //     let d_x = d.add_node();
    //     let d_out = d.add_node();
    //     let d_e = d
    //         .add_edge(
    //             vec![SourceWithBinding {
    //                 source: d_x,
    //                 bound: vec![d_x],
    //             }],
    //             vec![d_out],
    //             Some(Label::Symbol("λ".to_string())),
    //         )
    //         .unwrap();

    //     // B and C are copies of D
    //     let mut b = BHyp::new();
    //     let b_x = b.add_node();
    //     let b_out = b.add_node();
    //     let b_e = b
    //         .add_edge(
    //             vec![SourceWithBinding {
    //                 source: b_x,
    //                 bound: vec![b_x],
    //             }],
    //             vec![b_out],
    //             Some(Label::Symbol("λ".to_string())),
    //         )
    //         .unwrap();

    //     let mut c = BHyp::new();
    //     let c_x = c.add_node();
    //     let c_out = c.add_node();
    //     let c_e = c
    //         .add_edge(
    //             vec![SourceWithBinding {
    //                 source: c_x,
    //                 bound: vec![c_x],
    //             }],
    //             vec![c_out],
    //             Some(Label::Symbol("λ".to_string())),
    //         )
    //         .unwrap();

    //     let f = BHypMorphism::new(
    //         b.clone(),
    //         d.clone(),
    //         [(b_x, d_x), (b_out, d_out)].into_iter().collect(),
    //         [(b_e, d_e)].into_iter().collect(),
    //     )
    //     .unwrap();

    //     let g = BHypMorphism::new(
    //         c.clone(),
    //         d.clone(),
    //         [(c_x, d_x), (c_out, d_out)].into_iter().collect(),
    //         [(c_e, d_e)].into_iter().collect(),
    //     )
    //     .unwrap();

    //     let result = compute_pullback(&f, &g).unwrap();

    //     // Pullback should have 2 nodes and 1 edge (matching pairs)
    //     assert_eq!(result.pullback.nodes().len(), 2);
    //     assert_eq!(result.pullback.edges().len(), 1);

    //     // Check the edge has correct binding structure
    //     let p_edges: Vec<_> = result.pullback.edges().iter().collect();
    //     let p_e = *p_edges[0];
    //     let swbs = result.pullback.get_sources_with_binding(p_e).unwrap();
    //     assert_eq!(swbs.len(), 1);
    //     assert_eq!(swbs[0].bound.len(), 1);
    //     // The bound variable should be the source itself (λx.x structure)
    //     assert_eq!(swbs[0].source, swbs[0].bound[0]);
    // }

    // // ========================================================================
    // // Pushout Complement Tests - First Order
    // // ========================================================================

    // #[test]
    // fn test_pushout_complement_simple_deletion() {
    //     // Simple deletion: L has an edge, K is interface, G = L
    //     // C should be just the nodes without the edge

    //     let mut k = BHyp::new();
    //     let k1 = k.add_node();
    //     let k2 = k.add_node();

    //     let mut l = BHyp::new();
    //     let l1 = l.add_node();
    //     let l2 = l.add_node();
    //     let l_e = l
    //         .add_edge(
    //             vec![SourceWithBinding {
    //                 source: l1,
    //                 bound: vec![],
    //             }],
    //             vec![l2],
    //             Some(Label::Symbol("f".to_string())),
    //         )
    //         .unwrap();

    //     // G = L (identity embedding)
    //     let g = l.clone();

    //     let l_morph =
    //         BHypMorphism::new(k.clone(), l.clone(), 
    //         [(k1, l1), (k2, l2)].into_iter().collect(), 
    //         HashMap::new()).unwrap();

    //     let m = BHypMorphism::new(
    //         l.clone(),
    //         g.clone(),
    //         [(l1, l1), (l2, l2)].into_iter().collect(),
    //         [(l_e, l_e)].into_iter().collect(),
    //     )
    //     .unwrap();

    //     let result = compute_pushout_complement(&l_morph, &m).unwrap();

    //     // C should have 2 nodes but no edges
    //     assert_eq!(result.complement.nodes().len(), 2);
    //     assert_eq!(result.complement.edges().len(), 0);
    // }

    // #[test]
    // fn test_pushout_complement_preserves_interface() {
    //     // K has one node, L has that node plus an edge to delete
    //     // C should preserve the K node

    //     let mut k = BHyp::new();
    //     let k1 = k.add_node();

    //     let mut l = BHyp::new();
    //     let l1 = l.add_node(); // interface node
    //     let l2 = l.add_node(); // to be deleted
    //     let l_e = l
    //         .add_edge(
    //             vec![SourceWithBinding {
    //                 source: l1,
    //                 bound: vec![],
    //             }],
    //             vec![l2],
    //             Some(Label::Symbol("f".to_string())),
    //         )
    //         .unwrap();

    //     let mut g = BHyp::new();
    //     let g1 = g.add_node();
    //     let g2 = g.add_node();
    //     let g3 = g.add_node(); // extra context node
    //     let g_e = g
    //         .add_edge(
    //             vec![SourceWithBinding {
    //                 source: g1,
    //                 bound: vec![],
    //             }],
    //             vec![g2],
    //             Some(Label::Symbol("f".to_string())),
    //         )
    //         .unwrap();
    //     // Context edge that should be preserved
    //     g.add_edge(
    //         vec![SourceWithBinding {
    //             source: g1,
    //             bound: vec![],
    //         }],
    //         vec![g3],
    //         Some(Label::Symbol("context".to_string())),
    //     )
    //     .unwrap();

    //     let l_morph = BHypMorphism::new(
    //         k.clone(),
    //         l.clone(),
    //         [(k1, l1)].into_iter().collect(),
    //         HashMap::new(),
    //     )
    //     .unwrap();

    //     let m = BHypMorphism::new(
    //         l.clone(),
    //         g.clone(),
    //         [(l1, g1), (l2, g2)].into_iter().collect(),
    //         [(l_e, g_e)].into_iter().collect(),
    //     )
    //     .unwrap();

    //     let result = compute_pushout_complement(&l_morph, &m).unwrap();

    //     // C should have 2 nodes (g1 preserved, g2 deleted, g3 context) and 1 edge (context)
    //     assert_eq!(result.complement.nodes().len(), 2);
    //     assert_eq!(result.complement.edges().len(), 1);

    //     // Check that k1 is mapped correctly
    //     let k1_in_c = result.morphism_from_k.map_node(k1).unwrap();
    //     let k1_in_g = result.morphism_to_g.map_node(k1_in_c).unwrap();
    //     assert_eq!(k1_in_g, g1);
    // }

    // #[test]
    // fn test_pushout_complement_dangling_condition_violated() {
    //     // Create a situation where dangling condition is violated
    //     // K is empty, L has one node, but G has an edge connected to that node

    //     let k = BHyp::new();

    //     let mut l = BHyp::new();
    //     let l1 = l.add_node();

    //     let mut g = BHyp::new();
    //     let g1 = g.add_node();
    //     let g2 = g.add_node();
    //     g.add_edge(
    //         vec![SourceWithBinding {
    //             source: g1,
    //             bound: vec![],
    //         }],
    //         vec![g2],
    //         Some(Label::Symbol("f".to_string())),
    //     )
    //     .unwrap();

    //     let l_morph =
    //         BHypMorphism::new(k.clone(), l.clone(), HashMap::new(), HashMap::new()).unwrap();

    //     let m = BHypMorphism::new(
    //         l.clone(),
    //         g.clone(),
    //         [(l1, g1)].into_iter().collect(),
    //         HashMap::new(),
    //     )
    //     .unwrap();

    //     let result = compute_pushout_complement(&l_morph, &m);
    //     assert!(matches!(
    //         result,
    //         Err(CategoricalError::DanglingConditionViolated(_))
    //     ));
    // }

    // #[test]
    // fn test_pushout_complement_identification_condition_violated() {
    //     // m identifies two nodes of L, but only one is in l(K)

    //     let mut k = BHyp::new();
    //     let k1 = k.add_node();

    //     let mut l = BHyp::new();
    //     let l1 = l.add_node();
    //     let l2 = l.add_node(); // not in l(K) but will be identified with l1

    //     let mut g = BHyp::new();
    //     let g1 = g.add_node(); // l1 and l2 both map here

    //     let l_morph = BHypMorphism::new(
    //         k.clone(),
    //         l.clone(),
    //         [(k1, l1)].into_iter().collect(),
    //         HashMap::new(),
    //     )
    //     .unwrap();

    //     let m = BHypMorphism::new(
    //         l.clone(),
    //         g.clone(),
    //         [(l1, g1), (l2, g1)].into_iter().collect(), // identifies l1 and l2
    //         HashMap::new(),
    //     )
    //     .unwrap();

    //     let result = compute_pushout_complement(&l_morph, &m);
    //     assert!(matches!(
    //         result,
    //         Err(CategoricalError::IdentificationConditionViolated(_))
    //     ));
    // }

    // ========================================================================
    // Pushout Complement Tests - With Binding
    // ========================================================================

    #[test]
    fn test_pushout_complement_delete_body()
    {
        // lambda body insertion
        let mut k = BHyp::new();
        let k1 = k.add_node();
        let k2 = k.add_node();

        // L: f(x)
        let mut b = BHyp::new();
        let b_x = b.add_node();
        let b_out = b.add_node();
        let b_f = b.add_edge(
            vec![SourceWithBinding {
                source: b_x,
                bound: vec![],
            }],
            vec![b_out],
            Some(Label::Symbol("f".to_string())),
        )
        .unwrap();


        let mut gg = BHyp::new();
        let g_y = gg.add_node();
        let g_out = gg.add_node();
        let g_in = gg.add_node();

        gg.add_edge(
            vec![SourceWithBinding {
                source: g_in,
                bound: vec![g_y],
            }],
            vec![g_out],
            Some(Label::Symbol("λ".to_string())),
        )
        .unwrap();

        let g_f = gg.add_edge(
            vec![SourceWithBinding {
                source: g_y,
                bound: vec![],
            }],
            vec![g_in],
            Some(Label::Symbol("f".to_string())),
        )
        .unwrap();



        let f = 
        BHypMorphism::new(
            k.clone(), 
            b.clone(), 
            [(k1, b_x), (k2, b_out)].into_iter().collect(),
            HashMap::new(),
        ).unwrap();

        let g = BHypMorphism::new(
            b.clone(), 
            gg.clone(), 
            [(b_x, g_y), (b_out, g_in)].into_iter().collect(), 
            [(b_f, g_f)].into_iter().collect()
        ).unwrap();

        let result = compute_pushout_complement(&f, &g).unwrap();

        // result should be λy.[](y)
        assert_eq!(result.complement.nodes().len(), 3);
        assert_eq!(result.complement.edges().len(), 1);


        // C: λy.[]y
        let mut c = BHyp::new();
        let c_y = c.add_node();
        let c_out = c.add_node();
        let c_in = c.add_node();
        c.add_edge(
            vec![SourceWithBinding {
                source: c_in,
                bound: vec![c_y],
            }],
            vec![c_out],
            Some(Label::Symbol("λ".to_string())),
        )
        .unwrap();
        

        assert!(are_isomorphic(&result.complement, &c));
    }

    // #[test]
    // fn test_pushout_complement_delete_lambda() {
    //     // Delete a lambda edge, keeping the nodes
    //     // K: just two nodes (interface)
    //     // L: two nodes plus lambda edge
    //     // G = L

    //     let mut k = BHyp::new();
    //     let k_x = k.add_node();
    //     let k_out = k.add_node();

    //     let mut l = BHyp::new();
    //     let l_x = l.add_node();
    //     let l_out = l.add_node();
    //     let l_e = l
    //         .add_edge(
    //             vec![SourceWithBinding {
    //                 source: l_x,
    //                 bound: vec![l_x],
    //             }],
    //             vec![l_out],
    //             Some(Label::Symbol("λ".to_string())),
    //         )
    //         .unwrap();

    //     let g = l.clone();

    //     let l_morph = BHypMorphism::new(
    //         k.clone(),
    //         l.clone(),
    //         [(k_x, l_x), (k_out, l_out)].into_iter().collect(),
    //         HashMap::new(),
    //     )
    //     .unwrap();

    //     let m = BHypMorphism::new(
    //         l.clone(),
    //         g.clone(),
    //         [(l_x, l_x), (l_out, l_out)].into_iter().collect(),
    //         [(l_e, l_e)].into_iter().collect(),
    //     )
    //     .unwrap();

    //     let result = compute_pushout_complement(&l_morph, &m).unwrap();

    //     // C should have 2 nodes and 0 edges
    //     assert_eq!(result.complement.nodes().len(), 2);
    //     assert_eq!(result.complement.edges().len(), 0);
    // }

    // #[test]
    // fn test_pushout_complement_dangling_binding() {
    //     // Dangling condition violated through binding
    //     // Try to delete a node that is bound by a context edge

    //     let k = BHyp::new();

    //     let mut l = BHyp::new();
    //     let l_x = l.add_node(); // node to be deleted

    //     let mut g = BHyp::new();
    //     let g_x = g.add_node();
    //     let g_body = g.add_node();
    //     let g_out = g.add_node();
    //     // Lambda binds g_x
    //     g.add_edge(
    //         vec![SourceWithBinding {
    //             source: g_body,
    //             bound: vec![g_x],
    //         }],
    //         vec![g_out],
    //         Some(Label::Symbol("λ".to_string())),
    //     )
    //     .unwrap();

    //     let l_morph =
    //         BHypMorphism::new(k.clone(), l.clone(), HashMap::new(), HashMap::new()).unwrap();

    //     let m = BHypMorphism::new(
    //         l.clone(),
    //         g.clone(),
    //         [(l_x, g_x)].into_iter().collect(),
    //         HashMap::new(),
    //     )
    //     .unwrap();

    //     let result = compute_pushout_complement(&l_morph, &m);
    //     assert!(matches!(
    //         result,
    //         Err(CategoricalError::DanglingConditionViolated(_))
    //     ));
    // }


    // fn test_pushout_complement_roundtrip() {
    //     // Verify: PO of PC gives back original G
    //     // K -> L -> G gives PC = C
    //     // Then K -> C and K -> L should pushout to G
    
    //     let mut k = BHyp::new();
    //     let k_node = k.add_node();
    //     let k1 = k.add_node();

    //     let mut l = BHyp::new();
    //     let l_node1 = l.add_node();
    //     let l_node2 = l.add_node();
    //     let l1 = l.add_node(); // interface node
    //     let l2 = l.add_node(); // to be deleted
    //     let l_e = l
    //         .add_edge(
    //             vec![SourceWithBinding {
    //                 source: l1,
    //                 bound: vec![],
    //             }],
    //             vec![l2],
    //             Some(Label::Symbol("f".to_string())),
    //         )
    //         .unwrap();

    //     let mut g = BHyp::new();
    //     let g_node1 = g.add_node();
    //     let g_node2 = g.add_node();
    //     let g_node3 = g.add_node();
    //     let g1 = g.add_node();
    //     let g2 = g.add_node();
    //     let g3 = g.add_node(); // extra context node
    //     let g_e = g
    //         .add_edge(
    //             vec![SourceWithBinding {
    //                 source: g1,
    //                 bound: vec![],
    //             }],
    //             vec![g2],
    //             Some(Label::Symbol("f".to_string())),
    //         )
    //         .unwrap();
    //     // Context edge that should be preserved
    //     g.add_edge(
    //         vec![SourceWithBinding {
    //             source: g1,
    //             bound: vec![],
    //         }],
    //         vec![g3],
    //         Some(Label::Symbol("context".to_string())),
    //     )
    //     .unwrap();

    //     // K -> L: k_node maps to l_node1
    //     let l_morph = BHypMorphism::new(
    //         k.clone(),
    //         l.clone(),
    //         [(k_node, l_node1)].into_iter().collect(),
    //         [(k1, l1)].into_iter().collect(),
    //         HashMap::new(),
    //     )
    //     .unwrap();

    //     // L -> G: l_node1 -> g_node1, l_node2 -> g_node2
    //     let m_morph = BHypMorphism::new(
    //         l.clone(),
    //         g.clone(),
    //         [(l_node1, g_node1), (l_node2, g_node2)].into_iter().collect(),
    //         HashMap::new(),
    //         [(l1, g1), (l2, g2)].into_iter().collect(),
    //         [(l_e, g_e)].into_iter().collect(),
    //     )
    //     .unwrap();

    //     let pc_result = compute_pushout_complement(&l_morph, &m_morph).unwrap();
    //     let result = compute_pushout_complement(&l_morph, &m).unwrap();

    //     // Now compute pushout of K -> L and K -> C
    //     let po_result = compute_pushout(&l_morph, &pc_result.morphism_from_a).unwrap();
    //     // C should have 2 nodes (g1 preserved, g2 deleted, g3 context) and 1 edge (context)
    //     assert_eq!(result.complement.nodes().len(), 2);
    //     assert_eq!(result.complement.edges().len(), 1);

    //     // The pushout should be isomorphic to G
    //     assert!(are_isomorphic(&po_result.pushout, &g));
    //     // Check that k1 is mapped correctly
    //     let k1_in_c = result.morphism_from_k.map_node(k1).unwrap();
    //     let k1_in_g = result.morphism_to_g.map_node(k1_in_c).unwrap();
    //     assert_eq!(k1_in_g, g1);
    // }





    // #[test]
    // fn test_pushout_complement_preserve_binding_structure() {
    //     // Delete an edge but preserve a lambda with bindings

    //     let mut k = BHyp::new();
    //     let k_x = k.add_node();
    //     let k_body = k.add_node();
    //     let k_out = k.add_node();
    //     let k_lambda = k
    //         .add_edge(
    //             vec![SourceWithBinding {
    //                 source: k_body,
    //                 bound: vec![k_x],
    //             }],
    //             vec![k_out],
    //             Some(Label::Symbol("λ".to_string())),
    //         )
    //         .unwrap();

    //     let mut l = BHyp::new();
    //     let l_x = l.add_node();
    //     let l_body = l.add_node();
    //     let l_out = l.add_node();
    //     let l_extra = l.add_node(); // extra node to delete
    //     let l_lambda = l
    //         .add_edge(
    //             vec![SourceWithBinding {
    //                 source: l_body,
    //                 bound: vec![l_x],
    //             }],
    //             vec![l_out],
    //             Some(Label::Symbol("λ".to_string())),
    //         )
    //         .unwrap();
    //     let l_edge = l
    //         .add_edge(
    //             vec![SourceWithBinding {
    //                 source: l_body,
    //                 bound: vec![],
    //             }],
    //             vec![l_extra],
    //             Some(Label::Symbol("f".to_string())),
    //         )
    //         .unwrap();

    //     // G = L
    //     let g = l.clone();

    //     let l_morph = BHypMorphism::new(
    //         k.clone(),
    //         l.clone(),
    //         [(k_x, l_x), (k_body, l_body), (k_out, l_out)]
    //             .into_iter()
    //             .collect(),
    //         [(k_lambda, l_lambda)].into_iter().collect(),
    //     )
    //     .unwrap();

    //     let m = BHypMorphism::new(
    //         l.clone(),
    //         g.clone(),
    //         [
    //             (l_x, l_x),
    //             (l_body, l_body),
    //             (l_out, l_out),
    //             (l_extra, l_extra),
    //         ]
    //         .into_iter()
    //         .collect(),
    //         [(l_lambda, l_lambda), (l_edge, l_edge)]
    //             .into_iter()
    //             .collect(),
    //     )
    //     .unwrap();

    //     let result = compute_pushout_complement(&l_morph, &m).unwrap();

    //     // C should have 3 nodes (k_x, k_body, k_out) and 1 edge (lambda)
    //     assert_eq!(result.complement.nodes().len(), 3);
    //     assert_eq!(result.complement.edges().len(), 1);

    //     // Check that the lambda edge has correct binding structure
    //     let c_edges: Vec<_> = result.complement.edges().iter().collect();
    //     let c_e = *c_edges[0];
    //     let swbs = result.complement.get_sources_with_binding(c_e).unwrap();
    //     assert_eq!(swbs.len(), 1);
    //     assert_eq!(swbs[0].bound.len(), 1);
    // }

    // // ========================================================================
    // // Integration Tests
    // // ========================================================================


    // /// Create an identity span: L <- L -> L (all morphisms are identity)
    // fn identity_span(g: &BHyp) -> Span {
    //     let id_l = identity_morphism(g);
    //     let id_r = identity_morphism(g);
    //     Span {
    //         left: g.clone(),
    //         middle: g.clone(),
    //         right: g.clone(),
    //         to_l: id_l,
    //         to_r: id_r,
    //     }
    // }

    // /// Create a span where L = R but middle is different (smaller interface)
    // fn equal_lr_span(
    //     left_right: &BHyp,
    //     middle: &BHyp,
    //     to_l_nodes: HashMap<NodeId, NodeId>,
    //     to_l_edges: HashMap<EdgeId, EdgeId>,
    //     to_r_nodes: HashMap<NodeId, NodeId>,
    //     to_r_edges: HashMap<EdgeId, EdgeId>,
    // ) -> Result<Span, MorphismError> {
    //     let to_l = BHypMorphism::new(
    //         middle.clone(),
    //         left_right.clone(),
    //         to_l_nodes,
    //         to_l_edges,
    //     )?;
    //     let to_r = BHypMorphism::new(
    //         middle.clone(),
    //         left_right.clone(),
    //         to_r_nodes,
    //         to_r_edges,
    //     )?;
    //     Ok(Span {
    //         left: left_right.clone(),
    //         middle: middle.clone(),
    //         right: left_right.clone(),
    //         to_l,
    //         to_r,
    //     })
    // }

    // // ========================================================================
    // // Identity Span Tests
    // // ========================================================================

    // #[test]
    // fn test_dpo_identity_span_produces_identity_result() {
    //     // DPO with identity span L <- L -> L should produce identity result span
    //     // G <- G -> G (nothing changes)

    //     let mut g = BHyp::new();
    //     let g1 = g.add_node();
    //     let g2 = g.add_node();
    //     g.add_edge(
    //         vec![SourceWithBinding {
    //             source: g1,
    //             bound: vec![],
    //         }],
    //         vec![g2],
    //         Some(Label::Symbol("f".to_string())),
    //     )
    //     .unwrap();

    //     let span = identity_span(&g);
    //     let m = identity_morphism(&g); // Match L -> G is identity

    //     let result = dpo(&span, &g, &m).unwrap();

    //     // Result should be isomorphic to identity span on G
    //     assert!(are_isomorphic(&result.left, &g));
    //     assert!(are_isomorphic(&result.middle, &g));
    //     assert!(are_isomorphic(&result.right, &g));
        
    //     // The morphisms should be isomorphisms
    //     assert!(result.to_l.is_isomorphism());
    //     assert!(result.to_r.is_isomorphism());
    // }

    // #[test]
    // fn test_dpo_identity_span_on_empty_graph() {
    //     let g = BHyp::new();
    //     let span = identity_span(&g);
    //     let m = identity_morphism(&g);

    //     let result = dpo(&span, &g, &m).unwrap();

    //     assert!(result.left.is_empty());
    //     assert!(result.middle.is_empty());
    //     assert!(result.right.is_empty());
    // }

    // #[test]
    // fn test_dpo_identity_span_with_binding() {
    //     // Test identity span preserves binding structure
    //     let mut g = BHyp::new();
    //     let x = g.add_node();
    //     let body = g.add_node();
    //     let out = g.add_node();
    //     g.add_edge(
    //         vec![SourceWithBinding {
    //             source: body,
    //             bound: vec![x],
    //         }],
    //         vec![out],
    //         Some(Label::Symbol("λ".to_string())),
    //     )
    //     .unwrap();

    //     let span = identity_span(&g);
    //     let m = identity_morphism(&g);

    //     let result = dpo(&span, &g, &m).unwrap();

    //     // Check binding structure preserved
    //     assert_eq!(result.right.nodes().len(), 3);
    //     assert_eq!(result.right.edges().len(), 1);
        
    //     let e = *result.right.edges().iter().next().unwrap();
    //     let swbs = result.right.get_sources_with_binding(e).unwrap();
    //     assert_eq!(swbs[0].bound.len(), 1);
    // }

    // // ========================================================================
    // // Equal L=R (Different Middle) Tests
    // // ========================================================================

    // #[test]
    // fn test_dpo_equal_lr_different_middle_preserves_equality() {
    //     // Span: L <- K -> R where L = R (isomorphic) but K is smaller
    //     // Result should also have L' = R' (isomorphic)

    //     // L = R: two nodes with edge
    //     let mut lr = BHyp::new();
    //     let lr1 = lr.add_node();
    //     let lr2 = lr.add_node();
    //     lr.add_edge(
    //         vec![SourceWithBinding {
    //             source: lr1,
    //             bound: vec![],
    //         }],
    //         vec![lr2],
    //         Some(Label::Symbol("f".to_string())),
    //     )
    //     .unwrap();

    //     // K: just one node (the interface)
    //     let mut k = BHyp::new();
    //     let k1 = k.add_node();

    //     // Both to_l and to_r map k1 to lr1
    //     let span = equal_lr_span(
    //         &lr,
    //         &k,
    //         [(k1, lr1)].into_iter().collect(),
    //         HashMap::new(),
    //         [(k1, lr1)].into_iter().collect(),
    //         HashMap::new(),
    //     )
    //     .unwrap();

    //     // G = L (identity match)
    //     let g = lr.clone();
    //     let g1 = *g.nodes().iter().min().unwrap();
    //     let g2 = *g.nodes().iter().max().unwrap();
    //     let g_e = *g.edges().iter().next().unwrap();

    //     let m = BHypMorphism::new(
    //         lr.clone(),
    //         g.clone(),
    //         [(lr1, g1), (lr2, g2)].into_iter().collect(),
    //         [(EdgeId(0), g_e)].into_iter().collect(),
    //     )
    //     .unwrap();

    //     let result = dpo(&span, &g, &m).unwrap();

    //     // L' and R' should be isomorphic to each other
    //     assert!(are_isomorphic(&result.left, &result.right));
    // }

    // #[test]
    // fn test_dpo_equal_lr_with_context() {
    //     // L = R with different middle, applied to G with extra context
    //     // Result L' = R' should still hold

    //     // L = R: single node
    //     let mut lr = BHyp::new();
    //     let lr1 = lr.add_node();

    //     // K: same single node
    //     let mut k = BHyp::new();
    //     let k1 = k.add_node();

    //     let span = equal_lr_span(
    //         &lr,
    //         &k,
    //         [(k1, lr1)].into_iter().collect(),
    //         HashMap::new(),
    //         [(k1, lr1)].into_iter().collect(),
    //         HashMap::new(),
    //     )
    //     .unwrap();

    //     // G: the matched node plus extra context
    //     let mut g = BHyp::new();
    //     let g1 = g.add_node();
    //     let g2 = g.add_node();
    //     let g3 = g.add_node();
    //     g.add_edge(
    //         vec![SourceWithBinding {
    //             source: g1,
    //             bound: vec![],
    //         }],
    //         vec![g2],
    //         Some(Label::Symbol("context1".to_string())),
    //     )
    //     .unwrap();
    //     g.add_edge(
    //         vec![SourceWithBinding {
    //             source: g1,
    //             bound: vec![],
    //         }],
    //         vec![g3],
    //         Some(Label::Symbol("context2".to_string())),
    //     )
    //     .unwrap();

    //     let m = BHypMorphism::new(
    //         lr.clone(),
    //         g.clone(),
    //         [(lr1, g1)].into_iter().collect(),
    //         HashMap::new(),
    //     )
    //     .unwrap();

    //     let result = dpo(&span, &g, &m).unwrap();

    //     // Since L = R and they share the same interface to K,
    //     // the result should have L' isomorphic to R'
    //     assert!(are_isomorphic(&result.left, &result.right));
        
    //     // Context should be preserved
    //     assert_eq!(result.right.nodes().len(), 3);
    //     assert_eq!(result.right.edges().len(), 2);
    // }

    // // ========================================================================
    // // Symmetric Span Tests  
    // // ========================================================================

    // #[test]
    // fn test_dpo_symmetric_span() {
    //     // If the span is symmetric (to_l and to_r are "the same"), 
    //     // result should also be symmetric

    //     let mut k = BHyp::new();
    //     let k1 = k.add_node();
    //     let k2 = k.add_node();

    //     let mut l = BHyp::new();
    //     let l1 = l.add_node();
    //     let l2 = l.add_node();
    //     l.add_edge(
    //         vec![SourceWithBinding {
    //             source: l1,
    //             bound: vec![],
    //         }],
    //         vec![l2],
    //         Some(Label::Symbol("f".to_string())),
    //     )
    //     .unwrap();

    //     // Symmetric: R is isomorphic to L
    //     let mut r = BHyp::new();
    //     let r1 = r.add_node();
    //     let r2 = r.add_node();
    //     r.add_edge(
    //         vec![SourceWithBinding {
    //             source: r1,
    //             bound: vec![],
    //         }],
    //         vec![r2],
    //         Some(Label::Symbol("f".to_string())),
    //     )
    //     .unwrap();

    //     let to_l = BHypMorphism::new(
    //         k.clone(),
    //         l.clone(),
    //         [(k1, l1), (k2, l2)].into_iter().collect(),
    //         HashMap::new(),
    //     )
    //     .unwrap();

    //     let to_r = BHypMorphism::new(
    //         k.clone(),
    //         r.clone(),
    //         [(k1, r1), (k2, r2)].into_iter().collect(),
    //         HashMap::new(),
    //     )
    //     .unwrap();

    //     let span = Span {
    //         left: l.clone(),
    //         middle: k,
    //         right: r,
    //         to_l,
    //         to_r,
    //     };

    //     let g = l.clone();
    //     let m = identity_morphism(&l);

    //     let result = dpo(&span, &g, &m).unwrap();

    //     // Result L' and R' should be isomorphic (symmetric rewrite)
    //     assert!(are_isomorphic(&result.left, &result.right));
    // }

    // // ========================================================================
    // // Deletion/Addition Preservation Tests
    // // ========================================================================

    // #[test]
    // fn test_dpo_deletion_in_span_causes_deletion_in_result() {
    //     // L has more than K (deletion), R = K (no addition)
    //     // Result: items deleted from G

    //     let mut k = BHyp::new();
    //     let k1 = k.add_node();

    //     let mut l = BHyp::new();
    //     let l1 = l.add_node();
    //     let l2 = l.add_node();
    //     let l_e = l
    //         .add_edge(
    //             vec![SourceWithBinding {
    //                 source: l1,
    //                 bound: vec![],
    //             }],
    //             vec![l2],
    //             Some(Label::Symbol("delete_me".to_string())),
    //         )
    //         .unwrap();

    //     // R = K (just one node, no edge)
    //     let mut r = BHyp::new();
    //     let r1 = r.add_node();

    //     let to_l = BHypMorphism::new(
    //         k.clone(),
    //         l.clone(),
    //         [(k1, l1)].into_iter().collect(),
    //         HashMap::new(),
    //     )
    //     .unwrap();

    //     let to_r = BHypMorphism::new(
    //         k.clone(),
    //         r.clone(),
    //         [(k1, r1)].into_iter().collect(),
    //         HashMap::new(),
    //     )
    //     .unwrap();

    //     let span = Span {
    //         left: l.clone(),
    //         middle: k,
    //         right: r,
    //         to_l,
    //         to_r,
    //     };

    //     // G = L
    //     let g = l.clone();
    //     let m = identity_morphism(&l);

    //     let result = dpo(&span, &g, &m).unwrap();

    //     // Result right should have 1 node, 0 edges (deletion happened)
    //     assert_eq!(result.right.nodes().len(), 1);
    //     assert_eq!(result.right.edges().len(), 0);
    // }

    // #[test]
    // fn test_dpo_addition_in_span_causes_addition_in_result() {
    //     // L = K (no deletion), R has more than K (addition)

    //     let mut k = BHyp::new();
    //     let k1 = k.add_node();

    //     // L = K
    //     let mut l = BHyp::new();
    //     let l1 = l.add_node();

    //     let mut r = BHyp::new();
    //     let r1 = r.add_node();
    //     let r2 = r.add_node();
    //     r.add_edge(
    //         vec![SourceWithBinding {
    //             source: r1,
    //             bound: vec![],
    //         }],
    //         vec![r2],
    //         Some(Label::Symbol("added".to_string())),
    //     )
    //     .unwrap();

    //     let to_l = BHypMorphism::new(
    //         k.clone(),
    //         l.clone(),
    //         [(k1, l1)].into_iter().collect(),
    //         HashMap::new(),
    //     )
    //     .unwrap();

    //     let to_r = BHypMorphism::new(
    //         k.clone(),
    //         r.clone(),
    //         [(k1, r1)].into_iter().collect(),
    //         HashMap::new(),
    //     )
    //     .unwrap();

    //     let span = Span {
    //         left: l.clone(),
    //         middle: k,
    //         right: r,
    //         to_l,
    //         to_r,
    //     };

    //     let g = l.clone();
    //     let m = identity_morphism(&l);

    //     let result = dpo(&span, &g, &m).unwrap();

    //     // Result right should have 2 nodes, 1 edge (addition happened)
    //     assert_eq!(result.right.nodes().len(), 2);
    //     assert_eq!(result.right.edges().len(), 1);

    //     let e = *result.right.edges().iter().next().unwrap();
    //     assert_eq!(
    //         result.right.get_label(e),
    //         Some(&Label::Symbol("added".to_string()))
    //     );
    // }

    // // ========================================================================
    // // Context Preservation Tests
    // // ========================================================================

    // #[test]
    // fn test_dpo_preserves_context_nodes() {
    //     // Rewrite in G but context (unmatched parts) preserved

    //     let mut k = BHyp::new();
    //     let k1 = k.add_node();

    //     let mut l = BHyp::new();
    //     let l1 = l.add_node();

    //     let mut r = BHyp::new();
    //     let r1 = r.add_node();

    //     let to_l = BHypMorphism::new(
    //         k.clone(),
    //         l.clone(),
    //         [(k1, l1)].into_iter().collect(),
    //         HashMap::new(),
    //     )
    //     .unwrap();

    //     let to_r = BHypMorphism::new(
    //         k.clone(),
    //         r.clone(),
    //         [(k1, r1)].into_iter().collect(),
    //         HashMap::new(),
    //     )
    //     .unwrap();

    //     let span = Span {
    //         left: l.clone(),
    //         middle: k,
    //         right: r,
    //         to_l,
    //         to_r,
    //     };

    //     // G has matched node plus context
    //     let mut g = BHyp::new();
    //     let g1 = g.add_node();
    //     let g_ctx1 = g.add_node();
    //     let g_ctx2 = g.add_node();
    //     g.add_edge(
    //         vec![SourceWithBinding {
    //             source: g_ctx1,
    //             bound: vec![],
    //         }],
    //         vec![g_ctx2],
    //         Some(Label::Symbol("context".to_string())),
    //     )
    //     .unwrap();

    //     let m = BHypMorphism::new(
    //         l.clone(),
    //         g.clone(),
    //         [(l1, g1)].into_iter().collect(),
    //         HashMap::new(),
    //     )
    //     .unwrap();

    //     let result = dpo(&span, &g, &m).unwrap();

    //     // Context should be preserved in result
    //     assert_eq!(result.right.nodes().len(), 3);
    //     assert_eq!(result.right.edges().len(), 1);

    //     let e = *result.right.edges().iter().next().unwrap();
    //     assert_eq!(
    //         result.right.get_label(e),
    //         Some(&Label::Symbol("context".to_string()))
    //     );
    // }

    // #[test]
    // fn test_dpo_preserves_context_connected_to_interface() {
    //     // Context connected to interface node is preserved

    //     let mut k = BHyp::new();
    //     let k1 = k.add_node();
    //     let k2 = k.add_node();

    //     let mut l = BHyp::new();
    //     let l1 = l.add_node();
    //     let l2 = l.add_node();
    //     let l3 = l.add_node();
    //     let l_e = l
    //         .add_edge(
    //             vec![SourceWithBinding {
    //                 source: l1,
    //                 bound: vec![],
    //             }],
    //             vec![l3],
    //             Some(Label::Symbol("to_delete".to_string())),
    //         )
    //         .unwrap();

    //     let mut r = BHyp::new();
    //     let r1 = r.add_node();
    //     let r2 = r.add_node();

    //     let to_l = BHypMorphism::new(
    //         k.clone(),
    //         l.clone(),
    //         [(k1, l1), (k2, l2)].into_iter().collect(),
    //         HashMap::new(),
    //     )
    //     .unwrap();

    //     let to_r = BHypMorphism::new(
    //         k.clone(),
    //         r.clone(),
    //         [(k1, r1), (k2, r2)].into_iter().collect(),
    //         HashMap::new(),
    //     )
    //     .unwrap();

    //     let span = Span {
    //         left: l.clone(),
    //         middle: k,
    //         right: r,
    //         to_l,
    //         to_r,
    //     };

    //     // G = L plus context edge from l2
    //     let mut g = BHyp::new();
    //     let g1 = g.add_node();
    //     let g2 = g.add_node();
    //     let g3 = g.add_node();
    //     let g4 = g.add_node(); // context node
    //     let g_e1 = g
    //         .add_edge(
    //             vec![SourceWithBinding {
    //                 source: g1,
    //                 bound: vec![],
    //             }],
    //             vec![g3],
    //             Some(Label::Symbol("to_delete".to_string())),
    //         )
    //         .unwrap();
    //     g.add_edge(
    //         vec![SourceWithBinding {
    //             source: g2,
    //             bound: vec![],
    //         }],
    //         vec![g4],
    //         Some(Label::Symbol("context".to_string())),
    //     )
    //     .unwrap();

    //     let m = BHypMorphism::new(
    //         l.clone(),
    //         g.clone(),
    //         [(l1, g1), (l2, g2), (l3, g3)].into_iter().collect(),
    //         [(l_e, g_e1)].into_iter().collect(),
    //     )
    //     .unwrap();

    //     let result = dpo(&span, &g, &m).unwrap();

    //     // Result should have 3 nodes (l3/g3 deleted) and 1 edge (context preserved)
    //     assert_eq!(result.right.nodes().len(), 3);
    //     assert_eq!(result.right.edges().len(), 1);

    //     let e = *result.right.edges().iter().next().unwrap();
    //     assert_eq!(
    //         result.right.get_label(e),
    //         Some(&Label::Symbol("context".to_string()))
    //     );
    // }

    // // ========================================================================
    // // Binding-Specific DPO Tests
    // // ========================================================================

    // #[test]
    // fn test_dpo_preserves_binding_in_context() {
    //     // Lambda in context should be preserved with correct binding

    //     let mut k = BHyp::new();
    //     let k1 = k.add_node();

    //     let mut l = BHyp::new();
    //     let l1 = l.add_node();

    //     let mut r = BHyp::new();
    //     let r1 = r.add_node();

    //     let to_l = BHypMorphism::new(
    //         k.clone(),
    //         l.clone(),
    //         [(k1, l1)].into_iter().collect(),
    //         HashMap::new(),
    //     )
    //     .unwrap();

    //     let to_r = BHypMorphism::new(
    //         k.clone(),
    //         r.clone(),
    //         [(k1, r1)].into_iter().collect(),
    //         HashMap::new(),
    //     )
    //     .unwrap();

    //     let span = Span {
    //         left: l.clone(),
    //         middle: k,
    //         right: r,
    //         to_l,
    //         to_r,
    //     };

    //     // G: matched node plus lambda context
    //     let mut g = BHyp::new();
    //     let g1 = g.add_node(); // matched
    //     let g_x = g.add_node(); // bound var
    //     let g_body = g.add_node(); // body
    //     let g_out = g.add_node(); // output
    //     g.add_edge(
    //         vec![SourceWithBinding {
    //             source: g_body,
    //             bound: vec![g_x],
    //         }],
    //         vec![g_out],
    //         Some(Label::Symbol("λ".to_string())),
    //     )
    //     .unwrap();

    //     let m = BHypMorphism::new(
    //         l.clone(),
    //         g.clone(),
    //         [(l1, g1)].into_iter().collect(),
    //         HashMap::new(),
    //     )
    //     .unwrap();

    //     let result = dpo(&span, &g, &m).unwrap();

    //     // Lambda with binding should be preserved
    //     assert_eq!(result.right.nodes().len(), 4);
    //     assert_eq!(result.right.edges().len(), 1);

    //     let e = *result.right.edges().iter().next().unwrap();
    //     let swbs = result.right.get_sources_with_binding(e).unwrap();
    //     assert_eq!(swbs.len(), 1);
    //     assert_eq!(swbs[0].bound.len(), 1);
    //     assert_eq!(
    //         result.right.get_label(e),
    //         Some(&Label::Symbol("λ".to_string()))
    //     );
    // }

    // #[test]
    // fn test_dpo_adds_binding_edge() {
    //     // Rule adds a lambda edge

    //     let mut k = BHyp::new();
    //     let k1 = k.add_node();
    //     let k2 = k.add_node();

    //     let mut l = BHyp::new();
    //     let l1 = l.add_node();
    //     let l2 = l.add_node();

    //     let mut r = BHyp::new();
    //     let r1 = r.add_node();
    //     let r2 = r.add_node();
    //     let r3 = r.add_node(); // new output node
    //     r.add_edge(
    //         vec![SourceWithBinding {
    //             source: r2,
    //             bound: vec![r1],
    //         }],
    //         vec![r3],
    //         Some(Label::Symbol("λ".to_string())),
    //     )
    //     .unwrap();

    //     let to_l = BHypMorphism::new(
    //         k.clone(),
    //         l.clone(),
    //         [(k1, l1), (k2, l2)].into_iter().collect(),
    //         HashMap::new(),
    //     )
    //     .unwrap();

    //     let to_r = BHypMorphism::new(
    //         k.clone(),
    //         r.clone(),
    //         [(k1, r1), (k2, r2)].into_iter().collect(),
    //         HashMap::new(),
    //     )
    //     .unwrap();

    //     let span = Span {
    //         left: l.clone(),
    //         middle: k,
    //         right: r,
    //         to_l,
    //         to_r,
    //     };

    //     let g = l.clone();
    //     let m = identity_morphism(&l);

    //     let result = dpo(&span, &g, &m).unwrap();

    //     // Should have 3 nodes and 1 lambda edge
    //     assert_eq!(result.right.nodes().len(), 3);
    //     assert_eq!(result.right.edges().len(), 1);

    //     let e = *result.right.edges().iter().next().unwrap();
    //     let swbs = result.right.get_sources_with_binding(e).unwrap();
    //     assert_eq!(swbs[0].bound.len(), 1);
    // }

}