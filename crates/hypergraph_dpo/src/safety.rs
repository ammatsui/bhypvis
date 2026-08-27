// src/safety.rs
//! Safety checking for hypergraphs with binding (Definition 3.7)
//!
//! A hypergraph with binding is **safe** if it satisfies five conditions:
//! 1. Each vertex is bound to at most one edge, at most once
//! 2. No two distinct edges share their body
//! 3. No bound vertex is a target
//! 4. No leaking: body outputs connected to bound vertices aren't shared sources
//! 5. No leaking: body outputs aren't in the output interface

use std::collections::{HashMap, HashSet};
use crate::bhyp::{BHyp, BHyp_with_interface, NodeId, EdgeId};

/// Types of safety violations
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SafetyViolation {
    /// Condition 1a: A vertex is bound by multiple edges
    BoundToMultipleEdges {
        node: NodeId,
        edges: Vec<EdgeId>,
    },
    /// Condition 1b: A vertex is bound multiple times by the same edge
    BoundMultipleTimes {
        node: NodeId,
        edge: EdgeId,
        count: usize,
    },
    /// Condition 2: Two edges share body nodes
    SharedBody {
        edge1: EdgeId,
        edge2: EdgeId,
        shared_nodes: Vec<NodeId>,
    },
    /// Condition 3: A bound vertex is also a target of some edge
    BoundNodeIsTarget {
        node: NodeId,
        binding_edge: EdgeId,
        target_edge: EdgeId,
    },
    /// Condition 4: Leaking - body output connected to bound vertex is shared source
    LeakingSharedSource {
        node: NodeId,
        body_edge: EdgeId,
        external_edge: EdgeId,
    },
    /// Condition 5: Leaking - body output is in output interface
    LeakingInOutput {
        node: NodeId,
        edge: EdgeId,
    },
}

/// Result of safety checking
pub type SafetyResult = Result<(), Vec<SafetyViolation>>;

/// Check all safety conditions for a hypergraph with binding
/// Returns Ok(()) if safe, Err(violations) if unsafe
pub fn check_safety(g: &BHyp) -> SafetyResult {
    let mut violations = Vec::new();
    
    // Check condition 1: each vertex bound to at most one edge, at most once
    check_binding_uniqueness(g, &mut violations);
    
    // Check condition 2: no shared body between edges
    check_no_shared_body(g, &mut violations);
    
    // Check condition 3: no bound vertex is a target
    check_bound_not_target(g, &mut violations);
    
    // Check conditions 4 & 5: no leaking
    check_no_leaking(g, &mut violations);
    
    if violations.is_empty() {
        Ok(())
    } else {
        Err(violations)
    }
}

pub fn is_safe(g: &BHyp) -> bool {
    check_safety(g).is_ok()
}

/// Check all safety conditions for a hypergraph with interface
/// Also checks condition 5 (body outputs not in output interface)
pub fn check_safety_with_interface(g: &BHyp_with_interface) -> SafetyResult {
    let mut violations = Vec::new();
    
    // Check conditions 1-4 on underlying BHyp
    check_binding_uniqueness(g.bhyp(), &mut violations);
    check_no_shared_body(g.bhyp(), &mut violations);
    check_bound_not_target(g.bhyp(), &mut violations);
    check_no_leaking(g.bhyp(), &mut violations);
    
    // Check condition 5: body outputs not in output interface
    check_no_leaking_to_output_interface(g, &mut violations);
    
    if violations.is_empty() {
        Ok(())
    } else {
        Err(violations)
    }
}

/// Check condition 1: Each vertex is bound to at most one edge, at most once
fn check_binding_uniqueness(g: &BHyp, violations: &mut Vec<SafetyViolation>) {
    // Track which edges bind each node
    let mut bound_by: HashMap<NodeId, Vec<EdgeId>> = HashMap::new();
    
    for &edge_id in g.edges() {
        if let Some(swbs) = g.get_sources_with_binding(edge_id) {
            // Count how many times each node is bound by this edge
            let mut bind_count: HashMap<NodeId, usize> = HashMap::new();
            
            for swb in swbs {
                for &bound_node in &swb.bound {
                    *bind_count.entry(bound_node).or_insert(0) += 1;
                    bound_by.entry(bound_node).or_default().push(edge_id);
                }
            }
            
            // Check for multiple bindings by same edge (condition 1b)
            for (&node, &count) in &bind_count {
                if count > 1 {
                    violations.push(SafetyViolation::BoundMultipleTimes {
                        node,
                        edge: edge_id,
                        count,
                    });
                }
            }
        }
    }
    
    // Check for binding by multiple edges (condition 1a)
    for (node, edges) in bound_by {
        // Remove duplicates to count unique edges
        let unique_edges: HashSet<_> = edges.iter().cloned().collect();
        if unique_edges.len() > 1 {
            violations.push(SafetyViolation::BoundToMultipleEdges {
                node,
                edges: unique_edges.into_iter().collect(),
            });
        }
    }
}

/// Compute the full body of an edge (union of bodies at all source indices with binding)
fn compute_full_body(g: &BHyp, edge_id: EdgeId) -> HashSet<NodeId> {
    let mut full_body = HashSet::new();
    
    if let Some(swbs) = g.get_sources_with_binding(edge_id) {
        for (source_idx, swb) in swbs.iter().enumerate() {
            if !swb.bound.is_empty() {
                if let Some(body) = g.compute_body(edge_id, source_idx) {
                    full_body.extend(body);
                }
            }
        }
    }
    
    full_body
}

/// Check condition 2: No two distinct edges share their body
fn check_no_shared_body(g: &BHyp, violations: &mut Vec<SafetyViolation>) {
    // Compute bodies for all edges with binding
    let mut bodies: HashMap<EdgeId, HashSet<NodeId>> = HashMap::new();
    
    for &edge_id in g.edges() {
        if let Some(swbs) = g.get_sources_with_binding(edge_id) {
            let has_binding = swbs.iter().any(|swb| !swb.bound.is_empty());
            
            if has_binding {
                bodies.insert(edge_id, compute_full_body(g, edge_id));
            }
        }
    }
    
    // Check for overlaps between bodies
    let edges_with_bodies: Vec<_> = bodies.keys().cloned().collect();
    for i in 0..edges_with_bodies.len() {
        for j in (i + 1)..edges_with_bodies.len() {
            let e1 = edges_with_bodies[i];
            let e2 = edges_with_bodies[j];
            
            let body1 = bodies.get(&e1).unwrap();
            let body2 = bodies.get(&e2).unwrap();
            
            let shared: Vec<NodeId> = body1.intersection(body2).cloned().collect();
            
            if !shared.is_empty() {
                violations.push(SafetyViolation::SharedBody {
                    edge1: e1,
                    edge2: e2,
                    shared_nodes: shared,
                });
            }
        }
    }
}

/// Check condition 3: No bound vertex is a target
fn check_bound_not_target(g: &BHyp, violations: &mut Vec<SafetyViolation>) {
    // Collect all bound nodes and which edge binds them
    let mut bound_nodes: HashMap<NodeId, EdgeId> = HashMap::new();
    
    for &edge_id in g.edges() {
        if let Some(swbs) = g.get_sources_with_binding(edge_id) {
            for swb in swbs {
                for &bound in &swb.bound {
                    bound_nodes.insert(bound, edge_id);
                }
            }
        }
    }
    
    // Check if any bound node is a target
    for &edge_id in g.edges() {
        if let Some(targets) = g.get_targets(edge_id) {
            for &target in targets {
                if let Some(&binding_edge) = bound_nodes.get(&target) {
                    violations.push(SafetyViolation::BoundNodeIsTarget {
                        node: target,
                        binding_edge,
                        target_edge: edge_id,
                    });
                }
            }
        }
    }
}

/// Get body outputs: targets of edges in the body that are not also sources within the body
fn compute_body_outputs(g: &BHyp, edge_id: EdgeId, source_idx: usize) -> HashSet<NodeId> {
    let mut body_outputs = HashSet::new();
    
    if let Some(body_edges) = g.compute_body_edges(edge_id, source_idx) {
        // Get all targets of body edges
        for &body_edge_id in &body_edges {
            if let Some(targets) = g.get_targets(body_edge_id) {
                body_outputs.extend(targets.iter().cloned());
            }
        }
        
        // Remove nodes that are sources of other body edges (they're internal)
        for &body_edge_id in &body_edges {
            if let Some(sources) = g.get_sources(body_edge_id) {
                for source in sources {
                    body_outputs.remove(&source);
                }
            }
        }
    }
    
    body_outputs
}

/// Check condition 4: No leaking via shared sources
/// "If a vertex in output(body(e,i)) is connected to the bound vertex bnd(e,i)
/// by a sequence of edges (through sources), then it should not be a shared source
/// of edges in body(e,i) and outside body(e,i)"
fn check_no_leaking(g: &BHyp, violations: &mut Vec<SafetyViolation>) {
    for &edge_id in g.edges() {
        if let Some(swbs) = g.get_sources_with_binding(edge_id) {
            for (source_idx, swb) in swbs.iter().enumerate() {
                if swb.bound.is_empty() {
                    continue;
                }
                
                // Get body nodes and body edges
                let body_nodes = match g.compute_body(edge_id, source_idx) {
                    Some(b) => b,
                    None => continue,
                };
                
                let body_edges = match g.compute_body_edges(edge_id, source_idx) {
                    Some(e) => e,
                    None => continue,
                };
                
                // Check each node in the body that is used as a source
                for &body_node in &body_nodes {
                    // Check if this node is a source of both body edges and external edges
                    let mut is_source_in_body = false;
                    let mut external_edges: Vec<EdgeId> = Vec::new();
                    
                    for &other_edge_id in g.edges() {
                        if other_edge_id == edge_id {
                            continue;
                        }
                        
                        if let Some(sources) = g.get_sources(other_edge_id) {
                            if sources.contains(&body_node) {
                                if body_edges.contains(&other_edge_id) {
                                    is_source_in_body = true;
                                } else {
                                    external_edges.push(other_edge_id);
                                }
                            }
                        }
                    }
                    
                    // If node is source in both body and external edges, it's leaking
                    if is_source_in_body && !external_edges.is_empty() {
                        for external_edge in external_edges {
                            violations.push(SafetyViolation::LeakingSharedSource {
                                node: body_node,
                                body_edge: edge_id,
                                external_edge,
                            });
                        }
                    }
                }
            }
        }
    }
}

/// Check condition 5: Body outputs not in output interface
fn check_no_leaking_to_output_interface(g: &BHyp_with_interface, violations: &mut Vec<SafetyViolation>) {
    let output_nodes = g.output_interface_nodes();
    
    for &edge_id in g.edges() {
        if let Some(swbs) = g.get_sources_with_binding(edge_id) {
            for (source_idx, swb) in swbs.iter().enumerate() {
                if swb.bound.is_empty() {
                    continue;
                }
                
                let body_outputs = compute_body_outputs(g.bhyp(), edge_id, source_idx);
                
                // Check if any body output is in the output interface
                for &output in &body_outputs {
                    if output_nodes.contains(&output) {
                        violations.push(SafetyViolation::LeakingInOutput {
                            node: output,
                            edge: edge_id,
                        });
                    }
                }
            }
        }
    }
}

/// Check safety for a specific metaedge instance
pub fn check_metaedge_safety(g: &BHyp, metaedge_id: EdgeId) -> SafetyResult {
    let mut violations = Vec::new();
    
    // Do full safety check
    check_binding_uniqueness(g, &mut violations);
    check_no_shared_body(g, &mut violations);
    check_bound_not_target(g, &mut violations);
    check_no_leaking(g, &mut violations);
    
    // Filter violations to those relevant to the metaedge
    let relevant: Vec<_> = violations.into_iter()
        .filter(|v| match v {
            SafetyViolation::BoundToMultipleEdges { edges, .. } => {
                edges.contains(&metaedge_id)
            }
            SafetyViolation::BoundMultipleTimes { edge, .. } => {
                *edge == metaedge_id
            }
            SafetyViolation::SharedBody { edge1, edge2, .. } => {
                *edge1 == metaedge_id || *edge2 == metaedge_id
            }
            SafetyViolation::BoundNodeIsTarget { binding_edge, target_edge, .. } => {
                *binding_edge == metaedge_id || *target_edge == metaedge_id
            }
            SafetyViolation::LeakingSharedSource { body_edge, external_edge, .. } => {
                *body_edge == metaedge_id || *external_edge == metaedge_id
            }
            SafetyViolation::LeakingInOutput { edge, .. } => {
                *edge == metaedge_id
            }
        })
        .collect();
    
    if relevant.is_empty() {
        Ok(())
    } else {
        Err(relevant)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bhyp::{Label, SourceWithBinding};
    
    #[test]
    fn test_safe_simple_lambda() {
        // λx.f(x) - standard safe lambda term
        let mut g = BHyp::new();
        let x = g.add_node();
        let fx = g.add_node();
        let result = g.add_node();
        
        // f(x)
        g.add_edge(
            vec![SourceWithBinding { source: x, bound: vec![] }],
            vec![fx],
            Some(Label::Symbol("f".to_string())),
        ).unwrap();
        
        // λx.f(x)
        g.add_edge(
            vec![SourceWithBinding { source: fx, bound: vec![x] }],
            vec![result],
            Some(Label::Symbol("λ".to_string())),
        ).unwrap();
        
        assert!(check_safety(&g).is_ok());
    }
    
    #[test]
    fn test_safe_nested_lambda() {
        // λx.λy.f(x,y) - nested lambda
        let mut g = BHyp::new();
        let x = g.add_node();
        let y = g.add_node();
        let fxy = g.add_node();
        let inner = g.add_node();
        let outer = g.add_node();
        
        // f(x, y)
        g.add_edge(
            vec![
                SourceWithBinding { source: x, bound: vec![] },
                SourceWithBinding { source: y, bound: vec![] },
            ],
            vec![fxy],
            Some(Label::Symbol("f".to_string())),
        ).unwrap();
        
        // λy.f(x,y)
        g.add_edge(
            vec![SourceWithBinding { source: fxy, bound: vec![y] }],
            vec![inner],
            Some(Label::Symbol("λ".to_string())),
        ).unwrap();
        
        // λx.λy.f(x,y)
        g.add_edge(
            vec![SourceWithBinding { source: inner, bound: vec![x] }],
            vec![outer],
            Some(Label::Symbol("λ".to_string())),
        ).unwrap();
        
        assert!(check_safety(&g).is_ok());
    }
    
    #[test]
    fn test_unsafe_bound_multiple_edges() {
        // x bound by two different lambda edges
        let mut g = BHyp::new();
        let x = g.add_node();
        let body1 = g.add_node();
        let body2 = g.add_node();
        let r1 = g.add_node();
        let r2 = g.add_node();
        
        // First lambda binds x
        g.add_edge(
            vec![SourceWithBinding { source: body1, bound: vec![x] }],
            vec![r1],
            Some(Label::Symbol("λ1".to_string())),
        ).unwrap();
        
        // Second lambda ALSO binds x - UNSAFE!
        g.add_edge(
            vec![SourceWithBinding { source: body2, bound: vec![x] }],
            vec![r2],
            Some(Label::Symbol("λ2".to_string())),
        ).unwrap();
        
        let result = check_safety(&g);
        assert!(result.is_err());
        
        let violations = result.unwrap_err();
        assert!(violations.iter().any(|v| matches!(v, 
            SafetyViolation::BoundToMultipleEdges { .. }
        )));
    }
    
    #[test]
    fn test_unsafe_bound_twice_same_edge() {
        // x bound twice by the same edge
        let mut g = BHyp::new();
        let x = g.add_node();
        let body = g.add_node();
        let result = g.add_node();
        
        // Edge binding x twice
        g.add_edge(
            vec![SourceWithBinding { source: body, bound: vec![x, x] }],
            vec![result],
            Some(Label::Symbol("λ".to_string())),
        ).unwrap();
        
        let result = check_safety(&g);
        assert!(result.is_err());
        
        let violations = result.unwrap_err();
        assert!(violations.iter().any(|v| matches!(v,
            SafetyViolation::BoundMultipleTimes { count: 2, .. }
        )));
    }
    
    #[test]
    fn test_unsafe_bound_is_target() {
        // x is both a target (output of f) and bound by lambda
        let mut g = BHyp::new();
        let input = g.add_node();
        let x = g.add_node(); // Will be both bound and target
        let result = g.add_node();
        
        // f produces x as output (x is a TARGET)
        g.add_edge(
            vec![SourceWithBinding { source: input, bound: vec![] }],
            vec![x],
            Some(Label::Symbol("f".to_string())),
        ).unwrap();
        
        // Lambda binds x (x is BOUND) - UNSAFE!
        g.add_edge(
            vec![SourceWithBinding { source: x, bound: vec![x] }],
            vec![result],
            Some(Label::Symbol("λ".to_string())),
        ).unwrap();
        
        let result = check_safety(&g);
        assert!(result.is_err());
        
        let violations = result.unwrap_err();
        assert!(violations.iter().any(|v| matches!(v,
            SafetyViolation::BoundNodeIsTarget { .. }
        )));
    }
    
    #[test]
    fn test_safe_no_binding() {
        // f(g(x)) - composition with no binding is always safe
        let mut g = BHyp::new();
        let x = g.add_node();
        let gx = g.add_node();
        let fgx = g.add_node();
        
        g.add_edge(
            vec![SourceWithBinding { source: x, bound: vec![] }],
            vec![gx],
            Some(Label::Symbol("g".to_string())),
        ).unwrap();
        
        g.add_edge(
            vec![SourceWithBinding { source: gx, bound: vec![] }],
            vec![fgx],
            Some(Label::Symbol("f".to_string())),
        ).unwrap();
        
        assert!(check_safety(&g).is_ok());
    }
    
    #[test]
    fn test_safe_with_interface() {
        let mut g = BHyp_with_interface::new();
        let x = g.add_node();
        let fx = g.add_node();
        let result = g.add_node();
        
        g.add_edge(
            vec![SourceWithBinding { source: x, bound: vec![] }],
            vec![fx],
            Some(Label::Symbol("f".to_string())),
        ).unwrap();
        
        g.add_edge(
            vec![SourceWithBinding { source: fx, bound: vec![x] }],
            vec![result],
            Some(Label::Symbol("λ".to_string())),
        ).unwrap();
        
        assert!(check_safety_with_interface(&g).is_ok());
    }
}