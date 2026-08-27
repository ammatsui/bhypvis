use std::collections::HashMap;
use std::env;
use std::fs::File;
use std::io::Write;

use hypergraph_dpo::bhyp::{BHyp, BHyp_with_interface, EdgeId, Label, NodeId, Signature, SourceWithBinding};
use hypergraph_dpo::categorical::{BHypMorphism, pushout, dpo, RewriteRule};
use hypergraph_dpo::visualisation::{
    bhyp_to_dot_labelled, bhyp_to_dot_unlabelled, bhyp_with_interface_to_dot_labelled,
    bhyp_with_interface_cospan_to_dot, 
    morphism_to_dot_labelled, pushout_to_dot_labelled, dpo_to_dot_labelled, 
    DotConfig,
};
use hypergraph_dpo::safety::{check_safety, SafetyViolation};

/// Simple example: function application f(x)
fn example_simple_function() -> BHyp {
    let mut g = BHyp::new();
    let n1 = g.add_node(); // source x
    let n2 = g.add_node(); // target f(x)

    g.add_edge(
        vec![SourceWithBinding {
            source: n1,
            bound: vec![],
        }],
        vec![n2],
        Some(Label::Symbol("f".to_string())),
    )
    .unwrap();

    g
}

/// Lambda abstraction: λx. f(x)
fn example_lambda() -> BHyp {
    let mut g = BHyp::new();

    let x = g.add_node(); // bound variable
    let f_node = g.add_node(); // output of f(x)
    let lambda_out = g.add_node(); // output of λx.f(x)

    // f(x)
    g.add_edge(
        vec![SourceWithBinding {
            source: x,
            bound: vec![],
        }],
        vec![f_node],
        Some(Label::Symbol("f".to_string())),
    )
    .unwrap();

    // λx binds x
    g.add_edge(
        vec![SourceWithBinding {
            source: f_node,
            bound: vec![x],
        }],
        vec![lambda_out],
        Some(Label::Symbol("λ".to_string())),
    )
    .unwrap();

    g
}

/// Higher-order example: λx. λy. f(x, y)
fn example_curried() -> BHyp {
    let mut sig = Signature::new();
    sig.add_symbol("λ".to_string(), vec![1]);
    sig.add_symbol("f".to_string(), vec![0, 0]); // f takes 2 arguments with no bindings

    let mut g = BHyp::with_signature(sig);

    let x = g.add_node(); // first bound variable
    let y = g.add_node(); // second bound variable
    let f_node = g.add_node(); // output of f(x, y)
    let lambda_y = g.add_node(); // output of λy.f(x, y)
    let lambda_x = g.add_node(); // output of λx.λy.f(x, y)

    // f(x, y)
    g.add_edge(
        vec![
            SourceWithBinding {
                source: x,
                bound: vec![],
            },
            SourceWithBinding {
                source: y,
                bound: vec![],
            },
        ],
        vec![f_node],
        Some(Label::Symbol("f".to_string())),
    )
    .unwrap();

    // λy binds y
    g.add_edge(
        vec![SourceWithBinding {
            source: f_node,
            bound: vec![y],
        }],
        vec![lambda_y],
        Some(Label::Symbol("λ".to_string())),
    )
    .unwrap();

    // λx binds x
    g.add_edge(
        vec![SourceWithBinding {
            source: lambda_y,
            bound: vec![x],
        }],
        vec![lambda_x],
        Some(Label::Symbol("λ".to_string())),
    )
    .unwrap();

    g
}

/// Complex example with metavariable
fn example_with_metavariable() -> BHyp {
    let mut g = BHyp::new();

    let n1 = g.add_node();
    let n2 = g.add_node();
    let n3 = g.add_node();
    let n4 = g.add_node();

    // Regular edge
    g.add_edge(
        vec![SourceWithBinding {
            source: n1,
            bound: vec![],
        }],
        vec![n2],
        Some(Label::Symbol("f".to_string())),
    )
    .unwrap();

    // Metavariable edge (arity 1, coarity 1)
    g.add_edge(
        vec![SourceWithBinding {
            source: n2,
            bound: vec![],
        }],
        vec![n3],
        Some(Label::Meta("M".to_string(), 1)),
    )
    .unwrap();

    // Another regular edge
    g.add_edge(
        vec![SourceWithBinding {
            source: n3,
            bound: vec![],
        }],
        vec![n4],
        Some(Label::Symbol("g".to_string())),
    )
    .unwrap();

    g
}

/// Example with BHyp_with_interface (cospan)
fn example_with_interface() -> BHyp_with_interface {
    let mut g = BHyp_with_interface::new();

    let n1 = g.add_node(); // will be input
    let n2 = g.add_node(); // internal
    let n3 = g.add_node(); // will be output

    g.add_edge(
        vec![SourceWithBinding {
            source: n1,
            bound: vec![],
        }],
        vec![n2],
        Some(Label::Symbol("f".to_string())),
    )
    .unwrap();

    g.add_edge(
        vec![SourceWithBinding {
            source: n2,
            bound: vec![],
        }],
        vec![n3],
        Some(Label::Symbol("g".to_string())),
    )
    .unwrap();

    g
}

/// Categorical example: Morphism between two simple graphs
/// Shows a structure-preserving map: (x -> f(x)) maps to (a -> f(a) -> g(a))
fn example_morphism() -> (BHyp, BHyp) {
    // Domain: simple graph with one edge f
    let mut domain = BHyp::new();
    let d_x = domain.add_node();
    let d_fx = domain.add_node();
    domain
        .add_edge(
            vec![SourceWithBinding {
                source: d_x,
                bound: vec![],
            }],
            vec![d_fx],
            Some(Label::Symbol("f".to_string())),
        )
        .unwrap();

    // Codomain: graph with chain f; g
    let mut codomain = BHyp::new();
    let c_a = codomain.add_node();
    let c_fa = codomain.add_node();
    let c_gfa = codomain.add_node();
    codomain
        .add_edge(
            vec![SourceWithBinding {
                source: c_a,
                bound: vec![],
            }],
            vec![c_fa],
            Some(Label::Symbol("f".to_string())),
        )
        .unwrap();
    codomain
        .add_edge(
            vec![SourceWithBinding {
                source: c_fa,
                bound: vec![],
            }],
            vec![c_gfa],
            Some(Label::Symbol("g".to_string())),
        )
        .unwrap();

    (domain, codomain)
}

/// Categorical example: Simple pushout square
/// Shows how two graphs with common vertex combine into a pushout
fn example_pushout() -> (BHyp, BHyp, BHyp, BHyp) {
    // Common vertex C
    let mut c = BHyp::new();
    let c_v = c.add_node();

    // First graph A: c_v -> a1 -> a2
    let mut a = BHyp::new();
    let a_v = a.add_node(); // image of c_v
    let a_1 = a.add_node();
    let a_2 = a.add_node();
    a.add_edge(
        vec![SourceWithBinding {
            source: a_v,
            bound: vec![],
        }],
        vec![a_1],
        Some(Label::Symbol("f".to_string())),
    )
    .unwrap();
    a.add_edge(
        vec![SourceWithBinding {
            source: a_1,
            bound: vec![],
        }],
        vec![a_2],
        Some(Label::Symbol("g".to_string())),
    )
    .unwrap();

    // Second graph B: c_v -> b1 -> b2
    let mut b = BHyp::new();
    let b_v = b.add_node(); // image of c_v
    let b_1 = b.add_node();
    let b_2 = b.add_node();
    b.add_edge(
        vec![SourceWithBinding {
            source: b_v,
            bound: vec![],
        }],
        vec![b_1],
        Some(Label::Symbol("h".to_string())),
    )
    .unwrap();
    b.add_edge(
        vec![SourceWithBinding {
            source: b_1,
            bound: vec![],
        }],
        vec![b_2],
        Some(Label::Symbol("k".to_string())),
    )
    .unwrap();

    // Morphisms: C -> A and C -> B (both map c_v to the common vertex)
    let mut f_nodes: HashMap<NodeId, NodeId> = HashMap::new();
    f_nodes.insert(c_v, a_v);
    let f_edges: HashMap<EdgeId, EdgeId> = HashMap::new();

    let mut g_nodes: HashMap<NodeId, NodeId> = HashMap::new();
    g_nodes.insert(c_v, b_v);
    let g_edges: HashMap<EdgeId, EdgeId> = HashMap::new();

    // Compute pushout
    let pushout_result = pushout(&c, &a, &b, &f_nodes, &f_edges, &g_nodes, &g_edges);

    (c, pushout_result.pushout.clone(), a, b)
}

/// Categorical example: DPO rewriting
/// Shows graph rewriting with a left-hand side rule, interface, and right-hand side
fn example_dpo_rewriting() -> (BHyp, BHyp, BHyp, BHyp) {
    // Left-hand side (rule LHS): pattern to match
    let mut lhs = BHyp::new();
    let l_x = lhs.add_node();
    let l_fx = lhs.add_node();
    lhs.add_edge(
        vec![SourceWithBinding {
            source: l_x,
            bound: vec![],
        }],
        vec![l_fx],
        Some(Label::Symbol("f".to_string())),
    )
    .unwrap();

    // Interface (preserved part)
    let mut interface = BHyp::new();
    let k_x = interface.add_node(); // x is preserved

    // Right-hand side (replacement)
    let mut rhs = BHyp::new();
    let r_x = rhs.add_node(); // x is preserved
    let r_gx = rhs.add_node(); // new node in result
    rhs.add_edge(
        vec![SourceWithBinding {
            source: r_x,
            bound: vec![],
        }],
        vec![r_gx],
        Some(Label::Symbol("g".to_string())),
    )
    .unwrap();

    // Host graph: graph to rewrite
    let mut host = BHyp::new();
    let h_a = host.add_node();
    let h_fa = host.add_node();
    let h_b = host.add_node();
    host.add_edge(
        vec![SourceWithBinding {
            source: h_a,
            bound: vec![],
        }],
        vec![h_fa],
        Some(Label::Symbol("f".to_string())),
    )
    .unwrap();
    host.add_edge(
        vec![SourceWithBinding {
            source: h_fa,
            bound: vec![],
        }],
        vec![h_b],
        Some(Label::Symbol("h".to_string())),
    )
    .unwrap();

    // Define morphisms for the rule
    let mut l_nodes: HashMap<NodeId, NodeId> = HashMap::new();
    l_nodes.insert(k_x, l_x);
    let l_edges: HashMap<EdgeId, EdgeId> = HashMap::new();

    let mut r_nodes: HashMap<NodeId, NodeId> = HashMap::new();
    r_nodes.insert(k_x, r_x);
    let r_edges: HashMap<EdgeId, EdgeId> = HashMap::new();

    let rule = RewriteRule::new(lhs, interface, rhs, l_nodes, l_edges, r_nodes, r_edges);

    // Define the match (find where to apply the rule in the host)
    let mut match_nodes: HashMap<NodeId, NodeId> = HashMap::new();
    match_nodes.insert(NodeId(0), h_a); // Match l_x to h_a
    let mut match_edges: HashMap<EdgeId, EdgeId> = HashMap::new();
    match_edges.insert(EdgeId(0), EdgeId(0)); // Match the f edge

    // Apply DPO rewriting
    let result = dpo(&rule, &host, &match_nodes, &match_edges)
        .expect("DPO rewriting failed");

    (rule.left, result.result, rule.right, host)
}

// ============================================================================
// SAFETY EXAMPLES FROM THE PAPER (Definition 3.7)
// ============================================================================

/// Safe example: Simple lambda term λx.f(x)
/// This is safe because:
/// - x is bound by exactly one edge (λ), exactly once
/// - No shared body between edges
/// - Bound variable x is not a target
/// - No leaking issues
fn example_safe_lambda() -> BHyp {
    let mut g = BHyp::new();
    
    let x = g.add_node();      // bound variable
    let fx = g.add_node();     // f(x) result
    let result = g.add_node(); // λx.f(x) result
    
    // f(x)
    g.add_edge(
        vec![SourceWithBinding { source: x, bound: vec![] }],
        vec![fx],
        Some(Label::Symbol("f".to_string())),
    ).unwrap();
    
    // λx.f(x) - binds x
    g.add_edge(
        vec![SourceWithBinding { source: fx, bound: vec![x] }],
        vec![result],
        Some(Label::Symbol("λ".to_string())),
    ).unwrap();
    
    g
}

/// Safe example: Nested lambda λx.λy.f(x,y)
/// Safe because each variable is bound exactly once by exactly one edge
fn example_safe_nested_lambda() -> BHyp {
    let mut g = BHyp::new();
    
    let x = g.add_node();       // outer bound variable
    let y = g.add_node();       // inner bound variable  
    let fxy = g.add_node();     // f(x,y) result
    let inner = g.add_node();   // λy.f(x,y) result
    let outer = g.add_node();   // λx.λy.f(x,y) result
    
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
    
    g
}

/// Safe example: Application with no binding
/// f(g(x)) - a simple composition with no binding
fn example_safe_composition() -> BHyp {
    let mut g = BHyp::new();
    
    let x = g.add_node();   // input
    let gx = g.add_node();  // g(x)
    let fgx = g.add_node(); // f(g(x))
    
    // g(x)
    g.add_edge(
        vec![SourceWithBinding { source: x, bound: vec![] }],
        vec![gx],
        Some(Label::Symbol("g".to_string())),
    ).unwrap();
    
    // f(g(x))
    g.add_edge(
        vec![SourceWithBinding { source: gx, bound: vec![] }],
        vec![fgx],
        Some(Label::Symbol("f".to_string())),
    ).unwrap();
    
    g
}

/// UNSAFE Example 1: Variable bound by multiple edges
/// Violates condition 1: "each vertex is bound to at most one edge"
fn example_unsafe_multiple_binders() -> BHyp {
    let mut g = BHyp::new();
    
    let x = g.add_node();       // variable bound by TWO edges - UNSAFE
    let body1 = g.add_node();   
    let body2 = g.add_node();   
    let result1 = g.add_node(); 
    let result2 = g.add_node(); 
    
    // First edge uses x
    g.add_edge(
        vec![SourceWithBinding { source: x, bound: vec![] }],
        vec![body1],
        Some(Label::Symbol("f".to_string())),
    ).unwrap();
    
    // Second edge uses x  
    g.add_edge(
        vec![SourceWithBinding { source: x, bound: vec![] }],
        vec![body2],
        Some(Label::Symbol("g".to_string())),
    ).unwrap();
    
    // First binder - binds x
    g.add_edge(
        vec![SourceWithBinding { source: body1, bound: vec![x] }],
        vec![result1],
        Some(Label::Symbol("λ".to_string())),
    ).unwrap();
    
    // Second binder - ALSO binds x! UNSAFE!
    g.add_edge(
        vec![SourceWithBinding { source: body2, bound: vec![x] }],
        vec![result2],
        Some(Label::Symbol("λ".to_string())),
    ).unwrap();
    
    g
}

/// UNSAFE Example 2: Variable bound multiple times by same edge
/// Violates condition 1: "at most once"
fn example_unsafe_bound_twice() -> BHyp {
    let mut g = BHyp::new();
    
    let x = g.add_node();      // bound TWICE by same edge - UNSAFE
    let body = g.add_node();   
    let result = g.add_node(); 
    
    // Use x
    g.add_edge(
        vec![SourceWithBinding { source: x, bound: vec![] }],
        vec![body],
        Some(Label::Symbol("f".to_string())),
    ).unwrap();
    
    // Bind x TWICE in the same binding list - UNSAFE!
    g.add_edge(
        vec![SourceWithBinding { source: body, bound: vec![x, x] }],
        vec![result],
        Some(Label::Symbol("λ".to_string())),
    ).unwrap();
    
    g
}

/// UNSAFE Example 3: Shared body between edges
/// Violates condition 2: "no two distinct edges share their body"
fn example_unsafe_shared_body() -> BHyp {
    let mut g = BHyp::new();
    
    let x = g.add_node();       // shared in body of two different binders
    let y = g.add_node();       
    let body_x = g.add_node();  
    let body_y = g.add_node();  
    let result1 = g.add_node(); 
    let result2 = g.add_node(); 
    
    // f(x) - x will be in body of edge1
    g.add_edge(
        vec![SourceWithBinding { source: x, bound: vec![] }],
        vec![body_x],
        Some(Label::Symbol("f".to_string())),
    ).unwrap();
    
    // g(x) - x will ALSO be in body of edge2! UNSAFE!
    g.add_edge(
        vec![SourceWithBinding { source: x, bound: vec![] }],
        vec![body_y],
        Some(Label::Symbol("g".to_string())),
    ).unwrap();
    
    // λy binds y, but body contains x
    g.add_edge(
        vec![SourceWithBinding { source: body_x, bound: vec![y] }],
        vec![result1],
        Some(Label::Symbol("λ".to_string())),
    ).unwrap();
    
    // This edge's body would share x with the previous edge's body
    // Actually, let me reconsider - the body is computed from what's reachable
    // Let me make a clearer example
    
    g
}

/// UNSAFE Example 3 (clearer): Two binders with overlapping scope
/// Two λ edges whose bodies share a common subgraph
fn example_unsafe_shared_body_clear() -> BHyp {
    let mut g = BHyp::new();
    
    let shared = g.add_node();  // This node will be in body of BOTH binders
    let x = g.add_node();       // bound by first λ
    let y = g.add_node();       // bound by second λ
    let fx = g.add_node();      
    let gy = g.add_node();      
    let h_shared = g.add_node();
    let result1 = g.add_node(); 
    let result2 = g.add_node(); 
    
    // f(x)
    g.add_edge(
        vec![SourceWithBinding { source: x, bound: vec![] }],
        vec![fx],
        Some(Label::Symbol("f".to_string())),
    ).unwrap();
    
    // g(y) 
    g.add_edge(
        vec![SourceWithBinding { source: y, bound: vec![] }],
        vec![gy],
        Some(Label::Symbol("g".to_string())),
    ).unwrap();
    
    // h(shared) - shared node used by both
    g.add_edge(
        vec![SourceWithBinding { source: shared, bound: vec![] }],
        vec![h_shared],
        Some(Label::Symbol("h".to_string())),
    ).unwrap();
    
    // First λ: binds x, body includes shared via some connection
    g.add_edge(
        vec![
            SourceWithBinding { source: fx, bound: vec![x] },
            SourceWithBinding { source: h_shared, bound: vec![] },
        ],
        vec![result1],
        Some(Label::Symbol("λ".to_string())),
    ).unwrap();
    
    // Second λ: binds y, body ALSO includes shared - UNSAFE!
    g.add_edge(
        vec![
            SourceWithBinding { source: gy, bound: vec![y] },
            SourceWithBinding { source: h_shared, bound: vec![] },
        ],
        vec![result2],
        Some(Label::Symbol("λ".to_string())),
    ).unwrap();
    
    g
}

/// UNSAFE Example 4: Bound variable is a target
/// Violates condition 3: "no bound vertex is a target"
fn example_unsafe_bound_is_target() -> BHyp {
    let mut g = BHyp::new();
    
    let x = g.add_node();      // This will be both bound AND a target - UNSAFE
    let input = g.add_node();  
    let result = g.add_node(); 
    
    // f produces x as output (x is a TARGET)
    g.add_edge(
        vec![SourceWithBinding { source: input, bound: vec![] }],
        vec![x],  // x is target!
        Some(Label::Symbol("f".to_string())),
    ).unwrap();
    
    // λ binds x (x is BOUND) - but x is already a target! UNSAFE!
    g.add_edge(
        vec![SourceWithBinding { source: x, bound: vec![x] }],
        vec![result],
        Some(Label::Symbol("λ".to_string())),
    ).unwrap();
    
    g
}

/// UNSAFE Example 5: Leaking - body output connected to bound vertex shared elsewhere
/// Violates condition 4 about leaking
fn example_unsafe_leaking_shared_source() -> BHyp {
    let mut g = BHyp::new();
    
    let x = g.add_node();      // bound variable
    let y = g.add_node();      // will be problematic
    let fx = g.add_node();     
    let gy = g.add_node();     
    let result = g.add_node(); 
    let external = g.add_node();
    
    // f(x)
    g.add_edge(
        vec![SourceWithBinding { source: x, bound: vec![] }],
        vec![fx],
        Some(Label::Symbol("f".to_string())),
    ).unwrap();
    
    // g(y) - y is used as source
    g.add_edge(
        vec![SourceWithBinding { source: y, bound: vec![] }],
        vec![gy],
        Some(Label::Symbol("g".to_string())),
    ).unwrap();
    
    // λ binds x, with body that includes y as source to fx
    // and y is connected to bound vertex x somehow
    g.add_edge(
        vec![SourceWithBinding { source: fx, bound: vec![x] }],
        vec![result],
        Some(Label::Symbol("λ".to_string())),
    ).unwrap();
    
    // External edge also uses x - this creates a leak!
    g.add_edge(
        vec![SourceWithBinding { source: x, bound: vec![] }],
        vec![external],
        Some(Label::Symbol("leak".to_string())),
    ).unwrap();
    
    g
}

/// Safe example with metavariable: M[x] where x is properly bound
fn example_safe_metavariable() -> BHyp {
    let mut g = BHyp::new();
    
    let x = g.add_node();      // bound variable
    let mx = g.add_node();     // M[x] result  
    let result = g.add_node(); // λx.M[x] result
    
    // Metavariable M applied to x
    g.add_edge(
        vec![SourceWithBinding { source: x, bound: vec![] }],
        vec![mx],
        Some(Label::Meta("M".to_string(), 1)),
    ).unwrap();
    
    // λx.M[x]
    g.add_edge(
        vec![SourceWithBinding { source: mx, bound: vec![x] }],
        vec![result],
        Some(Label::Symbol("λ".to_string())),
    ).unwrap();
    
    g
}

/// Paper Example: Figure from the paper showing a safe hypergraph
/// This represents the term structure from the paper's examples
fn example_paper_safe() -> BHyp {
    let mut g = BHyp::new();
    
    // Create a structure similar to paper's Figure 2
    let v1 = g.add_node();
    let v2 = g.add_node();
    let v3 = g.add_node();
    let v4 = g.add_node();
    
    // Edge e1: simple edge
    g.add_edge(
        vec![SourceWithBinding { source: v1, bound: vec![] }],
        vec![v2],
        Some(Label::Symbol("e₁".to_string())),
    ).unwrap();
    
    // Edge e2: with binding
    g.add_edge(
        vec![SourceWithBinding { source: v2, bound: vec![v1] }],
        vec![v3],
        Some(Label::Symbol("e₂".to_string())),
    ).unwrap();
    
    // Edge e3: continuation
    g.add_edge(
        vec![SourceWithBinding { source: v3, bound: vec![] }],
        vec![v4],
        Some(Label::Symbol("e₃".to_string())),
    ).unwrap();
    
    g
}

/// Paper Example: Unsafe hypergraph from paper
/// Demonstrates violation of safety conditions
fn example_paper_unsafe() -> BHyp {
    let mut g = BHyp::new();
    
    let v1 = g.add_node();
    let v2 = g.add_node();
    let v3 = g.add_node();
    let v4 = g.add_node();
    
    // Create an unsafe configuration where v1 is bound by two edges
    g.add_edge(
        vec![SourceWithBinding { source: v1, bound: vec![] }],
        vec![v2],
        Some(Label::Symbol("e₁".to_string())),
    ).unwrap();
    
    g.add_edge(
        vec![SourceWithBinding { source: v2, bound: vec![v1] }],
        vec![v3],
        Some(Label::Symbol("e₂".to_string())),
    ).unwrap();
    
    // Second edge also tries to bind v1 - UNSAFE!
    g.add_edge(
        vec![SourceWithBinding { source: v3, bound: vec![v1] }],
        vec![v4],
        Some(Label::Symbol("e₃".to_string())),
    ).unwrap();
    
    g
}

// ============================================================================
// EXPORT FUNCTIONS
// ============================================================================

/// Export example to DOT file
fn export_bhyp(name: &str, bhyp: &BHyp, labelled: bool) {
    let dot = if labelled {
        bhyp_to_dot_labelled(bhyp)
    } else {
        bhyp_to_dot_unlabelled(bhyp)
    };

    let filename = format!("{}.dot", name);
    match File::create(&filename) {
        Ok(mut f) => {
            if let Err(e) = f.write_all(dot.as_bytes()) {
                eprintln!("Failed to write {}: {}", filename, e);
            } else {
                println!("✓ Exported {} to {}", name, filename);
            }
        }
        Err(e) => eprintln!("Failed to create {}: {}", filename, e),
    }
}

/// Export BHyp_with_interface to DOT file (both detailed and cospan views)
fn export_bhyp_with_interface(name: &str, bhyp_i: &BHyp_with_interface) {
    // Detailed view
    let dot = bhyp_with_interface_to_dot_labelled(bhyp_i);
    let filename = format!("{}_detailed.dot", name);
    match File::create(&filename) {
        Ok(mut f) => {
            if let Err(e) = f.write_all(dot.as_bytes()) {
                eprintln!("Failed to write {}: {}", filename, e);
            } else {
                println!("✓ Exported {} detailed view to {}", name, filename);
            }
        }
        Err(e) => eprintln!("Failed to create {}: {}", filename, e),
    }

    // Cospan view
    let dot = bhyp_with_interface_cospan_to_dot(bhyp_i, &DotConfig::default());
    let filename = format!("{}_cospan.dot", name);
    match File::create(&filename) {
        Ok(mut f) => {
            if let Err(e) = f.write_all(dot.as_bytes()) {
                eprintln!("Failed to write {}: {}", filename, e);
            } else {
                println!("✓ Exported {} cospan view to {}", name, filename);
            }
        }
        Err(e) => eprintln!("Failed to create {}: {}", filename, e),
    }
}

/// Export morphism to DOT file
fn export_morphism(name: &str, morphism: &BHypMorphism) {
    let dot = morphism_to_dot_labelled(morphism);
    let filename = format!("{}_morphism.dot", name);
    match File::create(&filename) {
        Ok(mut f) => {
            if let Err(e) = f.write_all(dot.as_bytes()) {
                eprintln!("Failed to write {}: {}", filename, e);
            } else {
                println!("✓ Exported {} morphism diagram to {}", name, filename);
            }
        }
        Err(e) => eprintln!("Failed to create {}: {}", filename, e),
    }
}

/// Export pushout example to DOT file
fn export_pushout_example(name: &str, c: &BHyp, a: &BHyp, b: &BHyp, _pushout_obj: &BHyp) {
    use hypergraph_dpo::categorical::pushout;
    
    // Recompute to get the morphism mappings for visualization
    let mut f_nodes: HashMap<NodeId, NodeId> = HashMap::new();
    f_nodes.insert(NodeId(0), NodeId(0));
    let f_edges: HashMap<EdgeId, EdgeId> = HashMap::new();
    
    let mut g_nodes: HashMap<NodeId, NodeId> = HashMap::new();
    g_nodes.insert(NodeId(0), NodeId(0));
    let g_edges: HashMap<EdgeId, EdgeId> = HashMap::new();
    
    let pushout_result = pushout(c, a, b, &f_nodes, &f_edges, &g_nodes, &g_edges);
    
    let dot = pushout_to_dot_labelled(c, a, b, &pushout_result);
    let filename = format!("{}_pushout.dot", name);
    match File::create(&filename) {
        Ok(mut f) => {
            if let Err(e) = f.write_all(dot.as_bytes()) {
                eprintln!("Failed to write {}: {}", filename, e);
            } else {
                println!("✓ Exported {} pushout diagram to {}", name, filename);
            }
        }
        Err(e) => eprintln!("Failed to create {}: {}", filename, e),
    }
}

/// Export DPO example to DOT file
fn export_dpo_example(name: &str, lhs: &BHyp, interface: &BHyp, rhs: &BHyp, result: &BHyp) {
    use hypergraph_dpo::categorical::DPOResult;
    
    // Create a minimal DPOResult for visualization
    let dpo_result = DPOResult {
        result: result.clone(),
        right_to_result_nodes: HashMap::new(),
        right_to_result_edges: HashMap::new(),
        complement: BHyp::new(),
    };
    
    let dot = dpo_to_dot_labelled(lhs, interface, rhs, result, &dpo_result);
    let filename = format!("{}_dpo.dot", name);
    match File::create(&filename) {
        Ok(mut f) => {
            if let Err(e) = f.write_all(dot.as_bytes()) {
                eprintln!("Failed to write {}: {}", filename, e);
            } else {
                println!("✓ Exported {} DPO diagram to {}", name, filename);
            }
        }
        Err(e) => eprintln!("Failed to create {}: {}", filename, e),
    }
}

/// Export a safety example with check results
fn export_safety_example(name: &str, bhyp: &BHyp, expected_safe: bool) {
    // Export the graph
    export_bhyp(name, bhyp, true);
    
    // Check safety
    let result = check_safety(bhyp);
    
    let is_safe = result.is_ok();
    let status = if is_safe { "SAFE ✓" } else { "UNSAFE ✗" };
    let expected = if expected_safe { "expected safe" } else { "expected unsafe" };
    let match_status = if is_safe == expected_safe { "✓" } else { "MISMATCH!" };
    
    println!("  Safety check: {} ({}) {}", status, expected, match_status);
    
    if let Err(violations) = result {
        for v in violations {
            println!("    - {}", format_violation(&v));
        }
    }
}

/// Format a safety violation for display
fn format_violation(v: &SafetyViolation) -> String {
    match v {
        SafetyViolation::BoundToMultipleEdges { node, edges } => {
            format!("Node {:?} bound by multiple edges: {:?}", node, edges)
        }
        SafetyViolation::BoundMultipleTimes { node, edge, count } => {
            format!("Node {:?} bound {} times by edge {:?}", node, count, edge)
        }
        SafetyViolation::SharedBody { edge1, edge2, shared_nodes } => {
            format!("Edges {:?} and {:?} share body nodes: {:?}", edge1, edge2, shared_nodes)
        }
        SafetyViolation::BoundNodeIsTarget { node, binding_edge, target_edge } => {
            format!("Node {:?} is bound by {:?} but is target of {:?}", node, binding_edge, target_edge)
        }
        SafetyViolation::LeakingSharedSource { node, body_edge, external_edge } => {
            format!("Leaking: node {:?} in body of {:?} also source of {:?}", node, body_edge, external_edge)
        }
        SafetyViolation::LeakingInOutput { node, edge } => {
            format!("Leaking: body output {:?} of edge {:?} is in output interface", node, edge)
        }
    }
}

fn print_usage(prog: &str) {
    eprintln!("Usage: {} [all|simple|lambda|curried|metavar|interface|morphism|pushout|dpo|safety]", prog);
    eprintln!();
    eprintln!("Basic examples:");
    eprintln!("  {} simple      - Simple function application f(x)", prog);
    eprintln!("  {} lambda      - Lambda abstraction λx.f(x)", prog);
    eprintln!("  {} curried     - Curried function λx.λy.f(x,y)", prog);
    eprintln!("  {} metavar     - Example with metavariable", prog);
    eprintln!("  {} interface   - Hypergraph with interface (cospan)", prog);
    eprintln!();
    eprintln!("Categorical examples:");
    eprintln!("  {} morphism    - Morphism between two hypergraphs", prog);
    eprintln!("  {} pushout     - Pushout square construction", prog);
    eprintln!("  {} dpo         - Double Pushout graph rewriting", prog);
    eprintln!();
    eprintln!("Safety examples (from paper Definition 3.7):");
    eprintln!("  {} safety      - All safety examples with checks", prog);
    eprintln!();
    eprintln!("  {} all         - Run all examples", prog);
}

fn run_safety_examples() {
    println!("\n### SAFETY EXAMPLES (Definition 3.7) ###\n");
    
    // Safe examples
    println!("=== SAFE EXAMPLES ===\n");
    
    println!("1. Simple lambda λx.f(x):");
    let g = example_safe_lambda();
    println!("{}", g);
    export_safety_example("safety_safe_lambda", &g, true);
    
    println!("\n2. Nested lambda λx.λy.f(x,y):");
    let g = example_safe_nested_lambda();
    println!("{}", g);
    export_safety_example("safety_safe_nested", &g, true);
    
    println!("\n3. Simple composition f(g(x)):");
    let g = example_safe_composition();
    println!("{}", g);
    export_safety_example("safety_safe_composition", &g, true);
    
    println!("\n4. Safe metavariable λx.M[x]:");
    let g = example_safe_metavariable();
    println!("{}", g);
    export_safety_example("safety_safe_metavar", &g, true);
    
    println!("\n5. Paper safe example:");
    let g = example_paper_safe();
    println!("{}", g);
    export_safety_example("safety_paper_safe", &g, true);
    
    // Unsafe examples
    println!("\n=== UNSAFE EXAMPLES ===\n");
    
    println!("1. UNSAFE: Variable bound by multiple edges (violates condition 1):");
    let g = example_unsafe_multiple_binders();
    println!("{}", g);
    export_safety_example("safety_unsafe_multiple_binders", &g, false);
    
    println!("\n2. UNSAFE: Variable bound twice by same edge (violates condition 1):");
    let g = example_unsafe_bound_twice();
    println!("{}", g);
    export_safety_example("safety_unsafe_bound_twice", &g, false);
    
    println!("\n3. UNSAFE: Shared body between edges (violates condition 2):");
    let g = example_unsafe_shared_body_clear();
    println!("{}", g);
    export_safety_example("safety_unsafe_shared_body", &g, false);
    
    println!("\n4. UNSAFE: Bound variable is target (violates condition 3):");
    let g = example_unsafe_bound_is_target();
    println!("{}", g);
    export_safety_example("safety_unsafe_bound_target", &g, false);
    
    println!("\n5. UNSAFE: Leaking shared source (violates condition 4):");
    let g = example_unsafe_leaking_shared_source();
    println!("{}", g);
    export_safety_example("safety_unsafe_leaking", &g, false);
    
    println!("\n6. UNSAFE: Paper unsafe example (bound by multiple edges):");
    let g = example_paper_unsafe();
    println!("{}", g);
    export_safety_example("safety_paper_unsafe", &g, false);
    
    println!("\n✓ Safety examples complete!");
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let prog = args.get(0).map(|s| s.as_str()).unwrap_or("bhyp-vis");
    let example = args.get(1).map(|s| s.as_str()).unwrap_or("all");

    match example {
        "simple" => {
            let bhyp = example_simple_function();
            println!("\n=== Simple Function Application: f(x) ===");
            println!("{}", bhyp);
            export_bhyp("example_simple", &bhyp, true);
        }
        "lambda" => {
            let bhyp = example_lambda();
            println!("\n=== Lambda Abstraction: λx.f(x) ===");
            println!("{}", bhyp);
            export_bhyp("example_lambda", &bhyp, true);
        }
        "curried" => {
            let bhyp = example_curried();
            println!("\n=== Curried Function: λx.λy.f(x,y) ===");
            println!("{}", bhyp);
            export_bhyp("example_curried", &bhyp, true);
        }
        "metavar" => {
            let bhyp = example_with_metavariable();
            println!("\n=== Example with Metavariable ===");
            println!("{}", bhyp);
            export_bhyp("example_metavar", &bhyp, true);
        }
        "interface" => {
            let bhyp_i = example_with_interface();
            println!("\n=== Hypergraph with Interface (Cospan) ===");
            println!("{}", bhyp_i);
            export_bhyp_with_interface("example_interface", &bhyp_i);
        }
        "morphism" => {
            let (domain, codomain) = example_morphism();
            
            // Create morphism within this scope
            let mut on_nodes: HashMap<NodeId, NodeId> = HashMap::new();
            on_nodes.insert(NodeId(0), NodeId(0));
            on_nodes.insert(NodeId(1), NodeId(1));
            
            let mut on_edges: HashMap<EdgeId, EdgeId> = HashMap::new();
            on_edges.insert(EdgeId(0), EdgeId(0));
            
            let morphism = BHypMorphism::new(&domain, &codomain, on_nodes, on_edges)
                .expect("Failed to create morphism");
            
            println!("\n=== Categorical Example: Morphism ===");
            println!("Domain:");
            println!("{}", domain);
            println!("\nCodomain:");
            println!("{}", codomain);
            println!("\nMorphism: {} → {} (injective: {})",
                domain.nodes().len(), codomain.nodes().len(),
                morphism.is_monomorphism()
            );
            export_morphism("example_morphism", &morphism);
            export_bhyp("example_morphism_domain", &domain, true);
            export_bhyp("example_morphism_codomain", &codomain, true);
        }
        "pushout" => {
            let (c, pushout_obj, a, b) = example_pushout();
            println!("\n=== Categorical Example: Pushout ===");
            println!("Common vertex C:");
            println!("{}", c);
            println!("\nFirst graph A:");
            println!("{}", a);
            println!("\nSecond graph B:");
            println!("{}", b);
            println!("\nPushout object P:");
            println!("{}", pushout_obj);
            export_pushout_example("example_pushout", &c, &a, &b, &pushout_obj);
            export_bhyp("example_pushout_a", &a, true);
            export_bhyp("example_pushout_b", &b, true);
            export_bhyp("example_pushout_result", &pushout_obj, true);
        }
        "dpo" => {
            let (lhs, result, rhs, host) = example_dpo_rewriting();
            println!("\n=== Categorical Example: DPO Rewriting ===");
            println!("Left-hand side (pattern to match):");
            println!("{}", lhs);
            println!("\nRight-hand side (replacement):");
            println!("{}", rhs);
            println!("\nHost graph (to be rewritten):");
            println!("{}", host);
            println!("\nResult after DPO rewriting:");
            println!("{}", result);
            export_dpo_example("example_dpo", &lhs, &rhs, &rhs, &result);
            export_bhyp("example_dpo_lhs", &lhs, true);
            export_bhyp("example_dpo_rhs", &rhs, true);
            export_bhyp("example_dpo_host", &host, true);
            export_bhyp("example_dpo_result", &result, true);
        }
        "safety" => {
            run_safety_examples();
        }
        "all" => {
            println!("Running all BHyp and Categorical visualization examples...\n");

            // === Basic BHyp Examples ===
            println!("\n### BASIC BHYP EXAMPLES ###\n");

            let bhyp = example_simple_function();
            println!("=== Simple Function Application: f(x) ===");
            println!("{}", bhyp);
            export_bhyp("example_simple", &bhyp, true);

            let bhyp = example_lambda();
            println!("\n=== Lambda Abstraction: λx.f(x) ===");
            println!("{}\n", bhyp);
            export_bhyp("example_lambda", &bhyp, true);

            let bhyp = example_curried();
            println!("\n=== Curried Function: λx.λy.f(x,y) ===");
            println!("{}\n", bhyp);
            export_bhyp("example_curried", &bhyp, true);

            let bhyp = example_with_metavariable();
            println!("\n=== Example with Metavariable ===");
            println!("{}\n", bhyp);
            export_bhyp("example_metavar", &bhyp, true);

            let bhyp_i = example_with_interface();
            println!("\n=== Hypergraph with Interface (Cospan) ===");
            println!("{}\n", bhyp_i);
            export_bhyp_with_interface("example_interface", &bhyp_i);

            // === Categorical Examples ===
            println!("\n\n### CATEGORICAL EXAMPLES ###\n");

            let (domain, codomain) = example_morphism();
            
            // Create morphism within this scope
            let mut on_nodes: HashMap<NodeId, NodeId> = HashMap::new();
            on_nodes.insert(NodeId(0), NodeId(0));
            on_nodes.insert(NodeId(1), NodeId(1));
            
            let mut on_edges: HashMap<EdgeId, EdgeId> = HashMap::new();
            on_edges.insert(EdgeId(0), EdgeId(0));
            
            let morphism = BHypMorphism::new(&domain, &codomain, on_nodes, on_edges)
                .expect("Failed to create morphism");
            
            println!("=== Categorical Example: Morphism ===");
            println!("Domain:");
            println!("{}", domain);
            println!("\nCodomain:");
            println!("{}", codomain);
            println!("\nMorphism properties: monomorphism={}", morphism.is_monomorphism());
            export_morphism("example_morphism", &morphism);
            export_bhyp("example_morphism_domain", &domain, true);
            export_bhyp("example_morphism_codomain", &codomain, true);

            let (c, pushout_obj, a, b) = example_pushout();
            println!("\n=== Categorical Example: Pushout ===");
            println!("Common vertex C:");
            println!("{}", c);
            println!("\nFirst graph A: {} nodes, {} edges", a.nodes().len(), a.edges().len());
            println!("Second graph B: {} nodes, {} edges", b.nodes().len(), b.edges().len());
            println!("Pushout object P: {} nodes, {} edges", pushout_obj.nodes().len(), pushout_obj.edges().len());
            export_pushout_example("example_pushout", &c, &a, &b, &pushout_obj);
            export_bhyp("example_pushout_a", &a, true);
            export_bhyp("example_pushout_b", &b, true);
            export_bhyp("example_pushout_result", &pushout_obj, true);

            let (lhs, result, rhs, host) = example_dpo_rewriting();
            println!("\n=== Categorical Example: DPO Rewriting ===");
            println!("Left-hand side: {} nodes, {} edges", lhs.nodes().len(), lhs.edges().len());
            println!("Right-hand side: {} nodes, {} edges", rhs.nodes().len(), rhs.edges().len());
            println!("Host graph: {} nodes, {} edges", host.nodes().len(), host.edges().len());
            println!("Result: {} nodes, {} edges", result.nodes().len(), result.edges().len());
            export_dpo_example("example_dpo", &lhs, &rhs, &rhs, &result);
            export_bhyp("example_dpo_lhs", &lhs, true);
            export_bhyp("example_dpo_rhs", &rhs, true);
            export_bhyp("example_dpo_host", &host, true);
            export_bhyp("example_dpo_result", &result, true);

            // === Safety Examples ===
            run_safety_examples();

            println!("\n✓ All examples exported successfully!");
        }
        _ => {
            eprintln!("Unknown example: {}", example);
            print_usage(prog);
        }
    }
}