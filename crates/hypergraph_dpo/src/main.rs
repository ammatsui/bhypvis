

use std::env;
use std::fs::File;
use std::io::Write;

use hypergraph_dpo::bhyp::{BHyp, BHyp_with_interface, Label, Signature, SourceWithBinding};
use hypergraph_dpo::visualization::{
    bhyp_to_dot_labeled, bhyp_to_dot_unlabeled, bhyp_with_interface_to_dot_labeled,
    bhyp_with_interface_cospan_to_dot, DotConfig,
};

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

/// Export example to DOT file
fn export_bhyp(name: &str, bhyp: &BHyp, labeled: bool) {
    let dot = if labeled {
        bhyp_to_dot_labeled(bhyp)
    } else {
        bhyp_to_dot_unlabeled(bhyp)
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
    let dot = bhyp_with_interface_to_dot_labeled(bhyp_i);
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

fn print_usage(prog: &str) {
    eprintln!("Usage: {} [all|simple|lambda|curried|metavar|interface]", prog);
    eprintln!();
    eprintln!("Examples:");
    eprintln!("  {} simple      - Simple function application f(x)", prog);
    eprintln!("  {} lambda      - Lambda abstraction λx.f(x)", prog);
    eprintln!("  {} curried     - Curried function λx.λy.f(x,y)", prog);
    eprintln!("  {} metavar     - Example with metavariable", prog);
    eprintln!("  {} interface   - Hypergraph with interface (cospan)", prog);
    eprintln!("  {} all         - Run all examples", prog);
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
        "all" => {
            println!("Running all BHyp visualization examples...\n");

            let bhyp = example_simple_function();
            println!("=== Simple Function Application: f(x) ===");
            println!("{}\n", bhyp);
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

            println!("\n✓ All examples exported successfully!");
        }
        _ => {
            eprintln!("Unknown example: {}", example);
            print_usage(prog);
        }
    }
}