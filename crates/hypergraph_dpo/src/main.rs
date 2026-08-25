use std::env;
use std::fs::File;
use std::io::Write;

use hypergraph_dpo::bhyp::{BHyp, Label, Signature, SourceWithBinding};

/// Export a BHyp to a simple Graphviz DOT string (nodes + edge boxes).
fn export_to_dot(h: &BHyp) -> String {
	let mut out = String::new();
	out.push_str("digraph BHyp {\n  rankdir=LR;\n  node [shape=circle];\n\n");

	// Nodes
	let mut nodes: Vec<_> = h.nodes().iter().cloned().collect();
	nodes.sort_by_key(|n| n.0);
	for n in nodes {
		out.push_str(&format!("  n{} [label=\"{}\"];\n", n.0, n.0));
	}
	out.push_str("\n  // edges as boxes\n");

	// Edges
	let mut edges: Vec<_> = h.edges().iter().cloned().collect();
	edges.sort_by_key(|e| e.0);
	for e in edges {
		let eid = e.0;
		let label_text = match h.get_label(e) {
			Some(Label::Symbol(s)) => s.clone(),
			Some(Label::Meta(nm, ar)) => format!("{}:{}", nm, ar),
			Some(Label::Lambda) => "λ".to_string(),
			Some(Label::None) | None => String::new(),
		};

		// Build a compact label including binding information
		let mut edge_lbl = label_text;
		if let Some(swbs) = h.get_sources_with_binding(e) {
			let parts: Vec<String> = swbs
				.iter()
				.map(|swb| {
					if swb.bound.is_empty() {
						format!("s{}", swb.source.0)
					} else {
						let bounds: Vec<String> = swb.bound.iter().map(|b| format!("n{}", b.0)).collect();
						format!("s{}[{}]", swb.source.0, bounds.join(","))
					}
				})
				.collect();
			if !parts.is_empty() {
				if !edge_lbl.is_empty() {
					edge_lbl = format!("{} | {}", edge_lbl, parts.join(" "));
				} else {
					edge_lbl = parts.join(" ");
				}
			}
		}

		out.push_str(&format!("  e{} [shape=box, label=\"{}\"];\n", eid, edge_lbl));

		// wire sources -> edge
		if let Some(swbs) = h.get_sources_with_binding(e) {
			for swb in swbs {
				out.push_str(&format!("  n{} -> e{};\n", swb.source.0, eid));
			}
		}

		// wire edge -> targets
		if let Some(targets) = h.get_targets(e) {
			for t in targets {
				out.push_str(&format!("  e{} -> n{};\n", eid, t.0));
			}
		}

		out.push_str("\n");
	}

	out.push_str("}\n");
	out
}

/// Simple example graph (no signature)
fn example_simple() -> BHyp {
	let mut g = BHyp::new();
	let n1 = g.add_node();
	let n2 = g.add_node();
	let n3 = g.add_node();

	g.add_edge(
		vec![SourceWithBinding {
			source: n1,
			bound: vec![],
		}],
		vec![n2, n3],
		Some(Label::Symbol("f".to_string())),
	)
	.unwrap();

	g
}

/// Example with a small signature and a lambda-like binding
fn example_lambda_with_signature() -> BHyp {
	let mut sig = Signature::new();
	sig.add_symbol("λ".to_string(), vec![1]);

	let mut g = BHyp::with_signature(sig);

	let x = g.add_node();
	let f_node = g.add_node();
	let lambda_out = g.add_node();

	g.add_edge(
		vec![SourceWithBinding {
			source: x,
			bound: vec![],
		}],
		vec![f_node],
		Some(Label::Symbol("f".to_string())),
	)
	.unwrap();

	g.add_edge(
		vec![SourceWithBinding {
			source: f_node,
			bound: vec![x],
		}],
		vec![lambda_out],
		Some(Label::Lambda),
	)
	.unwrap();

	g
}

fn usage(program: &str) {
	eprintln!("Usage: {} [simple|lambda] [out.dot]", program);
}

fn main() {
	let mut args: Vec<String> = env::args().collect();
	let prog = args.get(0).map(|s| s.as_str()).unwrap_or("bhyp-example");

	// Defaults
	let example = args.get(1).map(|s| s.as_str()).unwrap_or("simple");
	let out_path = args.get(2).map(|s| s.as_str()).unwrap_or("example.dot");

	let hyp = match example {
		"simple" => example_simple(),
		"lambda" => example_lambda_with_signature(),
		_ => {
			usage(prog);
			return;
		}
	};

	// Print a quick textual representation
	println!("{}", hyp);

	// Export DOT
	let dot = export_to_dot(&hyp);
	match File::create(out_path) {
		Ok(mut f) => {
			if let Err(e) = f.write_all(dot.as_bytes()) {
				eprintln!("Failed to write {}: {}", out_path, e);
			} else {
				println!("Wrote DOT to {}", out_path);
			}
		}
		Err(e) => eprintln!("Failed to create {}: {}", out_path, e),
	}
}

