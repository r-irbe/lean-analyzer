//! crates/lean-analyzer/tests/test_real_ilean_scan.rs
//! Integration test and zero-copy mmap throughput benchmark for BatchILeanScanner.
//! Strict 7-bit ASCII only (INV-001).

use lean_analyzer::batch_scanner::BatchILeanScanner;
use std::path::Path;
use std::time::Instant;

#[test]
fn test_corpus_ilean_scan_benchmark() {
    let p1 = Path::new("docs/easci/lean/.lake/build/lib/lean/EASCI");
    let p2 = Path::new("../../docs/easci/lean/.lake/build/lib/lean/EASCI");
    let p3 = Path::new("tests/fixtures/ilean");
    let p4 = Path::new("crates/lean-analyzer/tests/fixtures/ilean");
    let ir_dir = if p1.exists() {
        p1
    } else if p2.exists() {
        p2
    } else if p3.exists() {
        p3
    } else if p4.exists() {
        p4
    } else {
        eprintln!("Corpus lib/lean dir does not exist, skipping real scan test.");
        return;
    };

    let mut scanner = BatchILeanScanner::new();
    let start = Instant::now();
    let scanned = scanner
        .scan_directory(ir_dir)
        .expect("Scan directory should succeed");
    let elapsed = start.elapsed();

    println!(
        "BatchILeanScanner: Scanned {} .ilean files in {:?}",
        scanned, elapsed
    );
    println!("Total indexed symbols: {}", scanner.total_symbols());

    assert!(scanned > 0, "Should have scanned at least one .ilean file");
    assert!(scanner.total_symbols() > 0, "Should have indexed symbols");
    assert!(scanner.total_modules() > 0, "Should have indexed modules");

    let largest = scanner.largest_module();
    assert!(largest.is_some(), "Should find largest module");
    if let Some((mod_name, count)) = largest {
        println!("Largest module: {} ({} declarations)", mod_name, count);
        assert!(count > 0);
    }

    let prefix_res = scanner.search_by_prefix("EASCI.");
    println!("Declarations starting with 'EASCI.': {}", prefix_res.len());
}
