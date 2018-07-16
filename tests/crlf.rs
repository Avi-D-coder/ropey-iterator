//! Randomized tests to try to catch crlf seam errors.

extern crate rand;
extern crate ropey;

use rand::Rng;
use ropey::Rope;

#[test]
fn crlf_inserts() {
    let mut rng = rand::thread_rng();
    let mut tree = Rope::new();

    // Do a bunch of random incoherent inserts of CRLF
    // pairs.
    for _ in 0..(1 << 11) {
        let len = tree.len_chars().max(1);
        tree.insert(rng.gen::<usize>() % len, "\r\n\r\n");
        tree.insert(rng.gen::<usize>() % len, "\n\r\n\r");
        tree.insert(rng.gen::<usize>() % len, "\r\n\r\n");
        tree.insert(rng.gen::<usize>() % len, "\n\r\n\r");
        tree.insert(rng.gen::<usize>() % len, "\r\n\r\n");
        tree.insert(rng.gen::<usize>() % len, "\n\r\n\r");
        tree.insert(rng.gen::<usize>() % len, "\r\n\r\n");
        tree.insert(rng.gen::<usize>() % len, "\n\r\n\r");
        tree.insert(rng.gen::<usize>() % len, "\r\n\r\n");
        tree.insert(rng.gen::<usize>() % len, "\n\r\n\r");
        tree.insert(rng.gen::<usize>() % len, "\r\n\r\n");
        tree.insert(rng.gen::<usize>() % len, "\n\r\n\r");

        // Make sure the tree is sound
        tree.assert_integrity();
        tree.assert_invariants();
    }
}

#[test]
fn crlf_removals() {
    let mut rng = rand::thread_rng();
    let mut tree = Rope::new();

    // Build tree.
    for _ in 0..(1 << 11) {
        let len = tree.len_chars().max(1);
        tree.insert(rng.gen::<usize>() % len, "\r\n\r\n\r\n\r\n\r\n\r\n\r\n\r\n\r\n\r\n\r\n\r\n\r\n\r\n\r\n\r\n\r\n\r\n\r\n\r\n\r\n\r\n\r\n\r\n\r\n\r\n\r\n\r\n\r\n\r\n\r\n\r\n\r\n\r\n\r\n\r");
    }

    // Do a bunch of random incoherent removals
    for _ in 0..(1 << 10) {
        let start = rng.gen::<usize>() % tree.len_chars().max(1);
        let end = (start + 5).min(tree.len_chars());
        tree.remove(start..end);

        let start = rng.gen::<usize>() % tree.len_chars().max(1);
        let end = (start + 6).min(tree.len_chars());
        tree.remove(start..end);

        // Make sure the tree is sound
        tree.assert_integrity();
        tree.assert_invariants();
    }
}