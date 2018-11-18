extern crate lz_interval_tree_clock;

use lz_interval_tree_clock::Stamp;

fn main() {
    let start = Stamp::seed();

    let (left, right) = start.fork();

    let left = left.event();

    let right = right.event();

    let (left_left, left_right) = left.fork();
    let left_left = left_left.event();

    let right = right.event();

    let right = Stamp::join(&left_right, &right).unwrap();

    let (right_left, _) = right.fork();

    let end = Stamp::join(&left_left, &right_left).unwrap();

    let end = end.event();

    let expected_end = Stamp::seed();
    let expected_end = expected_end.event();
    let expected_end = expected_end.event();
    let (expected_end, _) = expected_end.fork();

    assert_eq!(end, expected_end);
}
