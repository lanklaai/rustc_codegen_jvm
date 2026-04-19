fn sum(values: &[i32]) -> i32 {
    values.iter().copied().sum()
}

fn main() {
    let total = sum(&[1, 2, 3, 4]);
    assert!(total == 10, "unexpected sum");
}
