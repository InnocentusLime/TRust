// total fn(int, int) -> int
fn gcd(x : int, y : int) -> int {
    if x < 0 { gcd(-x, y) }
    else if y < 0 { gcd(x, -y) }
    else if x == 0 { y }
    else if y == 0 { x }
    else if x < y { gcd(x, y - x) }
    else { gcd(x - y, y) }
}
