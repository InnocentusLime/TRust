// total fn(int) -> int
fn test() -> int { 2 }

fn a(x : int) -> int {
    if x == 2 {
        let y = 5 * 2;
        b() * test() + x
    } else { 5 + test2() }
}

fn b() -> int {
    let x = 2 * (test() + 2);
    a(3)
}

fn test2() -> int { 4 }

fn c() { b(); }

// 'e fn('e fn() -> int) -> ()
fn f(x : fn() -> int) {}
