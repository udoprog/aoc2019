use aoc2019::*;

fn part1(masses: &[u64]) -> u64 {
    masses.iter().copied().map(|m| m / 3 - 2).sum()
}

fn part2(masses: &[u64]) -> u64 {
    let mut masses = masses.to_vec();

    let mut total = 0;

    while let Some(m) = masses.pop() {
        let fuel = m / 3;

        if let Some(input) = fuel.checked_sub(2) {
            total += input;
            masses.push(input);
        }
    }

    total
}

fn main() -> Result<(), Error> {
    let masses = columns!(input!("day1.txt"), char::is_whitespace, u64);
    assert_eq!(3303995, part1(&masses));
    assert_eq!(4953118, part2(&masses));
    Ok(())
}
