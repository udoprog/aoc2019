use aoc2019::*;

#[derive(Debug, Clone, Copy)]
enum Step {
    Up(i64),
    Down(i64),
    Left(i64),
    Right(i64),
}

impl Step {
    fn step(self, (x, y): (i64, i64)) -> Box<dyn Iterator<Item = (i64, i64)>> {
        match self {
            Self::Up(n) => Box::new(((y - n)..=(y - 1)).rev().map(move |y| (x, y))),
            Self::Down(n) => Box::new(((y + 1)..=(y + n)).map(move |y| (x, y))),
            Self::Left(n) => Box::new(((x - n)..=(x - 1)).rev().map(move |x| (x, y))),
            Self::Right(n) => Box::new(((x + 1)..=(x + n)).map(move |x| (x, y))),
        }
    }

    /// Decode the given line of input.
    fn decode(line: &str) -> Vec<Self> {
        let mut out = Vec::new();

        for p in line.split(',') {
            let p = p.trim();

            if p.is_empty() {
                continue;
            }

            let (d, n) = p.split_at(1);

            let n = match str::parse(n) {
                Ok(n) => n,
                Err(..) => continue,
            };

            out.push(match d {
                "U" => Self::Up(n),
                "D" => Self::Down(n),
                "L" => Self::Left(n),
                "R" => Self::Right(n),
                o => panic!("unsupported direction: {}", o),
            })
        }

        out
    }
}

fn solve<S>(wires: Vec<Vec<Step>>, solver: S) -> u64
where
    S: Fn((i64, i64), u64, u64) -> u64,
{
    let mut path = HashMap::new();

    let origin = (0, 0);

    let mut distance = 0;
    let mut p = origin;

    for wire in wires[0].iter().copied() {
        for n in wire.step(p) {
            distance += 1;
            path.insert(n, distance);
            p = n;
        }
    }

    let mut min = std::u64::MAX;

    let mut to_distance = 0;
    let mut p = origin;

    for wire in wires[1].iter().copied() {
        for n in wire.step(p) {
            to_distance += 1;

            if let Some(from_distance) = path.get(&n).copied() {
                let d = solver(n, from_distance, to_distance);

                if d < min {
                    min = d;
                }
            }

            p = n;
        }
    }

    min
}

/// Calculate the manhattan distance from `a` to `b`.
fn manhattan_distance(a: (i64, i64), b: (i64, i64)) -> u64 {
    (i64::abs(a.0 - b.0) + i64::abs(a.1 - b.1)) as u64
}

fn part1(p: (i64, i64), _: u64, _: u64) -> u64 {
    manhattan_distance(p, (0, 0))
}

fn part2(_: (i64, i64), from_distance: u64, to_distance: u64) -> u64 {
    from_distance + to_distance
}

fn main() -> Result<()> {
    let test1 = input_str!("day3t1.txt")
        .lines()
        .map(Step::decode)
        .collect::<Vec<_>>();

    let test2 = input_str!("day3t2.txt")
        .lines()
        .map(Step::decode)
        .collect::<Vec<_>>();

    let real = input_str!("day3.txt")
        .lines()
        .map(Step::decode)
        .collect::<Vec<_>>();

    assert_eq!(159, solve(test1.clone(), part1));
    assert_eq!(135, solve(test2.clone(), part1));
    assert_eq!(5357, solve(real.clone(), part1));

    assert_eq!(610, solve(test1.clone(), part2));
    assert_eq!(410, solve(test2.clone(), part2));
    assert_eq!(101956, solve(real.clone(), part2));
    Ok(())
}
