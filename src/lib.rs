pub use anyhow::{bail, format_err, Context, Error, Result};
pub use chrono::Timelike;
pub use hashbrown::*;
pub use itertools::Itertools;
pub use nalgebra as na;
pub use num::{BigInt, BigUint};
pub use std::collections::{btree_map, btree_set, BTreeMap, BTreeSet, VecDeque};
pub use std::io::{BufRead, BufReader};
use std::ops;
pub use std::str;
pub use thiserror::Error;

/// Get the input as a string.
#[macro_export]
macro_rules! input_str {
    ($name:expr) => {
        include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/input/", $name))
    };
}

/// Load an input file.
#[macro_export]
macro_rules! input {
    ($name:expr) => {
        std::io::Cursor::new(input_str!($name))
    };
}

/// Read input as a long set of columns.
///
/// # Examples
///
/// Parsing different lines in different ways:
///
/// ```rust
/// use aoc2019::*;
///
/// fn main() -> Result<(), Error> {
///     let mut d = std::io::Cursor::new("1 2\n3\t4");
///     assert_eq!(columns!(d, char::is_whitespace, u32), vec![1, 2, 3, 4]);
///     Ok(())
/// }
/// ```
#[macro_export]
macro_rules! columns {
    ($data:expr, $sep:expr, $ty:ty) => {{
        use std::io::Read;

        let mut buf = String::new();
        $data.read_to_string(&mut buf)?;
        buf.trim()
            .split($sep)
            .filter(|s| !s.is_empty())
            .map(str::parse)
            .collect::<Result<Vec<$ty>, _>>()?
    }};
}

/// Read and parse lines.
///
/// Builds an iterator out of the given specification that will attempt to parse columns from each
/// line and provide excellent diagnostics in case it can't.
///
/// # Examples
///
/// Parsing different lines in different ways:
///
/// ```rust
/// use aoc2019::*;
///
/// fn main() -> Result<(), Error> {
///     let mut d = std::io::Cursor::new("1 2\nfoo 4");
///
///     for line in lines!(&mut d, u32, u32).take(1) {
///         assert_eq!(line?, (1, 2));
///     }
///
///     for line in lines!(&mut d, String, u32).take(1) {
///         assert_eq!(line?, (String::from("foo"), 4));
///     }
///
///     Ok(())
/// }
/// ```
#[macro_export]
macro_rules! lines {
    ($data:expr, $($ty:ty),*) => {{
        struct Iter<R, N> {
            data: R,
            line: N,
            buf: String,
        }

        impl<R, N> Iterator for Iter<R, N> where R: std::io::BufRead, N: Iterator<Item = usize> {
            type Item = Result<($($ty,)*), Error>;

            fn next(&mut self) -> Option<Self::Item> {
                self.buf.clear();

                let size = match self.data.read_line(&mut self.buf) {
                    Err(e) => return Some(Err(Error::from(e))),
                    Ok(size) => size,
                };

                if size == 0 {
                    return None;
                }

                let mut cols = self.buf.split_whitespace();

                let line = match self.line.next() {
                    None => return Some(Err(format_err!("no more lines"))),
                    Some(line) => line,
                };

                let mut col = 1..;

                let out = ($({
                    match $crate::parse_column(stringify!($ty), line, &mut cols, &mut col) {
                        Err(e) => return Some(Err(e)),
                        Ok(d) => d,
                    }
                },)*);

                return Some(Ok(out));
            }
        }

        Iter {
            data: $data,
            line: 1..,
            buf: String::new(),
        }
    }}
}

/// Parse a single column with the given type.
pub fn parse_column<'a, T>(
    ty: &'static str,
    line: usize,
    mut it: impl Iterator<Item = &'a str>,
    mut col: impl Iterator<Item = usize>,
) -> Result<T, Error>
where
    T: std::str::FromStr,
    T::Err: std::fmt::Display,
{
    let col = match col.next() {
        Some(col) => col,
        None => bail!("no more columns"),
    };

    let d = it
        .next()
        .ok_or_else(|| format!("missing column"))
        .and_then(|p| str::parse::<T>(p).map_err(|e| format!("bad value `{}`: {}", p, e)))
        .map_err(|e| format_err!("bad `{}` on {}:{}: {}", ty, line, col, e))?;

    Ok(d)
}

/// Ignore input.
pub struct Skip;

impl std::str::FromStr for Skip {
    type Err = Error;

    fn from_str(_: &str) -> Result<Self, Self::Err> {
        Ok(Skip)
    }
}

/// Trim non-numeric parts.
pub struct Trim<T>(pub T);

impl<T> std::str::FromStr for Trim<T>
where
    T: std::str::FromStr,
{
    type Err = T::Err;

    fn from_str(input: &str) -> Result<Self, Self::Err> {
        T::from_str(input.trim_matches(|c| !char::is_numeric(c))).map(Trim)
    }
}

macro_rules! tuple {
    ($name:ident, $($ty:ident),*) => {
        #[derive(Debug)]
        pub struct $name<$($ty,)*>($(pub $ty,)*);

        impl<$($ty,)*> std::str::FromStr for $name<$($ty,)*>
        where
            $(
            $ty: std::str::FromStr,
            $ty::Err: 'static + Send + Sync + std::error::Error,
            )*
        {
            type Err = Error;

            fn from_str(s: &str) -> Result<Self, Self::Err> {
                let mut it = s.split(|c| !char::is_numeric(c)).filter(|s| s.trim() != "");

                Ok($name($({
                    let x = it.next().ok_or_else(|| format_err!("expected x"))?;
                    $ty::from_str(x)?
                },)*))
            }
        }
    }
}

// Decoded a pair of values.
tuple!(Pair, A, B);
// Decodes a triple of values.
tuple!(Triple, A, B, C);
tuple!(Tup4, A, B, C, D);
tuple!(Tup5, A, B, C, D, E);

/// A helper that helps calcualte a minimum and maximum value.
///
/// # Examples
///
/// ```rust
/// use aoc2019::MinMax;
///
/// let mut dx = MinMax::default();
///
/// assert_eq!(dx.delta(), None);
/// dx.sample(5);
/// assert_eq!(dx.delta(), Some(0));
/// dx.sample(3);
/// assert_eq!(dx.delta(), Some(2));
///
/// assert_eq!(dx.range_inclusive().collect::<Vec<_>>(), vec![3, 4, 5]);
/// ```
#[derive(Debug, Default, Clone)]
pub struct MinMax<Idx> {
    value: Option<(Idx, Idx)>,
}

impl<Idx> MinMax<Idx>
where
    Idx: Copy,
{
    /// Sample the value to put into the MinMax calculation.
    pub fn sample(&mut self, value: Idx)
    where
        Idx: PartialOrd,
    {
        self.value = match self.value.take() {
            Some((min, max)) => {
                let min = if value < min { value } else { min };
                let max = if value > max { value } else { max };
                Some((min, max))
            }
            None => Some((value, value)),
        };
    }

    /// Get a copy of the current min/max value.
    pub fn get(&self) -> Option<(Idx, Idx)> {
        self.value.clone()
    }

    /// Calculate the delta if the stored value is `Sub<Idx>`.
    pub fn delta(&self) -> Option<Idx>
    where
        Idx: ops::Sub<Idx, Output = Idx>,
    {
        self.value.clone().map(|(mn, mx)| mx - mn)
    }

    /// Calculates an inclusive range if there is one.
    ///
    /// # Panics
    ///
    /// Panics if there is no samples.
    pub fn range_inclusive(&self) -> ops::RangeInclusive<Idx> {
        self.value
            .clone()
            .map(|(mn, mx)| ops::RangeInclusive::new(mn, mx))
            .expect("no samples")
    }
}
