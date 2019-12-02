use aoc2019::*;
use std::convert::TryFrom;

mod address {
    //! Abstraction for dealing with addresses.
    //!
    //! This makes sure that functions which only expect to receive address
    //! clearly communicate it, and we can limit how it can be used by limiting
    //! the various implementations it provide.
    use std::{convert::TryFrom, fmt, num};

    /// The address at a given location.
    #[derive(Debug, Clone, Copy)]
    #[repr(transparent)]
    pub struct Address(u64);

    impl Address {
        pub fn checked_add(self, offset: u64) -> Option<Self> {
            Some(Address(self.0.checked_add(offset)?))
        }
    }

    impl From<u64> for Address {
        fn from(value: u64) -> Address {
            Address(value)
        }
    }

    impl TryFrom<Address> for usize {
        type Error = num::TryFromIntError;

        fn try_from(address: Address) -> Result<Self, Self::Error> {
            usize::try_from(address.0)
        }
    }

    impl fmt::Display for Address {
        fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(fmt, "{}", self.0)
        }
    }
}

use self::address::Address;

#[derive(Debug, Error)]
#[error("failed to get value from non-existant slot {0}")]
pub struct GetError(Address);

#[derive(Debug, Error)]
#[error("failed to set value in non-existant slot {0}")]
pub struct SetError(Address);

#[derive(Debug, Error)]
#[error("program counter overflowed")]
pub struct InstructionPointerOverflow;

#[derive(Debug, Error)]
#[error("bad operation: {0}")]
pub struct BadOperation(u64);

#[derive(Debug, Error)]
#[error("operation {0} + {1} overflowed")]
pub struct AddOverflow(u64, u64);

#[derive(Debug, Error)]
#[error("operation {0} * {1} overflowed")]
pub struct MulOverflow(u64, u64);

#[derive(Debug, Clone)]
pub struct Machine {
    ip: Address,
    memory: Vec<u64>,
}

impl Machine {
    /// Construct a new machine with the given memory.
    pub fn new(memory: Vec<u64>) -> Self {
        Self {
            ip: Address::from(0),
            memory,
        }
    }

    /// Run until completion (opcode 99).
    pub fn run(&mut self) -> Result<()> {
        loop {
            let op = self.get(self.ip)?;

            match op {
                1 => {
                    let a = self.ip_add(1)?;
                    let b = self.ip_add(2)?;
                    let c = self.ip_add(3)?;

                    let (a, b) = (self.get_deref(a)?, self.get_deref(b)?);
                    *self.get_deref_mut(c)? = a.checked_add(b).ok_or_else(|| AddOverflow(a, b))?;

                    self.ip = self.ip_add(4)?;
                }
                2 => {
                    let a = self.ip_add(1)?;
                    let b = self.ip_add(2)?;
                    let c = self.ip_add(3)?;

                    let (a, b) = (self.get_deref(a)?, self.get_deref(b)?);
                    *self.get_deref_mut(c)? = a.checked_mul(b).ok_or_else(|| MulOverflow(a, b))?;

                    self.ip = self.ip_add(4)?;
                }
                99 => break,
                o => return Err(BadOperation(o).into()),
            }
        }

        Ok(())
    }

    /// Get the value at memory slot `slot`.
    fn get(&self, address: impl Into<Address>) -> Result<u64, GetError> {
        let address = address.into();

        let i = match usize::try_from(address) {
            Ok(i) => i,
            Err(..) => return Err(GetError(address)),
        };

        self.memory.get(i).copied().ok_or_else(|| GetError(address))
    }

    /// Get the dereferenced value at slot `slot`.
    fn get_deref(&self, address: Address) -> Result<u64, GetError> {
        let address = Address::from(self.get(address)?);
        self.get(address)
    }

    /// Get the dereferenced mutable value at slot `slot`.
    fn get_deref_mut(&mut self, address: Address) -> Result<&mut u64, GetError> {
        let address = Address::from(self.get(address)?);
        self.get_mut(address)
    }

    /// Get a mutable value at memory slot `slot`.
    fn get_mut(&mut self, slot: Address) -> Result<&mut u64, GetError> {
        let i = match usize::try_from(slot) {
            Ok(i) => i,
            Err(..) => return Err(GetError(slot)),
        };

        self.memory.get_mut(i).ok_or_else(|| GetError(slot))
    }

    /// Set the value at position `p` to `value`.
    fn set(&mut self, address: impl Into<Address>, value: u64) -> Result<(), SetError> {
        let address = address.into();

        let i = match usize::try_from(address) {
            Ok(i) => i,
            Err(..) => return Err(SetError(address)),
        };

        if let Some(slot) = self.memory.get_mut(i) {
            *slot = value;
            return Ok(());
        }

        Err(SetError(address))
    }

    /// Add the given number to the program counter and return the result.
    fn ip_add(&self, offset: u64) -> Result<Address, InstructionPointerOverflow> {
        self.ip
            .checked_add(offset)
            .ok_or_else(|| InstructionPointerOverflow)
    }
}

fn part1(mut machine: Machine) -> Result<u64> {
    machine.set(1, 12)?;
    machine.set(2, 2)?;

    machine.run()?;

    Ok(machine.get(0)?)
}

fn part2(machine: Machine, needle: u64) -> Result<u64> {
    for noun in 0..100 {
        for verb in 0..100 {
            let mut machine = machine.clone();
            machine.set(1, noun)?;
            machine.set(2, verb)?;

            machine.run()?;

            if machine.get(0)? == needle {
                return Ok(100 * noun + verb);
            }
        }
    }

    bail!("no solution found for needle: {}", needle)
}

fn main() -> Result<()> {
    let opcodes = columns!(
        input!("day2.txt"),
        |c| char::is_whitespace(c) || c == ',',
        u64
    );

    let machine = Machine::new(opcodes.clone());

    assert_eq!(5110675, part1(machine.clone())?);
    assert_eq!(4847, part2(machine.clone(), 19690720)?);
    Ok(())
}
