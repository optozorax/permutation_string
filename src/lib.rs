use num_bigint::BigUint;
use thiserror::Error;

use std::collections::BTreeMap;
use std::convert::TryFrom;

#[derive(Debug, Clone, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PermutationString {
    pub string: String,
    pub permutation_size: usize,
}

#[derive(Debug, Clone, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PermutationInt {
    pub int: BigUint,
    pub permutation_size: usize,
}

#[derive(Debug, Clone, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PermutationIndex(pub Vec<usize>);

#[derive(Debug, Clone, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PermutationArray(pub Vec<usize>);

lazy_static::lazy_static! {
    static ref RADIX64_CHARS: Vec<u8> =
        (b'0'..=b'9')
        .chain(b'a'..=b'z')
        .chain(b'A'..=b'Z')
        .chain(std::iter::once(b'+'))
        .chain(std::iter::once(b'/'))
        .collect();

    static ref RADIX64_CHARS_INVERT: BTreeMap<char, usize> =
        ('0'..='9').zip(b'0'..=b'9')
        .chain(('a'..='z').zip(b'a'..=b'z'))
        .chain(('A'..='Z').zip(b'A'..=b'Z'))
        .chain(std::iter::once('+').zip(std::iter::once(b'+')))
        .chain(std::iter::once('/').zip(std::iter::once(b'/')))
        .map(|(c, u)| (c, RADIX64_CHARS.iter().position(|x| *x == u).unwrap()))
        .collect();
}

#[derive(Debug, Clone, Eq, Hash, Ord, PartialEq, PartialOrd, Error)]
pub enum PermutationError {
    #[error("wrong symbol in permutation string: `{0}`")]
    WrongSymbol(char),
    #[error("number is too big for provided size: `{0}`")]
    NumberIsTooBig(usize),
    #[error(
        "array isn't correct permutation index in position: `{index}`, with element: `{element}`"
    )]
    NotPermutationIndex { index: usize, element: usize },
    #[error(
        "array isn't correct permutation array in position: `{index}`, with element: `{element}`"
    )]
    NotPermutationArray { index: usize, element: usize },
}

impl PermutationInt {
    pub fn new(number: u64, permutation_size: usize) -> Self {
        PermutationInt {
            int: BigUint::from(number),
            permutation_size,
        }
    }
}

impl TryFrom<PermutationString> for PermutationInt {
    type Error = PermutationError;

    fn try_from(value: PermutationString) -> Result<Self, Self::Error> {
        let int = value
            .string
            .chars()
            .map(|x| {
                RADIX64_CHARS_INVERT
                    .get(&x)
                    .cloned()
                    .ok_or(PermutationError::WrongSymbol(x))
            })
            .collect::<Result<Vec<usize>, _>>()?
            .into_iter()
            .scan(BigUint::from(1u32), |state, value| {
                let old_state = state.clone();
                *state *= RADIX64_CHARS.len();
                Some(old_state * value)
            })
            .sum::<BigUint>();
        Ok(PermutationInt {
            int,
            permutation_size: value.permutation_size,
        })
    }
}

impl From<PermutationInt> for PermutationString {
    fn from(mut value: PermutationInt) -> Self {
        let mut string = if value.int == BigUint::from(0u32) {
            "0".to_owned()
        } else {
            String::new()
        };

        while value.int != BigUint::from(0u32) {
            string.push(char::from(
                RADIX64_CHARS[usize::try_from(value.int.clone() % RADIX64_CHARS.len()).unwrap()],
            ));
            value.int /= RADIX64_CHARS.len();
        }
        PermutationString {
            string,
            permutation_size: value.permutation_size,
        }
    }
}

impl TryFrom<PermutationInt> for PermutationIndex {
    type Error = PermutationError;

    fn try_from(value: PermutationInt) -> Result<Self, Self::Error> {
        let mut number = value.int;
        let mut result = Vec::new();
        for i in 1..=value.permutation_size {
            result.push(usize::try_from(number.clone() % i).unwrap());
            number /= i;
        }
        result.reverse();
        if number != BigUint::from(0u32) {
            Err(PermutationError::NumberIsTooBig(value.permutation_size))
        } else {
            Ok(PermutationIndex(result))
        }
    }
}

impl From<PermutationIndex> for PermutationInt {
    fn from(value: PermutationIndex) -> Self {
        PermutationInt {
            int: value
                .0
                .iter()
                .rev()
                .enumerate()
                .skip(1)
                .scan(BigUint::from(1u32), |state, (index, value)| {
                    *state *= index;
                    Some(state.clone() * value)
                })
                .sum::<BigUint>(),
            permutation_size: value.0.len(),
        }
    }
}

impl TryFrom<PermutationIndex> for PermutationArray {
    type Error = PermutationError;

    fn try_from(value: PermutationIndex) -> Result<Self, Self::Error> {
        let len: usize = value.0.len();
        let mut indexes = (0..len).collect::<Vec<usize>>();

        let result = value
            .0
            .iter()
            .enumerate()
            .map(|(index, x)| {
                if *x <= indexes.len() {
                    Ok(indexes.remove(*x))
                } else {
                    Err(PermutationError::NotPermutationIndex { index, element: *x })
                }
            })
            .collect::<Result<Vec<usize>, _>>()?;

        Ok(PermutationArray(result))
    }
}

impl TryFrom<PermutationArray> for PermutationIndex {
    type Error = PermutationError;

    fn try_from(value: PermutationArray) -> Result<Self, Self::Error> {
        let len: usize = value.0.len();
        let mut indexes = (0..len).collect::<Vec<usize>>();

        let result = value
            .0
            .iter()
            .enumerate()
            .map(|(index, x)| {
                indexes
                    .iter()
                    .position(|y| y == x)
                    .map(|pos| {
                        indexes.remove(pos);
                        pos
                    })
                    .ok_or(PermutationError::NotPermutationArray { index, element: *x })
            })
            .collect::<Result<Vec<usize>, _>>()?;

        Ok(PermutationIndex(result))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn index() {
        macro_rules! arr2indx {
			($($a:expr),* => $($b:expr),*) => {
				assert_eq!(
					PermutationIndex::try_from(PermutationArray(vec![$($a),*])),
					Ok(PermutationIndex(vec![$($b),*]))
				);

				assert_eq!(
					PermutationArray::try_from(PermutationIndex(vec![$($b),*])),
					Ok(PermutationArray(vec![$($a),*]))
				);
			};
		}

        arr2indx!(0 => 0);
        arr2indx!(0, 1 => 0, 0);
        arr2indx!(1, 0 => 1, 0);
        arr2indx!(0, 1, 2 => 0, 0, 0);
        arr2indx!(0, 2, 1 => 0, 1, 0);
        arr2indx!(1, 0, 2 => 1, 0, 0);
        arr2indx!(1, 2, 0 => 1, 1, 0);
        arr2indx!(2, 0, 1 => 2, 0, 0);
        arr2indx!(2, 1, 0 => 2, 1, 0);
        arr2indx!(0, 1, 2, 3, 4, 5, 7, 11, 9, 8, 13, 10, 12, 14, 15, 6 => 0, 0, 0, 0, 0, 0, 1, 4, 2, 1, 3, 1, 1, 1, 1, 0);
    }

    #[test]
    fn number() {
        macro_rules! indx2num {
			($($a:expr),* => $size:tt $number:tt) => {
				assert_eq!(
					PermutationInt::try_from(PermutationIndex(vec![$($a),*])),
					Ok(PermutationInt { int: BigUint::from($number as u64), permutation_size: $size })
				);

				assert_eq!(
					PermutationIndex::try_from(PermutationInt { int: BigUint::from($number as u64), permutation_size: $size }),
					Ok(PermutationIndex(vec![$($a),*]))
				);
			};
		}

        indx2num!(0 => 1 0);
        indx2num!(0, 0 => 2 0);
        indx2num!(1, 0 => 2 1);
        indx2num!(0, 0, 0 => 3 0);
        indx2num!(0, 1, 0 => 3 1);
        indx2num!(1, 0, 0 => 3 2);
        indx2num!(1, 1, 0 => 3 3);
        indx2num!(2, 0, 0 => 3 4);
        indx2num!(2, 1, 0 => 3 5);
        indx2num!(0, 0, 0, 0, 0, 0, 1, 4, 2, 1, 3, 1, 1, 1, 1, 0 => 16 535353);
    }

    #[test]
    fn string() {
        macro_rules! string {
            ($size:tt $number:tt => $string:tt) => {
                assert_eq!(
                    PermutationString::try_from(PermutationInt {
                        int: BigUint::from($number as u64),
                        permutation_size: $size
                    }),
                    Ok(PermutationString {
                        string: $string.to_string(),
                        permutation_size: $size
                    })
                );

                assert_eq!(
                    PermutationInt::try_from(PermutationString {
                        string: $string.to_string(),
                        permutation_size: $size
                    }),
                    Ok(PermutationInt {
                        int: BigUint::from($number as u64),
                        permutation_size: $size
                    }),
                );
            };
        }

        string!(1 0 => "0");
        string!(2 0 => "0");
        string!(2 1 => "1");
        string!(3 0 => "0");
        string!(3 1 => "1");
        string!(3 2 => "2");
        string!(3 3 => "3");
        string!(3 4 => "4");
        string!(3 5 => "5");
        string!(16 535353 => "VI22");
    }

    #[test]
    fn big() {
        #[rustfmt::skip]
		let a = PermutationArray(vec![
		    0,  1,  54, 3,  36, 7,  18, 5,  72, 
		    9,  30, 19, 28, 39, 66, 21, 48, 75, 
		    6,  11, 60, 15, 42, 69, 56, 51, 26, 
		    27, 12, 55, 10, 37, 64, 57, 46, 73, 
		    4,  31, 58, 13, 40, 67, 22, 49, 76, 
		    63, 34, 61, 16, 43, 70, 25, 68, 79, 
		    2,  29, 24, 33, 38, 65, 20, 47, 62, 
		    45, 32, 59, 14, 41, 52, 23, 50, 77, 
		    8 , 35, 74, 17, 44, 71, 78, 53, 80,
		]);
        let b = PermutationIndex::try_from(a.clone()).unwrap();
        let c = PermutationInt::try_from(b).unwrap();
        let d = PermutationString::try_from(c).unwrap();
        assert_eq!(
            a,
            PermutationArray::try_from(
                PermutationIndex::try_from(PermutationInt::try_from(d).unwrap()).unwrap()
            )
            .unwrap()
        );
    }
}
