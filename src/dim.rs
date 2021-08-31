use crate::DimensionalOperationError;
use num_traits::Zero;
use std::{
    collections::{hash_map::Entry, HashMap},
    fmt::Debug,
    hash::Hash,
    ops::{Add, Div, Mul, Neg, Sub},
};

/// A Dimensional Value. Contains both its magnitude, and the dimensions the
/// value relates to.
#[derive(Debug, Clone)]
pub struct Dimensional<TDimensions, TMagnitude = f64, TDimensionalMagnitude = i8> {
    /// The unitless part of the value.
    /// For example, 3 seconds has a magnitude of `3`.
    pub magnitude: TMagnitude,
    /// A map containing all of the dimensions, and their respective count.
    /// For example, 3 square-metres per second will have an entry keyed on
    /// `Length` with value `2`, and an entry keyed on `Time` with value `-1`.
    ///
    /// Entries with a zero value should be considered as not existing.
    pub dimensions: HashMap<TDimensions, TDimensionalMagnitude>,
}

impl<TD, TM, TDM> Dimensional<TD, TM, TDM> {
    /// Creates a new unitless value.
    ///
    /// # Arguments
    ///
    /// `magnitude`: The magnitude the resulting value should have.
    pub fn new(magnitude: TM) -> Self {
        Dimensional {
            magnitude,
            dimensions: HashMap::new(),
        }
    }
}

impl<TD: Eq + Hash, TM, TDM: Zero + PartialEq> Dimensional<TD, TM, TDM> {
    /// Returns if the other value has equal dimensions, accounting for zero
    /// values.
    ///
    /// # Arguments
    ///
    /// `other`: The other dimensional value to check for equal dimensions.
    ///
    /// # Examples
    ///
    /// 2 seconds has the same dimensions as 1 minute
    /// ```
    /// # use std::collections::HashMap;
    /// # use dimensional::{dim, Dimensional, DimensionalOperationError};
    /// use dimensional::si::Dimensions as SI;
    /// assert!(
    ///     dim!(3.0, SI::Time => 1).equal_dimensions(
    ///         &dim!(60.0, SI::Time => 1)));
    /// ```
    ///
    /// 1 second does *not* have the same dimensions as 1 metre
    /// ```
    /// # use std::collections::HashMap;
    /// # use dimensional::{dim, Dimensional, DimensionalOperationError};
    /// use dimensional::si::Dimensions as SI;
    /// assert!(
    ///     ! dim!(3.0, SI::Time => 1).equal_dimensions(
    ///         &dim!(60.0, SI::Length => 1)));
    /// ```
    pub fn equal_dimensions(&self, other: &Self) -> bool {
        for (dim, mag1) in &self.dimensions {
            if mag1.is_zero() {
                continue;
            }
            match other.dimensions.get(dim) {
                Some(mag2) if mag1 == mag2 => continue,
                _ => return false,
            }
        }
        for (dim, mag1) in &other.dimensions {
            if mag1.is_zero() {
                continue;
            }
            match self.dimensions.get(dim) {
                Some(mag2) if mag1 == mag2 => continue,
                _ => return false,
            }
        }
        true
    }
}

impl<TD: Eq + Hash, TM: Add<Output = TM>, TDM: PartialEq + Zero> Add for Dimensional<TD, TM, TDM> {
    type Output = Result<Self, DimensionalOperationError>;

    /// Adds this dimensional value to another.
    ///
    /// # Arguments
    ///
    /// `other`: The other value to add.
    ///
    /// # Examples
    ///
    /// Adding 1 second to 2 seconds produces 3 seconds
    /// ```
    /// # use std::collections::HashMap;
    /// # use dimensional::{dim, Dimensional, DimensionalOperationError};
    /// use dimensional::si::Dimensions as SI;
    /// assert_eq!(
    ///     dim!(1.0, SI::Time => 1) + dim!(2.0, SI::Time => 1),
    ///     Ok(dim!(3.0, SI::Time => 1))
    /// );
    /// ```
    ///
    /// # Errors
    ///
    /// Attempting to add two values of differing dimensions will produce a
    /// [`DimensionalOperationError`].
    ///
    /// Adding 1 second to 1 metre produces an error
    /// ```
    /// # use std::collections::HashMap;
    /// # use dimensional::{dim, Dimensional, DimensionalOperationError};
    /// # use dimensional::si::Dimensions as SI;
    /// assert_eq!(
    ///     dim!(1.0, SI::Time => 1) + dim!(1.0, SI::Length => 1),
    ///     Err(DimensionalOperationError::DifferingDimensions)
    /// );
    /// ```
    fn add(mut self, other: Self) -> Self::Output {
        if !self.equal_dimensions(&other) {
            return Err(DimensionalOperationError::DifferingDimensions);
        }

        self.magnitude = self.magnitude + other.magnitude;
        Ok(self)
    }
}

impl<TD: Eq + Hash, TM: Sub<Output = TM>, TDM: PartialEq + Zero> Sub for Dimensional<TD, TM, TDM> {
    type Output = Result<Self, DimensionalOperationError>;

    /// Subtracts this dimensional value from another.
    ///
    /// # Arguments
    ///
    /// `other`: The other value to subtract.
    ///
    /// # Examples
    ///
    /// Subtracting 1 second from 2 seconds produces 1 second
    /// ```
    /// # use std::collections::HashMap;
    /// # use dimensional::{dim, Dimensional, DimensionalOperationError};
    /// use dimensional::si::Dimensions as SI;
    /// assert_eq!(
    ///     dim!(2.0, SI::Time => 1) - dim!(1.0, SI::Time => 1),
    ///     Ok(dim!(1.0, SI::Time => 1))
    /// );
    /// ```
    ///
    /// # Errors
    ///
    /// Attempting to subtract two values of differing dimensions will produce a
    /// [`DimensionalOperationError`].
    ///
    /// Subtracting 1 second from 1 metre produces an error
    /// ```
    /// # use std::collections::HashMap;
    /// # use dimensional::{dim, Dimensional, DimensionalOperationError};
    /// # use dimensional::si::Dimensions as SI;
    /// assert_eq!(
    ///     dim!(1.0, SI::Length => 1) + dim!(1.0, SI::Time => 1),
    ///     Err(DimensionalOperationError::DifferingDimensions)
    /// );
    /// ```
    fn sub(mut self, other: Self) -> Self::Output {
        if !self.equal_dimensions(&other) {
            return Err(DimensionalOperationError::DifferingDimensions);
        }

        self.magnitude = self.magnitude - other.magnitude;
        Ok(self)
    }
}

impl<TD: Eq + Hash, TM: Mul<Output = TM>, TDM: Add<Output = TDM>> Mul for Dimensional<TD, TM, TDM> {
    type Output = Self;

    /// Multiplies one dimensional value with another. Values of differing
    /// dimensions will have their dimensions combined.
    ///
    /// # Arguments
    ///
    /// `other`: The other value to subtract.
    ///
    /// # Examples
    ///
    /// Multiplying 2 metres with 2 metres produces 4 square-metres
    /// ```
    /// # use std::collections::HashMap;
    /// # use dimensional::{dim, Dimensional, DimensionalOperationError};
    /// use dimensional::si::Dimensions as SI;
    /// assert_eq!(
    ///     dim!(2.0, SI::Length => 1) * dim!(2.0, SI::Length => 1),
    ///     dim!(4.0, SI::Length => 2)
    /// )
    /// ```
    ///
    /// Multiplying 4 coulombs by 2 hertz produces 8 amps
    /// ```
    /// # use std::collections::HashMap;
    /// # use dimensional::{dim, Dimensional, DimensionalOperationError};
    /// # use dimensional::si::Dimensions as SI;
    /// assert_eq!(
    ///     dim!(4.0, SI::ElectricCurrent => 1, SI::Time => 1) * dim!(2.0, SI::Time => -1),
    ///     dim!(8.0, SI::ElectricCurrent => 1)
    /// )
    /// ```
    fn mul(mut self, other: Self) -> Self::Output {
        self.magnitude = self.magnitude * other.magnitude;
        for (dim, mag1) in other.dimensions {
            match self.dimensions.entry(dim) {
                Entry::Occupied(entry) => {
                    let (key, val) = entry.remove_entry();
                    self.dimensions.insert(key, val + mag1);
                }
                Entry::Vacant(entry) => {
                    entry.insert(mag1);
                }
            }
        }
        self
    }
}

impl<TD: Eq + Hash, TM: Div<Output = TM>, TDM: Sub<Output = TDM> + Neg<Output = TDM>> Div
    for Dimensional<TD, TM, TDM>
{
    type Output = Self;

    /// Divides one dimensional value with another. Values of differing
    /// dimensions will have their dimensions combined.
    ///
    /// # Arguments
    ///
    /// `other`: The other value to divide.
    ///
    /// # Examples
    ///
    /// Dividing 2 metres from 4 metres produces a dimensionless 2.
    /// ```
    /// # use std::collections::HashMap;
    /// # use dimensional::{dim, Dimensional, DimensionalOperationError};
    /// use dimensional::si::Dimensions as SI;
    /// assert_eq!(
    ///     dim!(4.0, SI::Length => 1) / dim!(2.0, SI::Length => 1),
    ///     Dimensional::new(2.0)
    /// )
    /// ```
    ///
    /// Dividing 3600 seconds from 1000 metres produces 1kph (just under 0.28
    /// meters per second).
    /// ```
    /// # use std::collections::HashMap;
    /// # use dimensional::{dim, Dimensional, DimensionalOperationError};
    /// # use dimensional::si::Dimensions as SI;
    /// assert_eq!(
    ///     dim!(1000.0, SI::Length => 1) / dim!(3600.0, SI::Time => 1),
    ///     dim!(1.0/3.6, SI::Length => 1, SI::Time => -1)
    /// )
    /// ```
    fn div(mut self, other: Self) -> Self::Output {
        self.magnitude = self.magnitude / other.magnitude;
        for (dim, mag1) in other.dimensions {
            match self.dimensions.entry(dim) {
                Entry::Occupied(entry) => {
                    let (key, val) = entry.remove_entry();
                    self.dimensions.insert(key, val - mag1);
                }
                Entry::Vacant(entry) => {
                    entry.insert(-mag1);
                }
            }
        }
        self
    }
}

impl<TD, TM: Neg<Output = TM>, TDM> Neg for Dimensional<TD, TM, TDM> {
    type Output = Self;

    /// Produces a negated value. Only magnitude is negated, not the dimensions.
    ///
    /// # Examples
    ///
    /// Negating 1 second produces -1 second.
    /// ```
    /// # use std::collections::HashMap;
    /// # use dimensional::{dim, Dimensional, DimensionalOperationError};
    /// use dimensional::si::Dimensions as SI;
    /// assert_eq!(
    ///     -dim!(1.0, SI::Time => 1),
    ///     dim!(-1.0, SI::Time => 1)
    /// )
    /// ```
    fn neg(mut self) -> Self::Output {
        self.magnitude = -self.magnitude;
        self
    }
}

impl<TD: Eq + Hash, TM: PartialEq, TDM: Zero + PartialEq> PartialEq for Dimensional<TD, TM, TDM> {
    /// Checks if a value equals another value, checking both magnitude and
    /// dimensions.
    ///
    /// # Arguments
    ///
    /// `other`: The other value to check for equality.
    ///
    /// # Examples
    ///
    /// 1 second is equal to another instance of 1 second.
    /// ```
    /// # use std::collections::HashMap;
    /// # use dimensional::{dim, Dimensional, DimensionalOperationError};
    /// use dimensional::si::Dimensions as SI;
    /// assert!(
    ///     dim!(1.0, SI::Time => 1) == dim!(1.0, SI::Time => 1)
    /// )
    /// ```
    ///
    /// 1 second is not equal to an instance of 1 metre.
    /// ```
    /// # use std::collections::HashMap;
    /// # use dimensional::{dim, Dimensional, DimensionalOperationError};
    /// use dimensional::si::Dimensions as SI;
    /// assert!(
    ///     dim!(1.0, SI::Time => 1) != dim!(1.0, SI::Length => 1)
    /// )
    /// ```
    ///
    fn eq(&self, other: &Self) -> bool {
        self.magnitude == other.magnitude && self.equal_dimensions(other)
    }
}

impl<TD: Eq + Hash, TM: Eq, TDM: Zero + Eq> Eq for Dimensional<TD, TM, TDM> {}

impl<TD, TM: Default, TDM> Default for Dimensional<TD, TM, TDM> {
    /// Returns a new unitless Dimensional Value with whatever the default value
    /// for the magnitude type is.
    fn default() -> Self {
        Dimensional::new(Default::default())
    }
}

/// Shorthand for creating a dimensional value.
///
/// # Examples
///
/// ```
/// # use std::collections::HashMap;
/// # use dimensional::{dim, Dimensional, DimensionalOperationError};
/// use dimensional::si::Dimensions as SI;
/// let d = dim!(2.0, SI::Length => 1, SI::Time => 2);
/// assert_eq!(d.magnitude, 2.0);
/// assert_eq!(d.dimensions.get(&SI::Length), Some(&1));
/// assert_eq!(d.dimensions.get(&SI::Time), Some(&2));
/// ```
#[macro_export]
macro_rules! dim {
    ($mag:expr) => {{
        Dimensional::new($mag)
    }};
    ($mag:expr, $($dim:expr => $dim_mag:expr),+) => {{
        let mut hash = std::collections::HashMap::new();
        $(
            hash.insert($dim, $dim_mag);
        )+

        Dimensional {
            magnitude: $mag,
            dimensions: hash
        }
    }}
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Debug, Hash, PartialEq, Eq)]
    enum Dim {
        Length,
        Time,
    }

    fn d(magnitude: f64) -> Dimensional<Dim> {
        Dimensional::<Dim> {
            magnitude,
            dimensions: HashMap::new(),
        }
    }
    fn dl(magnitude: f64, length: i8) -> Dimensional<Dim> {
        dim!(magnitude, Dim::Length => length)
    }
    fn dt(magnitude: f64, time: i8) -> Dimensional<Dim> {
        dim!(magnitude, Dim::Time => time)
    }
    fn dlt(magnitude: f64, length: i8, time: i8) -> Dimensional<Dim> {
        dim!(magnitude, Dim::Length => length, Dim::Time => time)
    }

    #[test]
    fn dimensional_dim_macro() {
        let dim = dim!(2, Dim::Length => 2);
        assert_eq!(dim.magnitude, 2);
        assert_eq!(dim.dimensions.get(&Dim::Length), Some(&2));
        assert_eq!(dim.dimensions.get(&Dim::Time), None);
    }

    #[test]
    fn dimensional_new() {
        assert_eq!(Dimensional::new(2.0), d(2.0));
    }

    #[test]
    fn dimensional_equal_dimensions() {
        assert!(d(2.0).equal_dimensions(&dl(4.0, 0)));
        assert!(dl(2.0, 2).equal_dimensions(&dl(4.0, 2)));
        assert!(dl(2.0, 2).equal_dimensions(&dlt(4.0, 2, 0)));
        assert!(dlt(2.0, 2, 0).equal_dimensions(&dl(-4.0, 2)));
        assert!(dlt(2.0, 2, 0).equal_dimensions(&dlt(-4.0, 2, 0)));

        assert!(!dl(2.0, 2).equal_dimensions(&dl(2.0, -1)));
        assert!(!dl(2.0, 2).equal_dimensions(&dt(2.0, 2)));
    }

    #[test]
    fn dimensional_add() {
        assert_eq!(d(2.0) + d(4.0), Ok(d(6.0)));
        assert_eq!(dl(2.0, 1) + dl(-2.0, 1), Ok(dl(0.0, 1)));

        assert_eq!(
            d(2.0) + dl(2.0, 1),
            Err(DimensionalOperationError::DifferingDimensions)
        );
    }

    #[test]
    fn dimensional_sub() {
        assert_eq!(d(2.0) - d(4.0), Ok(d(-2.0)));
        assert_eq!(dl(2.0, 1) - dl(-2.0, 1), Ok(dl(4.0, 1)));

        assert_eq!(
            d(2.0) - dl(2.0, 1),
            Err(DimensionalOperationError::DifferingDimensions)
        );
    }

    #[test]
    fn dimensional_mul() {
        assert_eq!(d(2.0) * d(2.0), d(4.0));
        assert_eq!(d(2.0) * dl(1.0, 1), dl(2.0, 1));
        assert_eq!(dl(3.0, 1) * dt(-3.0, 1), dlt(-9.0, 1, 1));

        assert_eq!(dl(3.0, 2) * dlt(1.0, -1, 1), dlt(3.0, 1, 1));
    }

    #[test]
    fn dimensional_div() {
        assert_eq!(d(2.0) / d(2.0), d(1.0));
        assert_eq!(d(2.0) / dl(1.0, 1), dl(2.0, -1));
        assert_eq!(dl(3.0, 1) / dt(-3.0, 1), dlt(-1.0, 1, -1));

        assert_eq!(dl(3.0, 2) / dlt(1.0, -1, 1), dlt(3.0, 3, -1));
    }

    #[test]
    fn dimensional_neg() {
        assert_eq!(-d(2.0), d(-2.0));
        assert_eq!(-d(-2.0), d(2.0));
        assert_eq!(-dlt(-2.0, 1, -1), dlt(2.0, 1, -1));
    }
}
