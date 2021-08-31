use std::{error::Error, fmt::Display};

#[derive(Debug, PartialEq, Eq)]
pub enum DimensionalOperationError {
    /// The units used in the operation have differing dimensions, and cannot
    /// produce a meaningful result.
    ///
    /// # Examples
    ///
    /// Attempting to add 3 seconds to 3 metres will produce this error.
    /// ```
    /// # use std::collections::HashMap;
    /// # use dimensional::{dim, Dimensional, DimensionalOperationError};
    /// use dimensional::si::Dimensions as SI;
    /// assert_eq!(
    ///     dim!(3.0, SI::Length => 1) + dim!(3.0, SI::Time => 1),
    ///     Err(DimensionalOperationError::DifferingDimensions)
    /// );
    /// ```
    DifferingDimensions,
}

impl Display for DimensionalOperationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DimensionalOperationError::DifferingDimensions => {
                write!(f, "attempted to perform an operation that does not support value with different dimensions")
            }
        }
    }
}

impl Error for DimensionalOperationError {}
