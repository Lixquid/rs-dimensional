mod dim;
mod errors;
pub use dim::Dimensional;
pub use errors::DimensionalOperationError;

#[cfg(feature = "si")]
pub mod si;

#[cfg(test)]
pub mod test_aid {
    /// Used as a stand-in for the SI Dimension enum in non-SI tests
    #[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
    pub enum Dimensions {
        Length,
        Time,
    }
}
