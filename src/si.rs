/// Dimensions in use by the International System of Units.
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum Dimensions {
    Time,
    Length,
    Mass,
    ElectricCurrent,
    Temperature,
    Substance,
    LuminousIntensity,
    Entropy,
}
