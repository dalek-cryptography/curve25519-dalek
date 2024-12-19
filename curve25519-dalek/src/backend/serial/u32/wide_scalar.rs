use super::scalar::Scalar29;

/// A wide scalar built of 9 u64 limbs. The scalars are stored as x/R (Montgomery form) with >32 bits of slack.
/// R = 2^261
pub struct WideScalar29(pub [u64; 9]);

impl WideScalar29 {
    pub const ZERO: Self = Self([0u64; 9]);

    pub fn from_scalar(x: &Scalar29) -> Self {
        Self::new_from_montgomery(&x.from_montgomery())
    }

    pub(crate) fn new_from_montgomery(x: &Scalar29) -> Self {
        let mut y = Self::ZERO;
        y.0.iter_mut().zip(x.0).for_each(|(ye, xe)| *ye = xe as u64);
        y
    }

    pub fn mul(a: &Scalar29, b: &Scalar29) -> Self {
        Self::new_from_montgomery(&Scalar29::montgomery_mul(a, b))
    }

    pub fn add_assign<'a>(&mut self, rhs: &'a WideScalar29) {
        self.0
            .iter_mut()
            .zip(rhs.0.iter())
            .for_each(|(a, b)| *a += b);
    }

    pub fn mul_acc(&mut self, lhs: &Scalar29, rhs: &Scalar29) {
        self.add_assign(&Self::mul(lhs, rhs));
    }

    pub fn to_scalar(&self) -> Scalar29 {
        /// `RRR` = (R^3) % L where R = 2^261
        const RRR: Scalar29 = Scalar29([
            0x07182148, 0x0d3d45a9, 0x0660b4aa, 0x13ad71e6, 0x08a69e2c, 0x013b16d9, 0x00cbb8d8,
            0x199cec78, 0x0005bb9a,
        ]);

        let mut out = [0u64; 17];
        out.iter_mut().zip(self.0).for_each(|(a, b)| *a = b);
        let res = Scalar29::montgomery_reduce(&out); // out/R^2
        Scalar29::montgomery_reduce(&Scalar29::mul_internal(&res, &RRR)) // out
    }
}
