use super::scalar::Scalar52;

/// A wide scalar built of 5 u128 limbs. The scalars are stored as x/R (Montgomery form) with >32 bits of slack.
/// R = 2^260
pub struct WideScalar52(pub [u128; 5]);

impl WideScalar52 {
    pub const ZERO: Self = Self([0u128; 5]);

    pub fn new(x: &Scalar52) -> Self {
        Self::new_from_montgomery(&x.from_montgomery())
    }

    pub(crate) fn new_from_montgomery(x: &Scalar52) -> Self {
        Self(core::array::from_fn(|i| x.0[i] as u128))
    }

    pub fn mul(a: &Scalar52, b: &Scalar52) -> Self {
        Self::new_from_montgomery(&Scalar52::montgomery_mul(a, b))
    }

    pub fn add_assign(&mut self, rhs: &Self) {
        self.0
            .iter_mut()
            .zip(rhs.0.iter())
            .for_each(|(a, b)| *a += b);
    }

    pub fn mul_acc(&mut self, lhs: &Scalar52, rhs: &Scalar52) {
        self.add_assign(&Self::mul(lhs, rhs));
    }

    pub fn into_scalar(&self) -> Scalar52 {
        /// `RRR` = (R^3) % L where R = 2^260
        const RRR: Scalar52 = Scalar52([
            0x0004f516a4e30429,
            0x000d71e63305a553,
            0x0005b6514d3c593a,
            0x00078065dc6c04ec,
            0x000000b773599cec,
        ]);

        let mut out = [0u128; 9];
        out.iter_mut().zip(self.0).for_each(|(a, b)| *a = b);
        let res = Scalar52::montgomery_reduce(&out); // out/R^2
        Scalar52::montgomery_reduce(&Scalar52::mul_internal(&res, &RRR)) // out
    }
}
