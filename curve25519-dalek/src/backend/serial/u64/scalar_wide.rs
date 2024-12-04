use super::scalar::Scalar52;

/// A wide scalar built of 5 u128 limbs. The scalars are stored as x/R (Montgomery form).
#[derive(Copy, Clone)]
pub struct WideScalar(pub [u128; 5]);

impl WideScalar {
    pub const ZERO: Self = Self([0u128; 5]);

    pub fn new(x: &Scalar52) -> Self {
        Self::new_from_montgomery(&x.from_montgomery())
    }

    pub(crate) fn new_from_montgomery(x: &Scalar52) -> Self {
        let inp = x.0;
        let out = core::array::from_fn(|i| inp[i] as u128);
        Self(out)
    }

    pub fn mul(a: &Scalar52, b: &Scalar52) -> Self {
        Self::new_from_montgomery(&Scalar52::montgomery_mul(a, b))
    }

    pub fn add_assign<'a>(&mut self, rhs: &'a WideScalar) {
        self.0
            .iter_mut()
            .zip(rhs.0.iter())
            .for_each(|(a, b)| *a += b);
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

#[cfg(test)]
mod tests {
    use super::*;

    pub static X: Scalar52 = Scalar52([
        0x000fffffffffffff,
        0x000fffffffffffff,
        0x000fffffffffffff,
        0x000fffffffffffff,
        0x00001fffffffffff,
    ]);

    /// y = 6145104759870991071742105800796537629880401874866217824609283457819451087098
    pub static Y: Scalar52 = Scalar52([
        0x000b75071e1458fa,
        0x000bf9d75e1ecdac,
        0x000433d2baf0672b,
        0x0005fffcc11fad13,
        0x00000d96018bb825,
    ]);

    /// x^2/R mod l in Montgomery form
    pub static XX_MONT: Scalar52 = Scalar52([
        0x000c754eea569a5c,
        0x00063b6ed36cb215,
        0x0008ffa36bf25886,
        0x000e9183614e7543,
        0x0000061db6c6f26f,
    ]);

    /// x*y/R mod l in Montgomery form
    pub static XY_MONT: Scalar52 = Scalar52([
        0x0006d52bf200cfd5,
        0x00033fb1d7021570,
        0x000f201bc07139d8,
        0x0001267e3e49169e,
        0x000007b839c00268,
    ]);

    /// x^2 = 3078544782642840487852506753550082162405942681916160040940637093560259278169 mod l
    pub static XX: Scalar52 = Scalar52([
        0x0001668020217559,
        0x000531640ffd0ec0,
        0x00085fd6f9f38a31,
        0x000c268f73bb1cf4,
        0x000006ce65046df0,
    ]);

    /// x*y = 36752150652102274958925982391442301741 mod l
    pub static XY: Scalar52 = Scalar52([
        0x000ee6d76ba7632d,
        0x000ed50d71d84e02,
        0x00000000001ba634,
        0x0000000000000000,
        0x0000000000000000,
    ]);

    /// x*y * 2^24 mod l in Montgomery form
    /// test carry propagation
    pub static XY_24: Scalar52 = Scalar52([
        0x000ba7632d000000,
        0x0001d84e02ee6d76,
        0x00001ba634ed50d7,
        0x0000000000000000,
        0x0000000000000000,
    ]);

    #[test]
    fn multiplication() {
        let xx_mont = WideScalar::mul(&X, &X);
        for (v, v_exp) in xx_mont.0.iter().zip(XX_MONT.0) {
            assert_eq!(*v, v_exp as u128);
        }
        let xx = xx_mont.into_scalar();
        for (v, v_exp) in xx.0.iter().zip(XX.0) {
            assert_eq!(*v, v_exp);
        }

        let xy_mont = WideScalar::mul(&X, &Y);
        for (v, v_exp) in xy_mont.0.iter().zip(XY_MONT.0) {
            assert_eq!(*v, v_exp as u128);
        }
        let xy = xy_mont.into_scalar();
        for (v, v_exp) in xy.0.iter().zip(XY.0) {
            assert_eq!(*v, v_exp);
        }
    }

    #[test]
    fn dot_product() {
        let mut r = WideScalar::ZERO;
        for _ in 0..1 << 24 {
            r.add_assign(&WideScalar::mul(&X, &Y));
        }

        let r = r.into_scalar();
        for (v, v_exp) in r.0.iter().zip(XY_24.0) {
            assert_eq!(*v, v_exp);
        }
    }

    #[test]
    fn conversions() {
        let r = WideScalar::new_from_montgomery(&XY_MONT);
        for (v, v_exp) in r.0.iter().zip(XY_MONT.0) {
            assert_eq!(*v, v_exp as u128);
        }
        let r = r.into_scalar();
        for (v, v_exp) in r.0.iter().zip(XY.0) {
            assert_eq!(*v, v_exp);
        }

        let r = WideScalar::new(&Y).into_scalar();
        for (v, v_exp) in r.0.iter().zip(Y.0) {
            assert_eq!(*v, v_exp);
        }
    }
}
