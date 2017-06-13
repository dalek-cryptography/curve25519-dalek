// Various macros for implmenting repetative pass-by-value semantics

#[macro_export]
macro_rules! add_impl {
    ($lhs:ty, $rhs:ty, $out:ty) => {
        impl Add<$rhs> for $lhs {
            type Output = $out;

            #[inline(always)]
            fn add(self, rhs: $rhs) -> $out {
                &self + &rhs
            }
        }
    };
}

#[macro_export]
macro_rules! sub_impl {
    ($lhs:ty, $rhs:ty, $out:ty) => {
        impl Sub<$rhs> for $lhs {
            type Output = $out;

            #[inline(always)]
            fn sub(self, rhs: $rhs) -> $out {
                &self - &rhs
            }
        }
    };
}

#[macro_export]
macro_rules! mul_impl {
    ($lhs:ty, $rhs:ty, $out:ty) => {
        impl Mul<$rhs> for $lhs {
            type Output = $out;

            #[inline(always)]
            fn mul(self, rhs: $rhs) -> $out {
                &self * &rhs
            }
        }
    };
}

#[macro_export]
macro_rules! neg_impl {
    ($t:ty, $out:ty) => {
        impl Neg for $t {
            type Output = $out;

            #[inline(always)]
            fn neg(self) -> $out {
                -(&self)
            }
        }
    };
}
