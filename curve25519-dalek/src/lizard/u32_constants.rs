use cfg_if::cfg_if;

cfg_if! {
    if #[cfg(curve25519_dalek_backend = "fiat")] {
        pub use crate::backend::serial::fiat_u32::field::FieldElement2625;

        const fn field_element(element: [u32; 10]) -> FieldElement2625 {
            FieldElement2625(fiat_crypto::curve25519_32::fiat_25519_tight_field_element(element))
        }
    } else {
        pub use crate::backend::serial::u32::field::FieldElement2625;

        const fn field_element(element: [u32; 10]) -> FieldElement2625 {
            FieldElement2625(element)
        }
    }
}

/// `= sqrt(i*d)`, where `i = +sqrt(-1)` and `d` is the Edwards curve parameter.
pub const SQRT_ID: FieldElement2625 = field_element([
    39590824, 701138, 28659366, 23623507, 53932708, 32206357, 36326585, 24309414, 26167230, 1494357,
]);

/// `= (d+1)/(d-1)`, where `d` is the Edwards curve parameter.
pub const DP1_OVER_DM1: FieldElement2625 = field_element([
    58833708, 32184294, 62457071, 26110240, 19032991, 27203620, 7122892, 18068959, 51019405,
    3776288,
]);

/// `= -2/sqrt(a-d)`, where `a = -1 (mod p)`, `d` are the Edwards curve parameters.
pub const MDOUBLE_INVSQRT_A_MINUS_D: FieldElement2625 = field_element([
    54885894, 25242303, 55597453, 9067496, 51808079, 33312638, 25456129, 14121551, 54921728,
    3972023,
]);

/// `= -2i/sqrt(a-d)`, where `a = -1 (mod p)`, `d` are the Edwards curve parameters
/// and `i = +sqrt(-1)`.
pub const MIDOUBLE_INVSQRT_A_MINUS_D: FieldElement2625 = field_element([
    58178520, 23970840, 26444491, 29801899, 41064376, 743696, 2900628, 27920316, 41968995, 5270573,
]);

/// `= -1/sqrt(1+d)`, where `d` is the Edwards curve parameters.
pub const MINVSQRT_ONE_PLUS_D: FieldElement2625 = field_element([
    38019585, 4791795, 20332186, 18653482, 46576675, 33182583, 65658549, 2817057, 12569934,
    30919145,
]);
