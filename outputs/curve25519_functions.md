# Curve25519 Functions

| Function | Module | Has Spec (Verus) | Has Proof (Verus) |
|----------|--------|:----------------:|:-----------------:|
| [fmt](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/build.rs#L14) | curve25519_dalek::build |  |  |
| [is_capable_simd](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/build.rs#L76) | curve25519_dalek::build |  |  |
| [determine_curve25519_dalek_bits_warning](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/build.rs#L93) | curve25519_dalek::build |  |  |
| [determine_curve25519_dalek_bits](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/build.rs#L98) | curve25519_dalek::build |  |  |
| [get_selected_backend](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/mod.rs#L53) | curve25519_dalek::backend |  |  |
| [pippenger_optional_multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/mod.rs#L77) | curve25519_dalek::backend |  |  |
| [VartimePrecomputedStraus::straus_multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/mod.rs#L174) | curve25519_dalek::backend |  |  |
| [VartimePrecomputedStraus::straus_optional_multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/mod.rs#L202) | curve25519_dalek::backend |  |  |
| [VartimePrecomputedStraus::variable_base_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/mod.rs#L231) | curve25519_dalek::backend |  |  |
| [VartimePrecomputedStraus::vartime_double_base_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/mod.rs#L245) | curve25519_dalek::backend |  |  |
| [ProjectiveNielsPoint::identity](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L241) | curve25519_dalek::backend::serial::curve_models |  |  |
| [AffineNielsPoint::identity](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L258) | curve25519_dalek::backend::serial::curve_models |  |  |
| [ProjectiveNielsPoint::default](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L252) | curve25519_dalek::backend::serial::curve_models |  |  |
| [AffineNielsPoint::conditional_select](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L315) | curve25519_dalek::backend::serial::curve_models |  |  |
| [CompletedPoint::as_extended](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L366) | curve25519_dalek::backend::serial::curve_models |  |  |
| [CompletedPoint::as_projective](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L354) | curve25519_dalek::backend::serial::curve_models |  |  |
| [ProjectivePoint::double](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L382) | curve25519_dalek::backend::serial::curve_models |  |  |
| [ProjectivePoint::add](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L459) | curve25519_dalek::backend::serial::curve_models |  |  |
| [ProjectivePoint::sub](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L480) | curve25519_dalek::backend::serial::curve_models |  |  |
| [ProjectivePoint::neg](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L517) | curve25519_dalek::backend::serial::curve_models |  |  |
| [Pippenger::optional_multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/scalar_mul/pippenger.rs#L65) | curve25519_dalek::backend::serial::scalar_mul::pippenger |  |  |
| [Straus::multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/scalar_mul/straus.rs#L101) | curve25519_dalek::backend::serial::scalar_mul::straus |  |  |
| [Straus::optional_multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/scalar_mul/straus.rs#L157) | curve25519_dalek::backend::serial::scalar_mul::straus |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/scalar_mul/variable_base.rs#L11) | curve25519_dalek::backend::serial::scalar_mul::variable_base |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/scalar_mul/vartime_double_base.rs#L23) | curve25519_dalek::backend::serial::scalar_mul::vartime_double_base |  |  |
| [FieldElement51::fmt](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L113) | curve25519_dalek::backend::serial::u64::field | :x: |  |
| [FieldElement51::add_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L166) | curve25519_dalek::backend::serial::u64::field | :heavy_check_mark: |  |
| [FieldElement51::add](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L222) | curve25519_dalek::backend::serial::u64::field | :heavy_check_mark: |  |
| [FieldElement51::sub](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L316) | curve25519_dalek::backend::serial::u64::field | :heavy_check_mark: |  |
| [FieldElement51::mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L390) | curve25519_dalek::backend::serial::u64::field | :heavy_check_mark: |  |
| [FieldElement51::m](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L153) | curve25519_dalek::backend::serial::u64::field | :heavy_check_mark: | :heavy_check_mark: |
| [FieldElement51::neg](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L547) | curve25519_dalek::backend::serial::u64::field | :heavy_check_mark: |  |
| [FieldElement51::conditional_select](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L565) | curve25519_dalek::backend::serial::u64::field | :heavy_check_mark: | :heavy_check_mark: |
| [FieldElement51::from_limbs](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L670) | curve25519_dalek::backend::serial::u64::field |  |  |
| [FieldElement51::negate](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L690) | curve25519_dalek::backend::serial::u64::field | :heavy_check_mark: | :heavy_check_mark: |
| [FieldElement51::reduce](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L745) | curve25519_dalek::backend::serial::u64::field | :heavy_check_mark: | :heavy_check_mark: |
| [FieldElement51::from_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L807) | curve25519_dalek::backend::serial::u64::field | :heavy_check_mark: | :heavy_check_mark: |
| [FieldElement51::load8_at](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L134) | curve25519_dalek::backend::serial::u64::field | :heavy_check_mark: | :heavy_check_mark: |
| [FieldElement51::as_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L887) | curve25519_dalek::backend::serial::u64::field | :heavy_check_mark: | :heavy_check_mark: |
| [FieldElement51::pow2k](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L1009) | curve25519_dalek::backend::serial::u64::field | :heavy_check_mark: | :heavy_check_mark: |
| [FieldElement51::square](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L1155) | curve25519_dalek::backend::serial::u64::field | :heavy_check_mark: | :heavy_check_mark: |
| [FieldElement51::square2](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L1171) | curve25519_dalek::backend::serial::u64::field | :heavy_check_mark: | :heavy_check_mark: |
| [index](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L63) | curve25519_dalek::backend::serial::u64::scalar | :heavy_check_mark: | :heavy_check_mark: |
| [index_mut](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L76) | curve25519_dalek::backend::serial::u64::scalar |  |  |
| [m](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L85) | curve25519_dalek::backend::serial::u64::scalar | :heavy_check_mark: | :heavy_check_mark: |
| [Scalar52::from_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L105) | curve25519_dalek::backend::serial::u64::scalar | :heavy_check_mark: |  |
| [Scalar52::from_bytes_wide](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L155) | curve25519_dalek::backend::serial::u64::scalar | :heavy_check_mark: |  |
| [Scalar52::as_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L196) | curve25519_dalek::backend::serial::u64::scalar | :heavy_check_mark: | :heavy_check_mark: |
| [Scalar52::add](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L249) | curve25519_dalek::backend::serial::u64::scalar | :heavy_check_mark: | :heavy_check_mark: |
| [Scalar52::sub](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L438) | curve25519_dalek::backend::serial::u64::scalar | :heavy_check_mark: | :heavy_check_mark: |
| [Scalar52::mul_internal](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L595) | curve25519_dalek::backend::serial::u64::scalar | :heavy_check_mark: | :heavy_check_mark: |
| [Scalar52::square_internal](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L655) | curve25519_dalek::backend::serial::u64::scalar | :heavy_check_mark: | :heavy_check_mark: |
| [Scalar52::montgomery_reduce](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L687) | curve25519_dalek::backend::serial::u64::scalar | :heavy_check_mark: |  |
| [Scalar52::part1](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L724) | curve25519_dalek::backend::serial::u64::scalar | :heavy_check_mark: |  |
| [Scalar52::part2](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L762) | curve25519_dalek::backend::serial::u64::scalar | :heavy_check_mark: |  |
| [Scalar52::mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L781) | curve25519_dalek::backend::serial::u64::scalar | :heavy_check_mark: |  |
| [Scalar52::montgomery_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L814) | curve25519_dalek::backend::serial::u64::scalar | :heavy_check_mark: | :heavy_check_mark: |
| [Scalar52::montgomery_square](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L828) | curve25519_dalek::backend::serial::u64::scalar | :heavy_check_mark: | :heavy_check_mark: |
| [Scalar52::as_montgomery](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L841) | curve25519_dalek::backend::serial::u64::scalar | :heavy_check_mark: |  |
| [Scalar52::from_montgomery](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L861) | curve25519_dalek::backend::serial::u64::scalar | :heavy_check_mark: | :heavy_check_mark: |
| [CompressedEdwardsY::as_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L199) | curve25519_dalek::edwards | :heavy_check_mark: | :heavy_check_mark: |
| [CompressedEdwardsY::decompress](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L218) | curve25519_dalek::edwards | :heavy_check_mark: |  |
| [step_1](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L269) | curve25519_dalek::edwards | :heavy_check_mark: |  |
| [step_2](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L332) | curve25519_dalek::edwards | :heavy_check_mark: |  |
| [CompressedEdwardsY::identity](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L549) | curve25519_dalek::edwards | :heavy_check_mark: |  |
| [EdwardsPoint::conditional_select](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L729) | curve25519_dalek::edwards |  |  |
| [CompressedEdwardsY::ct_eq](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L175) | curve25519_dalek::edwards | :heavy_check_mark: | :heavy_check_mark: |
| [EdwardsPoint::as_projective_niels](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L772) | curve25519_dalek::edwards |  |  |
| [EdwardsPoint::as_projective](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L798) | curve25519_dalek::edwards |  |  |
| [EdwardsPoint::as_affine_niels](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L804) | curve25519_dalek::edwards |  |  |
| [EdwardsPoint::to_montgomery](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L822) | curve25519_dalek::edwards |  |  |
| [EdwardsPoint::compress](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L836) | curve25519_dalek::edwards |  |  |
| [EdwardsPoint::double](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L889) | curve25519_dalek::edwards |  |  |
| [EdwardsPoint::add](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L900) | curve25519_dalek::edwards |  |  |
| [EdwardsPoint::add_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L912) | curve25519_dalek::edwards |  |  |
| [EdwardsPoint::sub](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L921) | curve25519_dalek::edwards |  |  |
| [EdwardsPoint::sub_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L933) | curve25519_dalek::edwards |  |  |
| [EdwardsPoint::neg](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L972) | curve25519_dalek::edwards |  |  |
| [EdwardsPoint::mul_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L982) | curve25519_dalek::edwards |  |  |
| [EdwardsPoint::mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L1011) | curve25519_dalek::edwards |  |  |
| [EdwardsPoint::mul_base](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L1021) | curve25519_dalek::edwards |  |  |
| [EdwardsPoint::mul_base_clamped](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L1051) | curve25519_dalek::edwards |  |  |
| [EdwardsPoint::multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L1073) | curve25519_dalek::edwards |  |  |
| [EdwardsPoint::optional_multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L1105) | curve25519_dalek::edwards |  |  |
| [EdwardsPoint::vartime_double_scalar_mul_basepoint](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L1175) | curve25519_dalek::edwards |  |  |
| [EdwardsPoint::create](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L1226) | curve25519_dalek::edwards |  |  |
| [EdwardsPoint::basepoint](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L1239) | curve25519_dalek::edwards |  |  |
| [EdwardsPoint::mul_by_pow_2](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L1465) | curve25519_dalek::edwards |  |  |
| [EdwardsPoint::is_torsion_free](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L1530) | curve25519_dalek::edwards |  |  |
| [CompressedEdwardsY::fmt](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L192) | curve25519_dalek::edwards | :x: |  |
| [FieldElement::eq](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/field.rs#L71) | curve25519_dalek::field | :heavy_check_mark: |  |
| [FieldElement::ct_eq](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/field.rs#L104) | curve25519_dalek::field | :heavy_check_mark: |  |
| [FieldElement::is_negative](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/field.rs#L139) | curve25519_dalek::field | :heavy_check_mark: |  |
| [FieldElement::is_zero](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/field.rs#L164) | curve25519_dalek::field | :heavy_check_mark: |  |
| [FieldElement::pow22501](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/field.rs#L189) | curve25519_dalek::field | :heavy_check_mark: |  |
| [FieldElement::batch_invert](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/field.rs#L238) | curve25519_dalek::field | :heavy_check_mark: |  |
| [FieldElement::invert](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/field.rs#L384) | curve25519_dalek::field | :heavy_check_mark: |  |
| [FieldElement::pow_p58](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/field.rs#L411) | curve25519_dalek::field | :heavy_check_mark: |  |
| [FieldElement::sqrt_ratio_i](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/field.rs#L442) | curve25519_dalek::field | :heavy_check_mark: |  |
| [FieldElement::invsqrt](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/field.rs#L548) | curve25519_dalek::field | :heavy_check_mark: |  |
| [JacobiPoint::elligator_inv](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/lizard/jacobi_quartic.rs#L29) | curve25519_dalek::lizard::jacobi_quartic |  |  |
| [JacobiPoint::dual](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/lizard/jacobi_quartic.rs#L65) | curve25519_dalek::lizard::jacobi_quartic |  |  |
| [RistrettoPoint::from_uniform_bytes_single_elligator](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/lizard/lizard_ristretto.rs#L25) | curve25519_dalek::lizard::lizard_ristretto |  |  |
| [RistrettoPoint::lizard_encode](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/lizard/lizard_ristretto.rs#L30) | curve25519_dalek::lizard::lizard_ristretto |  |  |
| [RistrettoPoint::lizard_decode](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/lizard/lizard_ristretto.rs#L46) | curve25519_dalek::lizard::lizard_ristretto |  |  |
| [RistrettoPoint::decode_253_bits](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/lizard/lizard_ristretto.rs#L86) | curve25519_dalek::lizard::lizard_ristretto |  |  |
| [RistrettoPoint::elligator_ristretto_flavor_inverse](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/lizard/lizard_ristretto.rs#L111) | curve25519_dalek::lizard::lizard_ristretto |  |  |
| [RistrettoPoint::to_jacobi_quartic_ristretto](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/lizard/lizard_ristretto.rs#L158) | curve25519_dalek::lizard::lizard_ristretto |  |  |
| [field_element](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/lizard/u64_constants.rs#L3) | curve25519_dalek::lizard::u64_constants |  |  |
| [add](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/macros.rs#L17) | curve25519_dalek::macros |  |  |
| [add_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/macros.rs#L42) | curve25519_dalek::macros |  |  |
| [sub](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/macros.rs#L54) | curve25519_dalek::macros |  |  |
| [sub_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/macros.rs#L79) | curve25519_dalek::macros |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/macros.rs#L91) | curve25519_dalek::macros |  |  |
| [mul_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/macros.rs#L116) | curve25519_dalek::macros |  |  |
| [MontgomeryPoint::ct_eq](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/montgomery.rs#L81) | curve25519_dalek::montgomery |  |  |
| [MontgomeryPoint::eq](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/montgomery.rs#L90) | curve25519_dalek::montgomery |  |  |
| [MontgomeryPoint::hash](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/montgomery.rs#L100) | curve25519_dalek::montgomery |  |  |
| [MontgomeryPoint::zeroize](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/montgomery.rs#L117) | curve25519_dalek::montgomery |  |  |
| [MontgomeryPoint::mul_clamped](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/montgomery.rs#L130) | curve25519_dalek::montgomery |  |  |
| [MontgomeryPoint::mul_bits_be](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/montgomery.rs#L163) | curve25519_dalek::montgomery |  |  |
| [MontgomeryPoint::as_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/montgomery.rs#L194) | curve25519_dalek::montgomery |  |  |
| [MontgomeryPoint::to_edwards](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/montgomery.rs#L219) | curve25519_dalek::montgomery |  |  |
| [MontgomeryPoint::identity](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/montgomery.rs#L110) | curve25519_dalek::montgomery |  |  |
| [ProjectivePoint::conditional_select](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/montgomery.rs#L305) | curve25519_dalek::montgomery |  |  |
| [ProjectivePoint::as_affine](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/montgomery.rs#L324) | curve25519_dalek::montgomery |  |  |
| [ProjectivePoint::differential_add_and_double](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/montgomery.rs#L345) | curve25519_dalek::montgomery |  |  |
| [ProjectivePoint::mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/montgomery.rs#L403) | curve25519_dalek::montgomery |  |  |
| [ProjectivePoint::mul_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/montgomery.rs#L411) | curve25519_dalek::montgomery |  |  |
| [CompressedRistretto::to_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L228) | curve25519_dalek::ristretto |  |  |
| [CompressedRistretto::as_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L233) | curve25519_dalek::ristretto |  |  |
| [CompressedRistretto::from_slice](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L243) | curve25519_dalek::ristretto |  |  |
| [CompressedRistretto::decompress](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L254) | curve25519_dalek::ristretto |  |  |
| [step_1](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L274) | curve25519_dalek::ristretto |  |  |
| [step_2](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L294) | curve25519_dalek::ristretto |  |  |
| [CompressedRistretto::identity](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L336) | curve25519_dalek::ristretto |  |  |
| [RistrettoPoint::serialize](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L370) | curve25519_dalek::ristretto |  |  |
| [CompressedRistretto::deserialize](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L400) | curve25519_dalek::ristretto |  |  |
| [CompressedRistretto::expecting](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L409) | curve25519_dalek::ristretto |  |  |
| [RistrettoPoint::compress](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L488) | curve25519_dalek::ristretto |  |  |
| [RistrettoPoint::double_and_compress_batch](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L552) | curve25519_dalek::ristretto |  |  |
| [BatchCompressState::efgh](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L567) | curve25519_dalek::ristretto |  |  |
| [BatchCompressState::from](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L574) | curve25519_dalek::ristretto |  |  |
| [BatchCompressState::coset4](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L638) | curve25519_dalek::ristretto |  |  |
| [BatchCompressState::elligator_ristretto_flavor](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L655) | curve25519_dalek::ristretto |  |  |
| [BatchCompressState::from_uniform_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L786) | curve25519_dalek::ristretto |  |  |
| [CompressedRistretto::default](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L342) | curve25519_dalek::ristretto |  |  |
| [RistrettoPoint::eq](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L822) | curve25519_dalek::ristretto |  |  |
| [CompressedRistretto::ct_eq](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L221) | curve25519_dalek::ristretto |  |  |
| [RistrettoPoint::add](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L853) | curve25519_dalek::ristretto |  |  |
| [RistrettoPoint::add_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L865) | curve25519_dalek::ristretto |  |  |
| [RistrettoPoint::sub](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L875) | curve25519_dalek::ristretto |  |  |
| [RistrettoPoint::sub_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L887) | curve25519_dalek::ristretto |  |  |
| [RistrettoPoint::sum](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L898) | curve25519_dalek::ristretto |  |  |
| [RistrettoPoint::neg](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L909) | curve25519_dalek::ristretto |  |  |
| [RistrettoPoint::mul_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L923) | curve25519_dalek::ristretto |  |  |
| [RistrettoPoint::mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L932) | curve25519_dalek::ristretto |  |  |
| [RistrettoPoint::mul_base](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L951) | curve25519_dalek::ristretto |  |  |
| [RistrettoPoint::multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L980) | curve25519_dalek::ristretto |  |  |
| [RistrettoPoint::optional_multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L996) | curve25519_dalek::ristretto |  |  |
| [RistrettoPoint::conditional_select](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L1143) | curve25519_dalek::ristretto |  |  |
| [CompressedRistretto::fmt](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L1157) | curve25519_dalek::ristretto |  |  |
| [Scalar::from_bytes_mod_order](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L238) | curve25519_dalek::scalar | :heavy_check_mark: | :heavy_check_mark: |
| [Scalar::from_bytes_mod_order_wide](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L261) | curve25519_dalek::scalar | :heavy_check_mark: |  |
| [Scalar::from_canonical_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L285) | curve25519_dalek::scalar | :heavy_check_mark: |  |
| [Scalar::eq](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L349) | curve25519_dalek::scalar | :heavy_check_mark: |  |
| [Scalar::ct_eq](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L376) | curve25519_dalek::scalar | :heavy_check_mark: | :heavy_check_mark: |
| [Scalar::index](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L394) | curve25519_dalek::scalar | :heavy_check_mark: | :heavy_check_mark: |
| [Scalar::mul_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L414) | curve25519_dalek::scalar | :heavy_check_mark: |  |
| [Scalar::mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L492) | curve25519_dalek::scalar | :heavy_check_mark: |  |
| [Scalar::add_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L632) | curve25519_dalek::scalar | :heavy_check_mark: | :heavy_check_mark: |
| [Scalar::add](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L567) | curve25519_dalek::scalar | :heavy_check_mark: |  |
| [Scalar::sub](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L667) | curve25519_dalek::scalar | :heavy_check_mark: |  |
| [Scalar::neg](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L767) | curve25519_dalek::scalar | :heavy_check_mark: |  |
| [Scalar::serialize](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L1722) | curve25519_dalek::scalar | :x: |  |
| [Scalar::deserialize](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L1736) | curve25519_dalek::scalar | :x: |  |
| [Scalar::expecting](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L1692) | curve25519_dalek::scalar | :x: |  |
| [Scalar::sum](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L896) | curve25519_dalek::scalar | :x: |  |
| [Scalar::default](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L918) | curve25519_dalek::scalar | :heavy_check_mark: |  |
| [Scalar::from](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L930) | curve25519_dalek::scalar | :heavy_check_mark: |  |
| [Scalar::hash_from_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L1228) | curve25519_dalek::scalar | :x: |  |
| [Scalar::from_hash](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L1304) | curve25519_dalek::scalar | :x: |  |
| [Scalar::to_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L1352) | curve25519_dalek::scalar | :heavy_check_mark: | :heavy_check_mark: |
| [Scalar::as_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L1371) | curve25519_dalek::scalar | :heavy_check_mark: | :heavy_check_mark: |
| [Scalar::invert](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L1419) | curve25519_dalek::scalar | :heavy_check_mark: |  |
| [Scalar::bits_le](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L1798) | curve25519_dalek::scalar |  |  |
| [non_adjacent_form](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L1946) | curve25519_dalek::scalar | :heavy_check_mark: |  |
| [bot_half](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L1752) | curve25519_dalek::scalar | :heavy_check_mark: | :heavy_check_mark: |
| [top_half](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L1774) | curve25519_dalek::scalar | :heavy_check_mark: | :heavy_check_mark: |
| [as_radix_16](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L2084) | curve25519_dalek::scalar | :heavy_check_mark: |  |
| [to_radix_2w_size_hint](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L2156) | curve25519_dalek::scalar | :heavy_check_mark: | :heavy_check_mark: |
| [as_radix_2w](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L2215) | curve25519_dalek::scalar | :heavy_check_mark: |  |
| [unpack](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L2415) | curve25519_dalek::scalar | :heavy_check_mark: | :heavy_check_mark: |
| [reduce](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L2429) | curve25519_dalek::scalar | :heavy_check_mark: |  |
| [is_canonical](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L2455) | curve25519_dalek::scalar | :heavy_check_mark: |  |
| [square_multiply](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L2474) | curve25519_dalek::scalar | :heavy_check_mark: |  |
| [UnpackedScalar::pack](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L2524) | curve25519_dalek::scalar | :heavy_check_mark: |  |
| [UnpackedScalar::montgomery_invert](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L2551) | curve25519_dalek::scalar | :heavy_check_mark: |  |
| [read_le_u64_into](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L2797) | curve25519_dalek::scalar | :heavy_check_mark: |  |
| [clamp_integer](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L2877) | curve25519_dalek::scalar | :heavy_check_mark: |  |
| [identity](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/traits.rs#L27) | curve25519_dalek::traits |  |  |
| [is_identity](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/traits.rs#L33) | curve25519_dalek::traits |  |  |
| [create](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/traits.rs#L54) | curve25519_dalek::traits |  |  |
| [basepoint](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/traits.rs#L57) | curve25519_dalek::traits |  |  |
| [mul_base](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/traits.rs#L60) | curve25519_dalek::traits |  |  |
| [multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/traits.rs#L126) | curve25519_dalek::traits |  |  |
| [optional_multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/traits.rs#L194) | curve25519_dalek::traits |  |  |
| [vartime_multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/traits.rs#L247) | curve25519_dalek::traits |  |  |
| [new](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/traits.rs#L295) | curve25519_dalek::traits |  |  |
| [optional_mixed_multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/traits.rs#L386) | curve25519_dalek::traits |  |  |
| [is_valid](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/traits.rs#L412) | curve25519_dalek::traits |  |  |
| [select](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/window.rs#L52) | curve25519_dalek::window |  |  |
| [default](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/window.rs#L78) | curve25519_dalek::window |  |  |
| [from](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/window.rs#L96) | curve25519_dalek::window |  |  |
