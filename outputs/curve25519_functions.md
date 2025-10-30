# Curve25519 Functions

| Function | Has Spec (Verus) | Has Proof (Verus) | Has Spec (Lean) | Has Proof (Lean) |
|----------|:------------------:|:-------------------:|:----------------:|:-----------------:|
| [fmt](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/build.rs#L14) |  |  |  |  |
| [is_capable_simd](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/build.rs#L76) |  |  |  |  |
| [determine_curve25519_dalek_bits_warning](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/build.rs#L93) |  |  |  |  |
| [determine_curve25519_dalek_bits](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/build.rs#L98) |  |  |  |  |
| [get_selected_backend](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/mod.rs#L53) |  |  |  |  |
| [pippenger_optional_multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/mod.rs#L77) |  |  |  |  |
| [straus_multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/mod.rs#L174) |  |  |  |  |
| [straus_optional_multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/mod.rs#L202) |  |  |  |  |
| [variable_base_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/mod.rs#L231) |  |  |  |  |
| [vartime_double_base_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/mod.rs#L245) |  |  |  |  |
| [identity](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L234) |  |  |  |  |
| [identity](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L234) |  |  |  |  |
| [identity](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L234) |  |  |  |  |
| [default](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L252) |  |  |  |  |
| [conditional_select](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L297) |  |  |  |  |
| [conditional_select](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L297) |  |  |  |  |
| [as_extended](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L339) |  |  |  |  |
| [as_projective](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L354) |  |  |  |  |
| [as_extended](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L339) |  |  |  |  |
| [double](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L382) |  |  |  |  |
| [add](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L415) |  |  |  |  |
| [sub](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L437) |  |  |  |  |
| [add](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L415) |  |  |  |  |
| [sub](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L437) |  |  |  |  |
| [neg](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L504) |  |  |  |  |
| [neg](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L504) |  |  |  |  |
| [optional_multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/scalar_mul/pippenger.rs#L65) |  |  |  |  |
| [multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/scalar_mul/straus.rs#L101) |  |  |  |  |
| [optional_multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/scalar_mul/straus.rs#L157) |  |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/scalar_mul/variable_base.rs#L11) |  |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/scalar_mul/vartime_double_base.rs#L23) |  |  |  |  |
| [fmt](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L111) | :x: |  |  |  |
| [add_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L164) |  |  |  |  |
| [add](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L203) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [sub](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L262) |  |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L299) |  |  |  |  |
| [m](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L151) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [neg](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L427) |  |  |  |  |
| [conditional_select](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L439) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [from_limbs](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L544) |  |  |  |  |
| [negate](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L564) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [reduce](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L619) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [from_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L681) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [load8_at](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L132) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [as_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L761) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [pow2k](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L883) | :heavy_check_mark: |  |  |  |
| [m](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L151) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [square](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L1011) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [square2](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L1027) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [load8_at](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field_verus.rs#L50) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [m](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field_verus.rs#L69) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [from_limbs](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field_verus.rs#L87) |  |  |  |  |
| [negate](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field_verus.rs#L108) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [reduce](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field_verus.rs#L163) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [from_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field_verus.rs#L230) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [to_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field_verus.rs#L298) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [pow2k](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field_verus.rs#L468) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [square](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field_verus.rs#L1004) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [square2](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field_verus.rs#L1020) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [index](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L61) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [index_mut](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L74) |  |  |  |  |
| [m](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L83) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [from_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L103) | :heavy_check_mark: |  |  |  |
| [from_bytes_wide](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L153) | :heavy_check_mark: |  |  |  |
| [as_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L194) | :heavy_check_mark: |  |  |  |
| [add](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L239) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [sub](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L428) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [mul_internal](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L585) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [square_internal](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L645) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [montgomery_reduce](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L677) | :heavy_check_mark: |  |  |  |
| [part1](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L714) | :heavy_check_mark: |  |  |  |
| [part2](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L752) | :heavy_check_mark: |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L771) | :heavy_check_mark: |  |  |  |
| [montgomery_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L804) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [montgomery_square](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L818) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [as_montgomery](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L831) | :heavy_check_mark: |  |  |  |
| [from_montgomery](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L851) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [as_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L198) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [decompress](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L217) |  |  |  |  |
| [step_1](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L232) |  |  |  |  |
| [step_2](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L250) |  |  |  |  |
| [identity](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L417) |  |  |  |  |
| [conditional_select](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L556) |  |  |  |  |
| [ct_eq](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L174) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [as_projective_niels](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L597) |  |  |  |  |
| [as_projective](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L610) |  |  |  |  |
| [as_affine_niels](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L620) |  |  |  |  |
| [to_montgomery](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L641) |  |  |  |  |
| [compress](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L665) |  |  |  |  |
| [double](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L719) |  |  |  |  |
| [add](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L730) |  |  |  |  |
| [add_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L742) |  |  |  |  |
| [sub](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L751) |  |  |  |  |
| [sub_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L763) |  |  |  |  |
| [neg](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L789) |  |  |  |  |
| [neg](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L789) |  |  |  |  |
| [mul_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L812) |  |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L829) |  |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L829) |  |  |  |  |
| [mul_base](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L851) |  |  |  |  |
| [mul_base_clamped](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L881) |  |  |  |  |
| [multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L903) |  |  |  |  |
| [optional_multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L935) |  |  |  |  |
| [vartime_double_scalar_mul_basepoint](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L1005) |  |  |  |  |
| [create](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L1056) |  |  |  |  |
| [basepoint](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L1069) |  |  |  |  |
| [mul_base](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L851) |  |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L829) |  |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L829) |  |  |  |  |
| [mul_by_pow_2](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L1295) |  |  |  |  |
| [is_torsion_free](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L1360) |  |  |  |  |
| [fmt](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L191) | :x: |  |  |  |
| [eq](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/field.rs#L71) | :heavy_check_mark: |  |  |  |
| [ct_eq](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/field.rs#L104) | :heavy_check_mark: |  |  |  |
| [is_negative](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/field.rs#L139) | :heavy_check_mark: |  |  |  |
| [is_zero](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/field.rs#L164) | :heavy_check_mark: |  |  |  |
| [pow22501](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/field.rs#L189) | :heavy_check_mark: |  |  |  |
| [batch_invert](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/field.rs#L238) | :heavy_check_mark: |  |  |  |
| [invert](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/field.rs#L384) | :heavy_check_mark: |  |  |  |
| [pow_p58](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/field.rs#L411) | :heavy_check_mark: |  |  |  |
| [sqrt_ratio_i](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/field.rs#L442) | :heavy_check_mark: |  |  |  |
| [invsqrt](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/field.rs#L548) | :heavy_check_mark: |  |  |  |
| [elligator_inv](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/lizard/jacobi_quartic.rs#L29) |  |  |  |  |
| [dual](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/lizard/jacobi_quartic.rs#L65) |  |  |  |  |
| [from_uniform_bytes_single_elligator](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/lizard/lizard_ristretto.rs#L25) |  |  |  |  |
| [lizard_encode](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/lizard/lizard_ristretto.rs#L30) |  |  |  |  |
| [lizard_decode](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/lizard/lizard_ristretto.rs#L46) |  |  |  |  |
| [decode_253_bits](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/lizard/lizard_ristretto.rs#L86) |  |  |  |  |
| [elligator_ristretto_flavor_inverse](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/lizard/lizard_ristretto.rs#L111) |  |  |  |  |
| [to_jacobi_quartic_ristretto](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/lizard/lizard_ristretto.rs#L158) |  |  |  |  |
| [field_element](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/lizard/u64_constants.rs#L3) |  |  |  |  |
| [add](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/macros.rs#L17) |  |  |  |  |
| [add](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/macros.rs#L17) |  |  |  |  |
| [add](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/macros.rs#L17) |  |  |  |  |
| [add_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/macros.rs#L42) |  |  |  |  |
| [sub](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/macros.rs#L54) |  |  |  |  |
| [sub_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/macros.rs#L79) |  |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/macros.rs#L91) |  |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/macros.rs#L91) |  |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/macros.rs#L91) |  |  |  |  |
| [mul_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/macros.rs#L116) |  |  |  |  |
| [ct_eq](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/montgomery.rs#L77) |  |  |  |  |
| [eq](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/montgomery.rs#L86) |  |  |  |  |
| [hash](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/montgomery.rs#L96) |  |  |  |  |
| [zeroize](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/montgomery.rs#L113) |  |  |  |  |
| [mul_clamped](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/montgomery.rs#L126) |  |  |  |  |
| [mul_bits_be](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/montgomery.rs#L159) |  |  |  |  |
| [as_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/montgomery.rs#L190) |  |  |  |  |
| [to_edwards](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/montgomery.rs#L215) |  |  |  |  |
| [identity](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/montgomery.rs#L106) |  |  |  |  |
| [conditional_select](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/montgomery.rs#L301) |  |  |  |  |
| [as_affine](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/montgomery.rs#L320) |  |  |  |  |
| [differential_add_and_double](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/montgomery.rs#L341) |  |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/montgomery.rs#L399) |  |  |  |  |
| [mul_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/montgomery.rs#L407) |  |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/montgomery.rs#L399) |  |  |  |  |
| [to_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L228) |  |  |  |  |
| [as_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L233) |  |  |  |  |
| [from_slice](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L243) |  |  |  |  |
| [decompress](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L254) |  |  |  |  |
| [step_1](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L274) |  |  |  |  |
| [step_2](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L294) |  |  |  |  |
| [identity](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L336) |  |  |  |  |
| [serialize](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L370) |  |  |  |  |
| [serialize](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L370) |  |  |  |  |
| [deserialize](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L400) |  |  |  |  |
| [expecting](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L409) |  |  |  |  |
| [deserialize](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L400) |  |  |  |  |
| [expecting](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L409) |  |  |  |  |
| [compress](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L488) |  |  |  |  |
| [double_and_compress_batch](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L552) |  |  |  |  |
| [efgh](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L567) |  |  |  |  |
| [from](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L574) |  |  |  |  |
| [coset4](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L638) |  |  |  |  |
| [elligator_ristretto_flavor](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L655) |  |  |  |  |
| [from_uniform_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L786) |  |  |  |  |
| [identity](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L336) |  |  |  |  |
| [default](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L342) |  |  |  |  |
| [eq](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L822) |  |  |  |  |
| [ct_eq](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L221) |  |  |  |  |
| [add](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L853) |  |  |  |  |
| [add_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L865) |  |  |  |  |
| [sub](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L875) |  |  |  |  |
| [sub_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L887) |  |  |  |  |
| [sum](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L898) |  |  |  |  |
| [neg](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L909) |  |  |  |  |
| [neg](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L909) |  |  |  |  |
| [mul_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L923) |  |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L932) |  |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L932) |  |  |  |  |
| [mul_base](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L951) |  |  |  |  |
| [multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L980) |  |  |  |  |
| [optional_multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L996) |  |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L932) |  |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L932) |  |  |  |  |
| [conditional_select](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L1143) |  |  |  |  |
| [fmt](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/ristretto.rs#L1157) |  |  |  |  |
| [from_bytes_mod_order](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L231) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [from_bytes_mod_order_wide](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L254) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [from_canonical_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L275) | :heavy_check_mark: |  |  |  |
| [eq](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L339) | :heavy_check_mark: |  |  |  |
| [ct_eq](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L366) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [index](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L384) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [mul_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L404) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L457) | :heavy_check_mark: |  |  |  |
| [add_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L578) | :heavy_check_mark: |  |  |  |
| [add](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L513) | :heavy_check_mark: |  |  |  |
| [sub](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L599) | :heavy_check_mark: |  |  |  |
| [neg](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L678) | :heavy_check_mark: |  |  |  |
| [neg](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L678) | :heavy_check_mark: |  |  |  |
| [serialize](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L1626) | :x: |  |  |  |
| [deserialize](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L1640) | :x: |  |  |  |
| [expecting](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L1596) | :x: |  |  |  |
| [sum](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L800) | :x: |  |  |  |
| [default](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L822) | :heavy_check_mark: |  |  |  |
| [from](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L834) | :heavy_check_mark: |  |  |  |
| [from](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L834) | :heavy_check_mark: |  |  |  |
| [hash_from_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L1132) | :x: |  |  |  |
| [from_hash](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L1208) | :x: |  |  |  |
| [to_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L1256) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [as_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L1275) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [invert](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L1323) | :heavy_check_mark: |  |  |  |
| [bits_le](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L1702) |  |  |  |  |
| [non_adjacent_form](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L1850) | :heavy_check_mark: |  |  |  |
| [bot_half](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L1656) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [top_half](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L1678) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [as_radix_16](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L1988) | :heavy_check_mark: |  |  |  |
| [to_radix_2w_size_hint](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L2060) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [as_radix_2w](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L2119) | :heavy_check_mark: |  |  |  |
| [unpack](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L2319) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [reduce](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L2333) | :heavy_check_mark: |  |  |  |
| [is_canonical](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L2359) | :heavy_check_mark: |  |  |  |
| [square_multiply](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L2378) | :heavy_check_mark: |  |  |  |
| [pack](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L2428) | :heavy_check_mark: |  |  |  |
| [montgomery_invert](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L2448) | :heavy_check_mark: |  |  |  |
| [invert](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L1323) | :heavy_check_mark: |  |  |  |
| [read_le_u64_into](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L2694) | :heavy_check_mark: |  |  |  |
| [clamp_integer](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L2774) | :heavy_check_mark: |  |  |  |
| [identity](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/traits.rs#L27) |  |  |  |  |
| [is_identity](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/traits.rs#L33) |  |  |  |  |
| [is_identity](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/traits.rs#L33) |  |  |  |  |
| [create](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/traits.rs#L54) |  |  |  |  |
| [basepoint](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/traits.rs#L57) |  |  |  |  |
| [mul_base](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/traits.rs#L60) |  |  |  |  |
| [multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/traits.rs#L126) |  |  |  |  |
| [optional_multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/traits.rs#L194) |  |  |  |  |
| [vartime_multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/traits.rs#L247) |  |  |  |  |
| [new](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/traits.rs#L295) |  |  |  |  |
| [optional_mixed_multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/traits.rs#L386) |  |  |  |  |
| [is_valid](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/traits.rs#L412) |  |  |  |  |
| [select](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/window.rs#L52) |  |  |  |  |
| [default](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/window.rs#L78) |  |  |  |  |
| [from](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/window.rs#L96) |  |  |  |  |
| [from](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/window.rs#L96) |  |  |  |  |
| [select](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/window.rs#L52) |  |  |  |  |
| [from](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/window.rs#L96) |  |  |  |  |
| [select](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/window.rs#L52) |  |  |  |  |
