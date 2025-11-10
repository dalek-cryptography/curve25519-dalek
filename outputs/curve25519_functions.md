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
| [identity](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L238) |  |  |  |  |
| [identity](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L238) |  |  |  |  |
| [identity](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L238) |  |  |  |  |
| [default](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L256) |  |  |  |  |
| [conditional_select](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L360) |  |  |  |  |
| [conditional_select](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L360) |  |  |  |  |
| [as_extended](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L402) |  |  |  |  |
| [as_projective](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L417) |  |  |  |  |
| [as_extended](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L402) |  |  |  |  |
| [double](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L445) |  |  |  |  |
| [add](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L478) |  |  |  |  |
| [sub](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L500) |  |  |  |  |
| [add](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L478) |  |  |  |  |
| [sub](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L500) |  |  |  |  |
| [neg](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L567) |  |  |  |  |
| [neg](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L567) |  |  |  |  |
| [optional_multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/scalar_mul/pippenger.rs#L65) |  |  |  |  |
| [multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/scalar_mul/straus.rs#L101) |  |  |  |  |
| [optional_multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/scalar_mul/straus.rs#L157) |  |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/scalar_mul/variable_base.rs#L11) |  |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/scalar_mul/vartime_double_base.rs#L23) |  |  |  |  |
| [fmt](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L113) | :x: |  |  |  |
| [add_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L166) | :heavy_check_mark: |  |  |  |
| [add](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L222) | :heavy_check_mark: |  |  |  |
| [sub](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L316) | :heavy_check_mark: |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L391) | :heavy_check_mark: |  |  |  |
| [m](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L153) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [neg](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L549) | :heavy_check_mark: |  |  |  |
| [conditional_select](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L567) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [from_limbs](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L672) |  |  |  |  |
| [negate](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L692) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [reduce](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L747) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [from_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L809) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [load8_at](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L134) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [as_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L889) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [pow2k](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L1011) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [m](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L153) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [square](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L1157) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [square2](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L1173) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [fmt](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L113) | :x: |  |  |  |
| [add_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L166) | :heavy_check_mark: |  |  |  |
| [add](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L222) | :heavy_check_mark: |  |  |  |
| [sub](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L316) | :heavy_check_mark: |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L391) | :heavy_check_mark: |  |  |  |
| [m](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L153) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [neg](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L549) | :heavy_check_mark: |  |  |  |
| [conditional_select](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L567) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [from_limbs](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L672) |  |  |  |  |
| [negate](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L692) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [reduce](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L747) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [from_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L809) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [load8_at](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L134) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [as_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L889) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [pow2k](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L1011) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [m](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L153) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [square](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L1157) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [square2](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/field.rs#L1173) | :heavy_check_mark: | :heavy_check_mark: |  |  |
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
| [index](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L63) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [index_mut](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L76) |  |  |  |  |
| [m](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L85) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [from_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L105) | :heavy_check_mark: |  |  |  |
| [from_bytes_wide](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L155) | :heavy_check_mark: |  |  |  |
| [as_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L196) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [add](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L249) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [sub](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L438) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [mul_internal](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L595) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [square_internal](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L655) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [montgomery_reduce](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L687) | :heavy_check_mark: |  |  |  |
| [part1](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L724) | :heavy_check_mark: |  |  |  |
| [part2](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L762) | :heavy_check_mark: |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L781) | :heavy_check_mark: |  |  |  |
| [montgomery_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L814) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [montgomery_square](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L828) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [as_montgomery](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L841) | :heavy_check_mark: |  |  |  |
| [from_montgomery](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/backend/serial/u64/scalar.rs#L861) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [as_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L201) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [decompress](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L220) | :heavy_check_mark: |  |  |  |
| [step_1](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L271) | :heavy_check_mark: |  |  |  |
| [step_2](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L334) | :heavy_check_mark: |  |  |  |
| [identity](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L551) | :heavy_check_mark: |  |  |  |
| [conditional_select](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L751) |  |  |  |  |
| [ct_eq](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L177) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [as_projective_niels](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L794) | :heavy_check_mark: |  |  |  |
| [as_projective](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L833) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [as_affine_niels](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L844) | :heavy_check_mark: |  |  |  |
| [to_montgomery](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L896) |  |  |  |  |
| [compress](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L910) |  |  |  |  |
| [double](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L963) |  |  |  |  |
| [add](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L974) |  |  |  |  |
| [add_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L986) |  |  |  |  |
| [sub](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L995) |  |  |  |  |
| [sub_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L1007) |  |  |  |  |
| [neg](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L1033) |  |  |  |  |
| [neg](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L1033) |  |  |  |  |
| [mul_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L1056) |  |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L1073) |  |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L1073) |  |  |  |  |
| [mul_base](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L1095) |  |  |  |  |
| [mul_base_clamped](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L1125) |  |  |  |  |
| [multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L1147) |  |  |  |  |
| [optional_multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L1179) |  |  |  |  |
| [vartime_double_scalar_mul_basepoint](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L1249) |  |  |  |  |
| [create](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L1300) |  |  |  |  |
| [basepoint](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L1313) |  |  |  |  |
| [mul_base](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L1095) |  |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L1073) |  |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L1073) |  |  |  |  |
| [mul_by_pow_2](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L1539) |  |  |  |  |
| [is_torsion_free](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L1604) |  |  |  |  |
| [fmt](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/edwards.rs#L194) | :x: |  |  |  |
| [eq](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/field.rs#L82) | :heavy_check_mark: |  |  |  |
| [ct_eq](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/field.rs#L112) | :heavy_check_mark: |  |  |  |
| [is_negative](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/field.rs#L146) | :heavy_check_mark: |  |  |  |
| [is_zero](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/field.rs#L171) | :heavy_check_mark: |  |  |  |
| [pow22501](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/field.rs#L196) | :heavy_check_mark: |  |  |  |
| [batch_invert](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/field.rs#L245) | :heavy_check_mark: |  |  |  |
| [invert](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/field.rs#L391) | :heavy_check_mark: |  |  |  |
| [pow_p58](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/field.rs#L419) | :heavy_check_mark: |  |  |  |
| [sqrt_ratio_i](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/field.rs#L450) | :heavy_check_mark: |  |  |  |
| [invsqrt](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/field.rs#L556) | :heavy_check_mark: |  |  |  |
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
| [ct_eq](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/montgomery.rs#L81) |  |  |  |  |
| [eq](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/montgomery.rs#L90) |  |  |  |  |
| [hash](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/montgomery.rs#L100) |  |  |  |  |
| [zeroize](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/montgomery.rs#L117) |  |  |  |  |
| [mul_clamped](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/montgomery.rs#L130) |  |  |  |  |
| [mul_bits_be](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/montgomery.rs#L163) |  |  |  |  |
| [as_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/montgomery.rs#L194) |  |  |  |  |
| [to_edwards](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/montgomery.rs#L219) |  |  |  |  |
| [identity](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/montgomery.rs#L110) |  |  |  |  |
| [conditional_select](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/montgomery.rs#L305) |  |  |  |  |
| [as_affine](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/montgomery.rs#L324) |  |  |  |  |
| [differential_add_and_double](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/montgomery.rs#L345) |  |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/montgomery.rs#L403) |  |  |  |  |
| [mul_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/montgomery.rs#L411) |  |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/montgomery.rs#L403) |  |  |  |  |
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
| [from_bytes_mod_order](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L238) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [from_bytes_mod_order_wide](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L261) | :heavy_check_mark: |  |  |  |
| [from_canonical_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L285) | :heavy_check_mark: |  |  |  |
| [eq](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L361) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [ct_eq](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L382) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [index](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L400) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [mul_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L420) | :heavy_check_mark: |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L498) | :heavy_check_mark: |  |  |  |
| [add_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L638) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [add](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L573) | :heavy_check_mark: |  |  |  |
| [sub](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L673) | :heavy_check_mark: |  |  |  |
| [neg](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L773) | :heavy_check_mark: |  |  |  |
| [neg](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L773) | :heavy_check_mark: |  |  |  |
| [serialize](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L1728) | :x: |  |  |  |
| [deserialize](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L1742) | :x: |  |  |  |
| [expecting](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L1698) | :x: |  |  |  |
| [sum](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L902) | :x: |  |  |  |
| [default](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L924) | :heavy_check_mark: |  |  |  |
| [from](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L936) | :heavy_check_mark: |  |  |  |
| [from](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L936) | :heavy_check_mark: |  |  |  |
| [hash_from_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L1234) | :x: |  |  |  |
| [from_hash](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L1310) | :x: |  |  |  |
| [to_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L1358) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [as_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L1377) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [invert](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L1425) | :heavy_check_mark: |  |  |  |
| [bits_le](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L1804) |  |  |  |  |
| [non_adjacent_form](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L1952) | :heavy_check_mark: |  |  |  |
| [bot_half](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L1758) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [top_half](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L1780) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [as_radix_16](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L2090) | :heavy_check_mark: |  |  |  |
| [to_radix_2w_size_hint](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L2162) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [as_radix_2w](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L2221) | :heavy_check_mark: |  |  |  |
| [unpack](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L2421) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [reduce](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L2435) | :heavy_check_mark: |  |  |  |
| [is_canonical](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L2461) | :heavy_check_mark: |  |  |  |
| [square_multiply](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L2480) | :heavy_check_mark: |  |  |  |
| [pack](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L2530) | :heavy_check_mark: |  |  |  |
| [montgomery_invert](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L2557) | :heavy_check_mark: |  |  |  |
| [invert](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L1425) | :heavy_check_mark: |  |  |  |
| [read_le_u64_into](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L2803) | :heavy_check_mark: |  |  |  |
| [clamp_integer](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/curve25519-dalek/src/scalar.rs#L2883) | :heavy_check_mark: |  |  |  |
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
