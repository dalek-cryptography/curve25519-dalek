# Curve25519 Functions

| Function | Has Spec (Verus) | Has Proof (Verus) | Has Spec (Lean) | Has Proof (Lean) |
|----------|:------------------:|:-------------------:|:----------------:|:-----------------:|
| [fmt](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/build.rs#L15) |  |  |  |  |
| [is_capable_simd](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/build.rs#L77) |  |  |  |  |
| [determine_curve25519_dalek_bits_warning](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/build.rs#L94) |  |  |  |  |
| [determine_curve25519_dalek_bits](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/build.rs#L99) |  |  |  |  |
| [get_selected_backend](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/mod.rs#L55) |  |  |  |  |
| [pippenger_optional_multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/mod.rs#L79) |  |  |  |  |
| [straus_multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/mod.rs#L176) |  |  |  |  |
| [straus_optional_multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/mod.rs#L204) |  |  |  |  |
| [variable_base_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/mod.rs#L233) |  |  |  |  |
| [vartime_double_base_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/mod.rs#L247) |  |  |  |  |
| [identity](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L230) |  |  |  |  |
| [identity](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L240) |  |  |  |  |
| [identity](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L257) |  |  |  |  |
| [default](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L267) |  |  |  |  |
| [conditional_select](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L296) |  |  |  |  |
| [conditional_select](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L314) |  |  |  |  |
| [as_extended](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L338) |  |  |  |  |
| [as_projective](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L353) |  |  |  |  |
| [as_extended](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L365) |  |  |  |  |
| [double](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L381) |  |  |  |  |
| [add](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L414) |  |  |  |  |
| [sub](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L436) |  |  |  |  |
| [add](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L458) |  |  |  |  |
| [sub](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L479) |  |  |  |  |
| [neg](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L503) |  |  |  |  |
| [neg](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/curve_models/mod.rs#L516) |  |  |  |  |
| [optional_multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/scalar_mul/pippenger.rs#L67) |  |  |  |  |
| [multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/scalar_mul/straus.rs#L103) |  |  |  |  |
| [optional_multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/scalar_mul/straus.rs#L159) |  |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/scalar_mul/variable_base.rs#L11) |  |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/scalar_mul/vartime_double_base.rs#L23) |  |  |  |  |
| [fmt](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/field.rs#L46) | :x: |  |  |  |
| [add_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/field.rs#L59) |  |  |  |  |
| [add](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/field.rs#L68) |  |  |  |  |
| [sub](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/field.rs#L84) |  |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/field.rs#L115) |  |  |  |  |
| [m](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/field.rs#L119) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [neg](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/field.rs#L218) |  |  |  |  |
| [conditional_select](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/field.rs#L226) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [from_limbs](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/field.rs#L258) |  |  |  |  |
| [negate](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/field.rs#L276) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [reduce](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/field.rs#L290) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [from_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/field.rs#L338) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [load8_at](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/field.rs#L339) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [as_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/field.rs#L368) | :heavy_check_mark: |  |  |  |
| [pow2k](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/field.rs#L454) | :heavy_check_mark: |  |  |  |
| [m](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/field.rs#L460) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [square](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/field.rs#L562) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [square2](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/field.rs#L567) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [load8_at](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/field_verus.rs#L44) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [m](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/field_verus.rs#L67) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [from_limbs](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/field_verus.rs#L86) |  |  |  |  |
| [negate](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/field_verus.rs#L103) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [reduce](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/field_verus.rs#L155) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [from_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/field_verus.rs#L214) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [to_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/field_verus.rs#L243) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [pow2k](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/field_verus.rs#L421) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [square](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/field_verus.rs#L979) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [square2](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/field_verus.rs#L995) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [index](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/scalar.rs#L60) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [index_mut](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/scalar.rs#L73) |  |  |  |  |
| [m](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/scalar.rs#L81) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [from_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/scalar.rs#L99) | :heavy_check_mark: |  |  |  |
| [from_bytes_wide](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/scalar.rs#L144) | :heavy_check_mark: |  |  |  |
| [as_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/scalar.rs#L185) | :heavy_check_mark: |  |  |  |
| [add](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/scalar.rs#L229) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [sub](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/scalar.rs#L389) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [mul_internal](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/scalar.rs#L493) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [square_internal](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/scalar.rs#L548) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [montgomery_reduce](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/scalar.rs#L575) | :heavy_check_mark: |  |  |  |
| [part1](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/scalar.rs#L609) | :heavy_check_mark: |  |  |  |
| [part2](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/scalar.rs#L628) | :heavy_check_mark: |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/scalar.rs#L646) | :heavy_check_mark: |  |  |  |
| [montgomery_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/scalar.rs#L678) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [montgomery_square](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/scalar.rs#L691) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [as_montgomery](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/scalar.rs#L703) | :heavy_check_mark: |  |  |  |
| [from_montgomery](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/backend/serial/u64/scalar.rs#L721) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [as_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/edwards.rs#L181) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [decompress](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/edwards.rs#L194) |  |  |  |  |
| [step_1](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/edwards.rs#L209) |  |  |  |  |
| [step_2](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/edwards.rs#L223) |  |  |  |  |
| [identity](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/edwards.rs#L410) |  |  |  |  |
| [conditional_select](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/edwards.rs#L468) |  |  |  |  |
| [ct_eq](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/edwards.rs#L483) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [as_projective_niels](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/edwards.rs#L509) |  |  |  |  |
| [as_projective](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/edwards.rs#L522) |  |  |  |  |
| [as_affine_niels](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/edwards.rs#L532) |  |  |  |  |
| [to_montgomery](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/edwards.rs#L553) |  |  |  |  |
| [compress](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/edwards.rs#L566) |  |  |  |  |
| [double](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/edwards.rs#L616) |  |  |  |  |
| [add](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/edwards.rs#L627) |  |  |  |  |
| [add_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/edwards.rs#L639) |  |  |  |  |
| [sub](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/edwards.rs#L648) |  |  |  |  |
| [sub_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/edwards.rs#L660) |  |  |  |  |
| [neg](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/edwards.rs#L686) |  |  |  |  |
| [neg](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/edwards.rs#L699) |  |  |  |  |
| [mul_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/edwards.rs#L709) |  |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/edwards.rs#L726) |  |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/edwards.rs#L738) |  |  |  |  |
| [mul_base](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/edwards.rs#L748) |  |  |  |  |
| [mul_base_clamped](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/edwards.rs#L778) |  |  |  |  |
| [multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/edwards.rs#L800) |  |  |  |  |
| [optional_multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/edwards.rs#L832) |  |  |  |  |
| [vartime_double_scalar_mul_basepoint](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/edwards.rs#L902) |  |  |  |  |
| [create](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/edwards.rs#L953) |  |  |  |  |
| [basepoint](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/edwards.rs#L966) |  |  |  |  |
| [mul_base](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/edwards.rs#L1014) |  |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/edwards.rs#L1039) |  |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/edwards.rs#L1050) |  |  |  |  |
| [mul_by_pow_2](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/edwards.rs#L1192) |  |  |  |  |
| [is_torsion_free](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/edwards.rs#L1257) |  |  |  |  |
| [fmt](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/edwards.rs#L1267) | :x: |  |  |  |
| [eq](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/field.rs#L79) | :heavy_check_mark: |  |  |  |
| [ct_eq](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/field.rs#L88) | :heavy_check_mark: |  |  |  |
| [is_negative](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/field.rs#L101) | :heavy_check_mark: |  |  |  |
| [is_zero](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/field.rs#L111) | :heavy_check_mark: |  |  |  |
| [pow22501](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/field.rs#L121) | :heavy_check_mark: |  |  |  |
| [batch_invert](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/field.rs#L161) | :heavy_check_mark: |  |  |  |
| [invert](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/field.rs#L206) | :heavy_check_mark: |  |  |  |
| [pow_p58](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/field.rs#L220) | :heavy_check_mark: |  |  |  |
| [sqrt_ratio_i](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/field.rs#L243) | :heavy_check_mark: |  |  |  |
| [invsqrt](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/field.rs#L303) | :heavy_check_mark: |  |  |  |
| [elligator_inv](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/lizard/jacobi_quartic.rs#L30) |  |  |  |  |
| [dual](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/lizard/jacobi_quartic.rs#L66) |  |  |  |  |
| [from_uniform_bytes_single_elligator](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/lizard/lizard_ristretto.rs#L26) |  |  |  |  |
| [lizard_encode](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/lizard/lizard_ristretto.rs#L31) |  |  |  |  |
| [lizard_decode](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/lizard/lizard_ristretto.rs#L47) |  |  |  |  |
| [decode_253_bits](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/lizard/lizard_ristretto.rs#L87) |  |  |  |  |
| [elligator_ristretto_flavor_inverse](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/lizard/lizard_ristretto.rs#L112) |  |  |  |  |
| [to_jacobi_quartic_ristretto](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/lizard/lizard_ristretto.rs#L159) |  |  |  |  |
| [field_element](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/lizard/u64_constants.rs#L13) |  |  |  |  |
| [add](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/macros.rs#L19) |  |  |  |  |
| [add](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/macros.rs#L26) |  |  |  |  |
| [add](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/macros.rs#L33) |  |  |  |  |
| [add_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/macros.rs#L44) |  |  |  |  |
| [sub](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/macros.rs#L70) |  |  |  |  |
| [sub_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/macros.rs#L81) |  |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/macros.rs#L93) |  |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/macros.rs#L100) |  |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/macros.rs#L107) |  |  |  |  |
| [mul_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/macros.rs#L118) |  |  |  |  |
| [ct_eq](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/montgomery.rs#L79) |  |  |  |  |
| [eq](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/montgomery.rs#L88) |  |  |  |  |
| [hash](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/montgomery.rs#L98) |  |  |  |  |
| [zeroize](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/montgomery.rs#L115) |  |  |  |  |
| [mul_clamped](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/montgomery.rs#L128) |  |  |  |  |
| [mul_bits_be](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/montgomery.rs#L161) |  |  |  |  |
| [as_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/montgomery.rs#L192) |  |  |  |  |
| [to_edwards](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/montgomery.rs#L217) |  |  |  |  |
| [identity](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/montgomery.rs#L288) |  |  |  |  |
| [conditional_select](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/montgomery.rs#L303) |  |  |  |  |
| [as_affine](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/montgomery.rs#L322) |  |  |  |  |
| [differential_add_and_double](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/montgomery.rs#L343) |  |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/montgomery.rs#L401) |  |  |  |  |
| [mul_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/montgomery.rs#L409) |  |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/montgomery.rs#L417) |  |  |  |  |
| [to_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/ristretto.rs#L229) |  |  |  |  |
| [as_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/ristretto.rs#L234) |  |  |  |  |
| [from_slice](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/ristretto.rs#L244) |  |  |  |  |
| [decompress](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/ristretto.rs#L255) |  |  |  |  |
| [step_1](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/ristretto.rs#L275) |  |  |  |  |
| [step_2](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/ristretto.rs#L295) |  |  |  |  |
| [identity](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/ristretto.rs#L337) |  |  |  |  |
| [serialize](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/ristretto.rs#L371) |  |  |  |  |
| [serialize](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/ristretto.rs#L386) |  |  |  |  |
| [deserialize](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/ristretto.rs#L401) |  |  |  |  |
| [expecting](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/ristretto.rs#L410) |  |  |  |  |
| [deserialize](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/ristretto.rs#L437) |  |  |  |  |
| [expecting](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/ristretto.rs#L446) |  |  |  |  |
| [compress](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/ristretto.rs#L489) |  |  |  |  |
| [double_and_compress_batch](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/ristretto.rs#L553) |  |  |  |  |
| [efgh](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/ristretto.rs#L568) |  |  |  |  |
| [from](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/ristretto.rs#L575) |  |  |  |  |
| [coset4](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/ristretto.rs#L639) |  |  |  |  |
| [elligator_ristretto_flavor](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/ristretto.rs#L656) |  |  |  |  |
| [from_uniform_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/ristretto.rs#L787) |  |  |  |  |
| [identity](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/ristretto.rs#L807) |  |  |  |  |
| [default](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/ristretto.rs#L813) |  |  |  |  |
| [eq](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/ristretto.rs#L823) |  |  |  |  |
| [ct_eq](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/ristretto.rs#L835) |  |  |  |  |
| [add](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/ristretto.rs#L854) |  |  |  |  |
| [add_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/ristretto.rs#L866) |  |  |  |  |
| [sub](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/ristretto.rs#L876) |  |  |  |  |
| [sub_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/ristretto.rs#L888) |  |  |  |  |
| [sum](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/ristretto.rs#L899) |  |  |  |  |
| [neg](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/ristretto.rs#L910) |  |  |  |  |
| [neg](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/ristretto.rs#L918) |  |  |  |  |
| [mul_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/ristretto.rs#L924) |  |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/ristretto.rs#L933) |  |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/ristretto.rs#L942) |  |  |  |  |
| [mul_base](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/ristretto.rs#L952) |  |  |  |  |
| [multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/ristretto.rs#L981) |  |  |  |  |
| [optional_multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/ristretto.rs#L997) |  |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/ristretto.rs#L1088) |  |  |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/ristretto.rs#L1097) |  |  |  |  |
| [conditional_select](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/ristretto.rs#L1144) |  |  |  |  |
| [fmt](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/ristretto.rs#L1164) |  |  |  |  |
| [from_bytes_mod_order](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/scalar.rs#L232) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [from_bytes_mod_order_wide](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/scalar.rs#L256) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [from_canonical_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/scalar.rs#L277) | :heavy_check_mark: |  |  |  |
| [eq](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/scalar.rs#L338) | :heavy_check_mark: |  |  |  |
| [ct_eq](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/scalar.rs#L352) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [index](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/scalar.rs#L367) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [mul_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/scalar.rs#L386) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/scalar.rs#L425) | :heavy_check_mark: |  |  |  |
| [add_assign](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/scalar.rs#L448) | :heavy_check_mark: |  |  |  |
| [add](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/scalar.rs#L458) | :heavy_check_mark: |  |  |  |
| [sub](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/scalar.rs#L478) | :heavy_check_mark: |  |  |  |
| [neg](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/scalar.rs#L490) | :heavy_check_mark: |  |  |  |
| [neg](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/scalar.rs#L499) | :heavy_check_mark: |  |  |  |
| [serialize](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/scalar.rs#L527) | :x: |  |  |  |
| [deserialize](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/scalar.rs#L543) | :x: |  |  |  |
| [expecting](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/scalar.rs#L552) | :x: |  |  |  |
| [sum](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/scalar.rs#L595) | :x: |  |  |  |
| [default](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/scalar.rs#L604) | :heavy_check_mark: |  |  |  |
| [from](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/scalar.rs#L610) | :heavy_check_mark: |  |  |  |
| [from](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/scalar.rs#L657) | :heavy_check_mark: |  |  |  |
| [hash_from_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/scalar.rs#L763) | :x: |  |  |  |
| [from_hash](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/scalar.rs#L810) | :x: |  |  |  |
| [to_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/scalar.rs#L830) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [as_bytes](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/scalar.rs#L845) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [invert](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/scalar.rs#L887) | :heavy_check_mark: |  |  |  |
| [bits_le](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/scalar.rs#L1176) |  |  |  |  |
| [non_adjacent_form](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/scalar.rs#L1262) | :heavy_check_mark: |  |  |  |
| [bot_half](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/scalar.rs#L1352) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [top_half](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/scalar.rs#L1356) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [as_radix_16](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/scalar.rs#L1372) | :heavy_check_mark: |  |  |  |
| [to_radix_2w_size_hint](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/scalar.rs#L1425) | :x: |  |  |  |
| [as_radix_2w](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/scalar.rs#L1462) | :heavy_check_mark: |  |  |  |
| [unpack](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/scalar.rs#L1524) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [reduce](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/scalar.rs#L1535) | :heavy_check_mark: |  |  |  |
| [is_canonical](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/scalar.rs#L1558) | :heavy_check_mark: |  |  |  |
| [square_multiply](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/scalar.rs#L1568) | :heavy_check_mark: |  |  |  |
| [pack](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/scalar.rs#L1584) | :heavy_check_mark: |  |  |  |
| [montgomery_invert](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/scalar.rs#L1606) | :heavy_check_mark: |  |  |  |
| [invert](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/scalar.rs#L1677) | :heavy_check_mark: |  |  |  |
| [read_le_u64_into](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/scalar.rs#L1843) | :heavy_check_mark: |  |  |  |
| [clamp_integer](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/scalar.rs#L1879) | :heavy_check_mark: |  |  |  |
| [identity](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/traits.rs#L29) |  |  |  |  |
| [is_identity](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/traits.rs#L35) |  |  |  |  |
| [is_identity](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/traits.rs#L45) |  |  |  |  |
| [create](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/traits.rs#L56) |  |  |  |  |
| [basepoint](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/traits.rs#L59) |  |  |  |  |
| [mul_base](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/traits.rs#L62) |  |  |  |  |
| [multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/traits.rs#L128) |  |  |  |  |
| [optional_multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/traits.rs#L196) |  |  |  |  |
| [vartime_multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/traits.rs#L249) |  |  |  |  |
| [new](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/traits.rs#L297) |  |  |  |  |
| [optional_mixed_multiscalar_mul](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/traits.rs#L388) |  |  |  |  |
| [is_valid](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/traits.rs#L414) |  |  |  |  |
| [select](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/window.rs#L54) |  |  |  |  |
| [default](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/window.rs#L80) |  |  |  |  |
| [from](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/window.rs#L98) |  |  |  |  |
| [from](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/window.rs#L108) |  |  |  |  |
| [select](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/window.rs#L187) |  |  |  |  |
| [from](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/window.rs#L202) |  |  |  |  |
| [select](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/5a57bad082ab43848deef98bbded087d54fbd560/curve25519-dalek/src/window.rs#L233) |  |  |  |  |
