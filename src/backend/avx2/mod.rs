// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2016-2017 Isis Lovecruft, Henry de Valence
// See LICENSE for licensing information.
//
// Authors:
// - Isis Agora Lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>

//! An implementation of group operations on the twisted Edwards form of
//! Curve25519, using AVX2 to implement the 4-way parallel formulas of
//! Hisil, Wong, Carter, and Dawson (HWCD).
//!
//! Their 2008 paper [_Twisted Edwards Curves Revisited_][hwcd08], which
//! introduced the extended coordinates used in other parts of `-dalek`,
//! also describes 4-way parallel formulas for point addition and
//! doubling:
//!
//! * a unified addition algorithm taking an effective \\(2\mathbf M +
//! 1\mathbf D\\);
//!
//! * a doubling algorithm taking an effective \\(1\mathbf M + 1\mathbf
//! S\\);
//!
//! * a dedicated (i.e., for distinct points) addition algorithm taking
//! an effective \\(2 \mathbf M \\).
//!
//! Here \\(\mathbf M\\) and \\(\mathbf S\\) represent the cost of
//! multiplication and squaring of generic field elements and \\(\mathbf
//! D\\) represents the cost of multiplication by a curve constant.
//!
//! Currently, this implementation uses only the first two algorithms.
//!
//! # Parallel formulas
//!
//! The doubling formula is presented in the HWCD paper as follows:
//!
//! | Cost             | Processor 1                    | Processor 2                    | Processor 3                    | Processor 4                    |
//! |------------------|--------------------------------|--------------------------------|--------------------------------|--------------------------------|
//! |                  | idle                           | idle                           | idle                           | \\( R\_1 \gets X\_1 + Y\_1 \\) |
//! | \\(1\mathbf S\\) | \\( R\_2 \gets X\_1\^2 \\)     | \\( R\_3 \gets Y\_1\^2   \\)   | \\( R\_4 \gets Z\_1\^2   \\)   | \\( R\_5 \gets R\_1\^2   \\)   |
//! |                  | \\( R\_6 \gets R\_2 + R\_3 \\) | \\( R\_7 \gets R\_2 - R\_3 \\) | \\( R\_4 \gets 2 R\_4 \\)      | idle                           |
//! |                  | idle                           | \\( R\_1 \gets R\_4 + R\_7 \\) | idle                           | \\( R\_2 \gets R\_6 - R\_5 \\) |
//! | \\(1\mathbf M\\) | \\( X\_3 \gets R\_1 R\_2 \\)   | \\( Y\_3 \gets R\_6 R\_7 \\)   | \\( T\_3 \gets R\_2 R\_6 \\)   | \\( Z\_3 \gets R\_1 R\_7 \\)   |
//!
//! and the unified addition algorithm is presented as follows:
//!
//! | Cost             | Processor 1                    | Processor 2                    | Processor 3                    | Processor 4                    |
//! |------------------|--------------------------------|--------------------------------|--------------------------------|--------------------------------|
//! |                  | \\( R\_1 \gets Y\_1 - X\_1 \\) | \\( R\_2 \gets Y\_2 - X\_2 \\) | \\( R\_3 \gets Y\_1 + X\_1 \\) | \\( R\_4 \gets Y\_2 + X\_2 \\) |
//! | \\(1\mathbf M\\) | \\( R\_5 \gets R\_1 R\_2 \\)   | \\( R\_6 \gets R\_3 R\_4 \\)   | \\( R\_7 \gets T\_1 T\_2 \\)   | \\( R\_8 \gets Z\_1 Z\_2 \\)   |
//! | \\(1\mathbf D\\) | idle                           | idle                           | \\( R\_7 \gets k R\_7 \\)      | \\( R\_8 \gets 2 R\_8 \\)      |
//! |                  | \\( R\_1 \gets R\_6 - R\_5 \\) | \\( R\_2 \gets R\_8 - R\_7 \\) | \\( R\_3 \gets R\_8 + R\_7 \\) | \\( R\_4 \gets R\_6 + R\_5 \\) |
//! | \\(1\mathbf M\\) | \\( X\_3 \gets R\_1 R\_2 \\)   | \\( Y\_3 \gets R\_3 R\_4 \\)   | \\( T\_3 \gets R\_1 R\_4 \\)   | \\( Z\_3 \gets R\_2 R\_3 \\)   |
//!
//! Here \\( k = 2d \\) is a curve constant.
//!
//! # Implementation strategy
//! 
//! For a software implementation, each "processor"'s operations are too
//! low-latency to parallelize across threads.  However, the main cost
//! is in the multiplication and squaring steps, which share a single
//! instruction.
//!
//! Our strategy is to implement 4-wide multiplication and squaring using one
//! 64-bit AVX2 lane for each field element.  Field elements are
//! represented in the usual way as 10 `u32` limbs. The addition and
//! subtraction steps are done largely serially, using masking to handle
//! the instruction divergence. 
//!
//! The remaining obstacle to parallelism is the multiplication by the curve constant \\(k = 2d\\).  In the Curve25519 case, this is 
//!
//! $$ k \equiv 2 \frac{-121665}{121666} \\ \equiv 16295367250680780974490674513165176452449235426866156013048779062215315747161 \pmod p. $$
//!
//! HWCD suggest parallelising this step by breaking \\(k\\) into four
//! parts as \\(k = k_0 + 2\^n k_1 + 2\^{2n} k_2 + 2\^{3n} k_3 \\) and
//! computing \\(k_i R_7 \\) in parallel.  However, this would be
//! somewhat awkward in our case, since we would normally represent
//! \\(k\\) as \\( 10 \\) 32-bit limbs, and \\(10 \\) is not divisible
//! by \\(4\\), so we would need a specialized routine to perform a
//! vectorized multiplication by 64-bit constants.
//!
//! Instead, since we are working projectively, we can multiply
//! \\(R_7\\) by \\( -2\cdot 121665 \\) and multiply the other three
//! variables by \\(121666\\).  This trick was suggested by Mike
//! Hamburg.  Ignoring the sign for the moment, since
//! \\(2 \cdot 121666 < 2\^{18}\\), all these constants fit in 32 bits,
//! so this can be done in parallel as a scaling by \\( (121666, 121666,
//! 2\cdot 121665, 2\cdot 121666) \\).  To handle the sign, we use
//! masking to negate one of the field elements.
//!
//! Since we're primarily interested in Ristretto performance, not
//! Curve25519 performance, we could alternately work on the
//! \\(4\\)-isogenous "IsoEd25519" curve, which has \\(d = 121665\\).
//! However, this would only save the negation step, since multiplying
//! one field element by a 32-bit constant is not much easier than
//! multiplying four field elements by 32-bit constants, and it would
//! prevent accelerating Curve25519, so we don't make this choice.
//!
//! The 4-wide formulas of the HWCD paper do not seem to have been
//! implemented using SIMD before.  The HWCD paper also describes and
//! analyzes a 2-wide variant of the Montgomery ladder (for comparison
//! with parallel Edwards formulas); this strategy was used in 2015 by
//! Tung Chou's `sandy2x` implementation, which used a 2-wide field
//! implementation in 128-bit vector registers.  
//!
//! Curiously, however, although the [`sandy2x` paper][sandy2x] also
//! implements Edwards arithmetic, and cites the HWCD paper, it doesn't
//! mention or discuss the parallel formulas from HWCD, or that the
//! 2-wide Montgomery formulas it uses were previously published there.
//! There is also a 2015 paper by Hernández and López on using AVX2 for
//! the X25519 Montgomery ladder, but neither the paper nor the code are
//! publicly available, and it apparently gives only a [slight
//! speedup][avx2trac], suggesting that it also overlooked the
//! HWCD formulas.
//!
//! HWCD also suggest using a mixed representation, passing between \\(
//! \mathbb P\^3 \\) "extended" coordinates and \\( \mathbb P\^2 \\)
//! "projective" coordinates, where doubling is slightly cheaper (saving
//! about \\(\mathbf 1M\\).  This approach is used for the
//! non-vectorized `u32` and `u64` backends, and more
//! details on the different coordinate systems can be found in the
//! `curve_models` module documentation.
//!
//! This optimization is not compatible with the parallel formulas, which are
//! therefore slightly less efficient when counting the total number of
//! field multiplications and squarings.  In particular, vectorized doublings
//! are less efficient than serial doublings.  
//! In addition, the parallel formulas can only use a \\( 32 \times 32
//! \rightarrow 64 \\)-bit integer multiplier, so the speedup from
//! vectorization must overcome the disadvantage of losing the \\( 64
//! \times 64 \rightarrow 128\\)-bit (serial) integer multiplier. 
//!
//! When used for constant-time variable-base scalar multiplication,
//! this strategy (using AVX2) gives a significant speedup over the
//! serial implementation (using the \\(64 \times 64\\) multiplier) of
//! approximately 1.6x for Skylake-X with `target_cpu=skylake` (using AVX2), of
//! approximately 1.8x for Skylake-X with `target_cpu=skylake-avx512` (using the extra
//! `ymm16..ymm31` registers from AVX512VL), and of approximately 1.0x
//! for Ryzen (which implements AVX2 at half rate).
//!
//! (Note: since testing this, the experimental `llvm50` Rust branch
//! used to compile the experimental `stdsimd` intrinsics have fallen
//! out of sync and it is no longer possible to compile for
//! `skylake-avx512`.  This is why all of this branch is part of the
//! `yolocrypto` feature, pending upstream work.)
//!
//! However, since the relative cost of doubling and addition has
//! changed, the optimal tradeoffs for window size etc. in scalar
//! multiplication have probably also changed and should be
//! re-evaluated.
//!
//! # Tweaked formulas
//!
//! After tweaking the formulas as described above, we obtain the
//! following.  To avoid confusion with the original HWCD formulas,
//! temporary variables are named \\(S\\) instead of \\(R\\) and are in
//! static single-assignment (SSA) form.
//!
//! ## Addition
//!
//! To add points \\(P_1 = (X_1 : Y_1 : Z_1 : T_1) \\) and \\(P_2 = (X_2
//! : Y_2 : Z_2 : T_2 ) \\), we compute
//!
//! $$
//! \begin{aligned}
//! S\_0 &\gets Y\_1 - X\_1 \\\\
//! S\_1 &\gets Y\_1 + X\_1 \\\\
//! S\_2 &\gets Y\_2 - X\_2 \\\\
//! S\_3 &\gets Y\_2 + X\_2 
//! \end{aligned}
//! $$
//!
//! $$
//! \begin{aligned}
//! S\_4 &\gets S\_0 S\_2 \\\\
//! S\_5 &\gets S\_1 S\_3 \\\\
//! S\_6 &\gets Z\_1 Z\_2 \\\\
//! S\_7 &\gets T\_1 T\_2 
//! \end{aligned}
//! $$
//!
//! $$
//! \begin{aligned}
//! S\_8    &\gets S\_4 \cdot 121666 \\\\
//! S\_9    &\gets S\_5 \cdot 121666 \\\\
//! S\_{10} &\gets S\_6 \cdot 2 \cdot 121666 \\\\
//! S\_{11} &\gets S\_7 \cdot 2 \cdot (-121665)
//! \end{aligned}
//! $$
//! 
//! $$
//! \begin{aligned}
//! S\_{12} &\gets S\_9 - S\_8 \\\\
//! S\_{13} &\gets S\_9 + S\_8 \\\\
//! S\_{14} &\gets S\_{10} - S\_{11} \\\\
//! S\_{15} &\gets S\_{10} + S\_{11}
//! \end{aligned}
//! $$
//!
//! $$
//! \begin{aligned}
//! X\_3 &\gets S\_{12} S\_{14} \\\\
//! Y\_3 &\gets S\_{15} S\_{13} \\\\
//! Z\_3 &\gets S\_{15} S\_{14} \\\\
//! T\_3 &\gets S\_{12} S\_{13}
//! \end{aligned}
//! $$
//!
//! to obtain \\( P\_3 = (X\_3 : Y\_3 : Z\_3 : T\_3) = P\_1 + P\_2 \\).
//!
//! ## Doubling
//!
//! To double a point \\( P = (X\_1 : Y\_1 : Z\_1 : T\_1) \\), we compute
//!
//! $$ S\_0 \gets X\_1 + Y\_1 $$
//!
//! $$
//! \begin{aligned}
//! S\_1 &\gets X\_1\^2 \\\\
//! S\_2 &\gets Y\_1\^2 \\\\
//! S\_3 &\gets Z\_1\^2 \\\\
//! S\_4 &\gets S\_0\^2 
//! \end{aligned}
//! $$
//!
//! $$
//! \begin{aligned}
//! S\_5 &\gets S\_1 + S\_2 \\\\
//! S\_6 &\gets S\_1 - S\_2 \\\\
//! S\_7 &\gets 2S\_3 \\\\
//! S\_8 &\gets S\_7 + S\_6 = S\_1 + 2S\_3 - S\_2 \\\\
//! S\_9 &\gets S\_5 - S\_4 = S\_1 + S\_2 - S\_4
//! \end{aligned}
//! $$
//!
//! $$
//! \begin{aligned}
//! X\_3 &\gets S\_8 S\_9 \\\\
//! Y\_3 &\gets S\_5 S\_6 \\\\
//! Z\_3 &\gets S\_8 S\_6 \\\\
//! T\_3 &\gets S\_5 S\_9 
//! \end{aligned}
//! $$
//!
//! to obtain \\( P\_3 = (X\_3 : Y\_3 : Z\_3 : T\_3) = [2]P\_1 \\).
//!
//! In practice, we compute \\( (S\_5, S\_6, S\_7, S\_9 ) \\) as
//!
//! $$
//! \begin{matrix}
//!  & S\_1 & S\_1 & S\_1 & S\_1 \\\\
//! +& S\_2 &      &      & S\_2 \\\\
//! +&      &      & S\_3 &      \\\\
//! +&      &      & S\_3 &      \\\\
//! +&      & 2p   & 2p   & 2p   \\\\
//! -&      & S\_2 & S\_2 &      \\\\
//! -&      &      &      & S\_4 \\\\
//! =& S\_5 & S\_6 & S\_8 & S\_9 
//! \end{matrix}
//! $$
//!
//! adding multiples of \\(p\\) to prevent underflow.  This results in
//! 32-bit limbs which are just too large for multiplication, so we
//! perform a reduction.  However, since we just need to reduce the
//! excess in each limb, not a full reduction, it's enough to perform
//! each carry in parallel.
//!
//! With some finesse, it may be possible to rearrange this
//! computation to avoid the extra carry pass, but this is not yet
//! implemented.
//!
//! # Field element representation
//!
//! The field element representation is oriented around the AVX2
//! `vpmuluqdq` instruction, which multiplies the low 32 bits of each
//! 64-bit lane of each operand to produce a 64-bit result.
//!
//! ```text,no_run
//! (a1 ?? b1 ?? c1 ?? d1 ??)
//! (a2 ?? b2 ?? c2 ?? d2 ??)
//!
//! (a1*a2 b1*b2 c1*c2 d1*d2)
//! ```
//!
//! To unpack 32-bit values into 64-bit lanes for use in multiplication
//! it would be convenient to use the `vpunpck[lh]dq` instructions,
//! which unpack and interleave the low and high 32-bit lanes of two
//! source vectors.
//! However, the AVX2 versions of these instructions are designed to
//! operate only within 128-bit lanes of the 256-bit vectors, so that
//! interleaving the low lanes of `(a0 b0 c0 d0 a1 b1 c1 d1)` with zero
//! gives `(a0 00 b0 00 a1 00 b1 00)`.  Instead, we pre-shuffle the data
//! layout as `(a0 b0 a1 b1 c0 d0 c1 d1)` so that we can unpack the
//! "low" and "high" parts as
//!
//! ```text,no_run
//! (a0 00 b0 00 c0 00 d0 00)
//! (a1 00 b1 00 c1 00 d1 00)
//! ```
//!
//! The data layout for a vector of four field elements \\( (a,b,c,d)
//! \\) with limbs \\( a_0, a_1, \ldots, a_9 \\) is as `[u32x8; 5]` in
//! the form
//!
//! ```text,no_run
//! (a0 b0 a1 b1 c0 d0 c1 d1)
//! (a2 b2 a3 b3 c2 d2 c3 d3)
//! (a4 b4 a5 b5 c4 d4 c5 d5)
//! (a6 b6 a7 b7 c6 d6 c7 d7)
//! (a8 b8 a9 b9 c8 d8 c9 d9)
//! ```
//!
//! Since this breaks cleanly into two 128-bit lanes, it may be possible
//! to adapt it to 128-bit vector instructions such as NEON without too
//! much difficulty.
//!
//! Going the other direction, to extend this to AVX512, we could either
//! run two point operations in parallel in lower and upper halves of
//! the registers, or use 2-way parallelism within a field operation.
//!
//! We don't attempt to use AVX2 for serial field element computations
//! such as inversion, since wherever we have AVX2 we also have `mulx`.
//! However, it might be useful for batched inverse square-root
//! computations, which can't be batched in the same way inversions can.
//!
//! # Implementation details
//!
//! The implementation uses the unstable `stdsimd` crate to provide AVX2
//! intrinsics, and the code is not yet cleanly factored between the
//! field element parts and the point parts.
//!
//! When compiling with AVX512VL, LLVM is able to use the extra
//! `ymm16..ymm31` registers to reduce register pressure, and avoid
//! spills during field multiplication.  This gives a small but
//! noticeable speedup.
//!
//! The addition and subtraction steps involve masking, to apply
//! operations to a single lane of the vector.  AVX512VL extends the
//! predication features of AVX512 to AVX2 code and would probably be
//! beneficial.  Unfortunately, LLVM is currently unable to lower `op +
//! blend` into an AVX512VL masked operation.  However, the explicitly
//! masked versions of the intrinsics seem to produce the same LLVM IR
//! as an `op + blend`, so hopefully this will improve as the AVX512
//! support in LLVM improves.
//!
//! [sandy2x]: https://eprint.iacr.org/2015/943.pdf
//! [avx2trac]: https://trac.torproject.org/projects/tor/ticket/8897#comment:28
//! [hwcd08]: https://www.iacr.org/archive/asiacrypt2008/53500329/53500329.pdf


pub(crate) mod field;

pub(crate) mod edwards;

pub(crate) mod constants;
