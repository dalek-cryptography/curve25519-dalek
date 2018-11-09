A vectorized implementation of group operations on the twisted Edwards
form of Curve25519, using a modification of the 4-way parallel
formulas of Hisil, Wong, Carter, and Dawson.

# Overview

The 2008 paper [_Twisted Edwards Curves Revisited_][hwcd08] by Hisil,
Wong, Carter, and Dawson (HWCD) introduced the “extended coordinates”
and mixed-model representations which are used by most Edwards curve
implementations.

However, they also describe 4-way parallel formulas for point addition
and doubling: a unified addition algorithm taking an effective
\\(2\mathbf M + 1\mathbf D\\), a doubling algorithm taking an
effective \\(1\mathbf M + 1\mathbf S\\), and a dedicated (i.e., for
distinct points) addition algorithm taking an effective \\(2 \mathbf M
\\).  They compare these formulas with a 2-way parallel variant of the
Montgomery ladder.

Unlike their serial formulas, which are used widely, their parallel
formulas do not seem to have been implemented in software before.  The
2-way parallel Montgomery ladder was used in 2015 by Tung Chou's
`sandy2x` implementation.  Curiously, however, although the [`sandy2x`
paper][sandy2x] also implements Edwards arithmetic, and cites HWCD08,
it doesn't mention their parallel Edwards formulas.
A 2015 paper by Hernández and López describes an AVX2 implementation
of X25519. Neither the paper nor the code are publicly available, but
it apparently gives only a [slight speedup][avx2trac], suggesting that
it uses a 4-way parallel Montgomery ladder rather than parallel
Edwards formulas.

The reason may be that HWCD08 describe their formulas as operating on
four independent processors, which would make a software
implementation impractical: all of the operations are too low-latency
to effectively synchronize.  But a closer inspection reveals that the
(more expensive) multiplication and squaring steps are uniform, while
the instruction divergence occurs in the (much cheaper) addition and
subtraction steps.  This means that a SIMD implementation can perform
the expensive steps uniformly, and handle divergence in the
inexpensive steps using masking.

These notes describe modifications to the original parallel formulas
to allow a SIMD implementation, and this module contains an
implementation of the modified formulas using 256-bit AVX2 vector
operations.

# Parallel formulas in HWCD'08

The doubling formula is presented in the HWCD paper as follows:

| Cost             | Processor 1                    | Processor 2                    | Processor 3                    | Processor 4                    |
|------------------|--------------------------------|--------------------------------|--------------------------------|--------------------------------|
|                  | idle                           | idle                           | idle                           | \\( R\_1 \gets X\_1 + Y\_1 \\) |
| \\(1\mathbf S\\) | \\( R\_2 \gets X\_1\^2 \\)     | \\( R\_3 \gets Y\_1\^2   \\)   | \\( R\_4 \gets Z\_1\^2   \\)   | \\( R\_5 \gets R\_1\^2   \\)   |
|                  | \\( R\_6 \gets R\_2 + R\_3 \\) | \\( R\_7 \gets R\_2 - R\_3 \\) | \\( R\_4 \gets 2 R\_4 \\)      | idle                           |
|                  | idle                           | \\( R\_1 \gets R\_4 + R\_7 \\) | idle                           | \\( R\_2 \gets R\_6 - R\_5 \\) |
| \\(1\mathbf M\\) | \\( X\_3 \gets R\_1 R\_2 \\)   | \\( Y\_3 \gets R\_6 R\_7 \\)   | \\( T\_3 \gets R\_2 R\_6 \\)   | \\( Z\_3 \gets R\_1 R\_7 \\)   |

and the unified addition algorithm is presented as follows:

| Cost             | Processor 1                    | Processor 2                    | Processor 3                    | Processor 4                    |
|------------------|--------------------------------|--------------------------------|--------------------------------|--------------------------------|
|                  | \\( R\_1 \gets Y\_1 - X\_1 \\) | \\( R\_2 \gets Y\_2 - X\_2 \\) | \\( R\_3 \gets Y\_1 + X\_1 \\) | \\( R\_4 \gets Y\_2 + X\_2 \\) |
| \\(1\mathbf M\\) | \\( R\_5 \gets R\_1 R\_2 \\)   | \\( R\_6 \gets R\_3 R\_4 \\)   | \\( R\_7 \gets T\_1 T\_2 \\)   | \\( R\_8 \gets Z\_1 Z\_2 \\)   |
| \\(1\mathbf D\\) | idle                           | idle                           | \\( R\_7 \gets k R\_7 \\)      | \\( R\_8 \gets 2 R\_8 \\)      |
|                  | \\( R\_1 \gets R\_6 - R\_5 \\) | \\( R\_2 \gets R\_8 - R\_7 \\) | \\( R\_3 \gets R\_8 + R\_7 \\) | \\( R\_4 \gets R\_6 + R\_5 \\) |
| \\(1\mathbf M\\) | \\( X\_3 \gets R\_1 R\_2 \\)   | \\( Y\_3 \gets R\_3 R\_4 \\)   | \\( T\_3 \gets R\_1 R\_4 \\)   | \\( Z\_3 \gets R\_2 R\_3 \\)   |

Here \\(\mathbf M\\) and \\(\mathbf S\\) represent the cost of
multiplication and squaring of generic field elements, \\(\mathbf D\\)
represents the cost of multiplication by a curve constant (in this
case \\( k = 2d \\)).

Notice that the \\(1\mathbf M\\) and \\(1\mathbf S\\) steps are
uniform.  The non-uniform steps are all inexpensive additions or
subtractions, with the exception of the multiplication by the curve
constant \\(k = 2d\\):
$$
R\_7 \gets 2 d R\_7.
$$

HWCD suggest parallelising this step by breaking \\(k = 2d\\) into four
parts as \\(k = k_0 + 2\^n k_1 + 2\^{2n} k_2 + 2\^{3n} k_3 \\) and
computing \\(k_i R_7 \\) in parallel.  This is quite awkward, but if
the curve constant is a ratio \\( d = d\_1/d\_2 \\), then projective
coordinates allow us to instead compute 
$$
(R\_5, R\_6, R\_7, R\_8) \gets (d\_2 R\_5, d\_2 R\_6, 2d\_1 R\_7, d\_2 R\_8).
$$
This can be performed as a uniform multiplication by a vector of
constants, and if \\(d\_1, d\_2\\) are small, it is relatively
inexpensive.  (This trick was suggested by Mike Hamburg).
In the Curve25519 case, we have 
$$
d = \frac{d\_1}{d\_2} = \frac{-121665}{121666};
$$
Since \\(2 \cdot 121666 < 2\^{18}\\), all the constants above fit (up
to sign) in 32 bits, so this can be done in parallel as four
multiplications by small constants \\( (121666, 121666, 2\cdot 121665,
2\cdot 121666) \\), followed by a negation to compute \\( - 2\cdot 121665\\).

# Modified parallel formulas

Using the modifications sketched above, we can write SIMD-friendly
versions of the parallel formulas as follows.  To avoid confusion with
the original formulas, temporary variables are named \\(S\\) instead
of \\(R\\) and are in static single-assignment form.

## Addition

To add points
\\(P_1 = (X_1 : Y_1 : Z_1 : T_1) \\)
and
\\(P_2 = (X_2 : Y_2 : Z_2 : T_2 ) \\),
we compute
$$
\begin{aligned}
(S\_0 &&,&& S\_1 &&,&& S\_2 &&,&& S\_3 )
&\gets
(Y\_1 - X\_1&&,&& Y\_1 + X\_1&&,&& Y\_2 - X\_2&&,&& Y\_2 + X\_2)
\\\\
(S\_4 &&,&& S\_5 &&,&& S\_6 &&,&& S\_7 )
&\gets
(S\_0 \cdot S\_2&&,&& S\_1 \cdot S\_3&&,&& Z\_1 \cdot Z\_2&&,&& T\_1 \cdot T\_2)
\\\\
(S\_8    &&,&& S\_9    &&,&& S\_{10} &&,&& S\_{11} )
&\gets
(d\_2 \cdot S\_4 &&,&& d\_2 \cdot S\_5 &&,&& 2 d\_2 \cdot S\_6 &&,&& 2 d\_1 \cdot S\_7 )
\\\\
(S\_{12} &&,&& S\_{13} &&,&& S\_{14} &&,&& S\_{15})
&\gets
(S\_9 - S\_8&&,&& S\_9 + S\_8&&,&& S\_{10} - S\_{11}&&,&& S\_{10} + S\_{11})
\\\\
(X\_3&&,&& Y\_3&&,&& Z\_3&&,&& T\_3)
&\gets
(S\_{12} \cdot S\_{14}&&,&& S\_{15} \cdot S\_{13}&&,&& S\_{15} \cdot S\_{14}&&,&& S\_{12} \cdot S\_{13})
\end{aligned}
$$
to obtain \\( P\_3 = (X\_3 : Y\_3 : Z\_3 : T\_3) = P\_1 + P\_2 \\).
This costs \\( 2\mathbf M + 1 \mathbf D\\).

## Readdition

If the point \\( P_2 = (X\_2 : Y\_2 : Z\_2 : T\_2) \\) is fixed, we
can cache the multiplication of the curve constants by computing
$$
\begin{aligned}
(S\_2' &&,&& S\_3' &&,&& Z\_2' &&,&& T\_2' )
&\gets
(d\_2 \cdot (Y\_2 - X\_2)&&,&& d\_2 \cdot (Y\_1 + X\_1)&&,&& 2d\_2 \cdot Z\_2 &&,&& 2d\_1 \cdot T\_2).
\end{aligned}
$$
This costs \\( 1\mathbf D\\); with \\( (S\_2', S\_3', Z\_2', T\_2')\\)
in hand, the addition formulas above become
$$
\begin{aligned}
(S\_0 &&,&& S\_1 &&,&& Z\_1 &&,&& T\_1 )
&\gets
(Y\_1 - X\_1&&,&& Y\_1 + X\_1&&,&& Z\_1 &&,&& T\_1)
\\\\
(S\_8    &&,&& S\_9    &&,&& S\_{10} &&,&& S\_{11} )
&\gets
(S\_0 \cdot S\_2' &&,&& S\_1 \cdot S\_3'&&,&& Z\_1 \cdot Z\_2' &&,&& T\_1 \cdot T\_2')
\\\\
(S\_{12} &&,&& S\_{13} &&,&& S\_{14} &&,&& S\_{15})
&\gets
(S\_9 - S\_8&&,&& S\_9 + S\_8&&,&& S\_{10} - S\_{11}&&,&& S\_{10} + S\_{11})
\\\\
(X\_3&&,&& Y\_3&&,&& Z\_3&&,&& T\_3)
&\gets
(S\_{12} \cdot S\_{14}&&,&& S\_{15} \cdot S\_{13}&&,&& S\_{15} \cdot S\_{14}&&,&& S\_{12} \cdot S\_{13})
\end{aligned}
$$
which costs only \\( 2\mathbf M \\).  This precomputation is
essentially similar to the precomputation that HWCD suggest for their
serial formulas.  Because the cost of precomputation and then
readdition is the same as addition, it's sufficient to only
implement caching and readdition.

## Doubling

The non-uniform portions of the (re)addition formulas have a fairly
regular structure.  Unfortunately, this is not the case for the
doubling formulas, which are much less nice.

To double a point \\( P = (X\_1 : Y\_1 : Z\_1 : T\_1) \\), we compute
$$
\begin{aligned}
(X\_1 &&,&& Y\_1 &&,&& Z\_1 &&,&& S\_0)
&\gets
(X\_1 &&,&& Y\_1 &&,&& Z\_1 &&,&& X\_1 + Y\_1)
\\\\
(S\_1 &&,&& S\_2 &&,&& S\_3 &&,&& S\_4 )
&\gets
(X\_1\^2 &&,&& Y\_1\^2&&,&& Z\_1\^2 &&,&& S\_0\^2)
\\\\
(S\_5 &&,&& S\_6 &&,&& S\_8 &&,&& S\_9 )
&\gets
(S\_1 + S\_2 &&,&& S\_1 - S\_2 &&,&& S\_1 + 2S\_3 - S\_2 &&,&& S\_1 + S\_2 - S\_4)
\\\\
(X\_3 &&,&& Y\_3 &&,&& Z\_3 &&,&& T\_3 )
&\gets
(S\_8 \cdot S\_9 &&,&& S\_5 \cdot S\_6 &&,&& S\_8 \cdot S\_6 &&,&& S\_5 \cdot S\_9)
\end{aligned}
$$
to obtain \\( P\_3 = (X\_3 : Y\_3 : Z\_3 : T\_3) = [2]P\_1 \\).

The intermediate step between the squaring and multiplication requires
a long chain of additions, but with some care and finesse,
described below, it is possible (in our case) to arrange this
computation without requiring an intermediate reduction.

However, it does mean that the doubling formulas have proportionately
more vectorization overhead than the (re)addition formulas.  The
effects of this are discussed in the comparison section below.

# Field element representation

Our strategy is to implement 4-wide multiplication and squaring by
wordslicing, using one 64-bit AVX2 lane for each field element.  Field
elements are represented in the usual way as 10 `u32` limbs in radix
\\(25.5\\) (i.e., alternating between \\(2\^{26}\\) for even limbs and
\\(2\^{25}\\) for odd limbs).  This has the effect that passing between
the parallel 32-bit AVX2 representation and the serial 64-bit
representation (which uses radix \\(2^{51}\\)) amounts to regrouping
digits.

The field element representation is oriented around the AVX2
`vpmuluqdq` instruction, which multiplies the low 32 bits of each
64-bit lane of each operand to produce a 64-bit result.

```text,no_run
(a1 ?? b1 ?? c1 ?? d1 ??)
(a2 ?? b2 ?? c2 ?? d2 ??)

(a1*a2 b1*b2 c1*c2 d1*d2)
```

To unpack 32-bit values into 64-bit lanes for use in multiplication
it would be convenient to use the `vpunpck[lh]dq` instructions,
which unpack and interleave the low and high 32-bit lanes of two
source vectors.
However, the AVX2 versions of these instructions are designed to
operate only within 128-bit lanes of the 256-bit vectors, so that
interleaving the low lanes of `(a0 b0 c0 d0 a1 b1 c1 d1)` with zero
gives `(a0 00 b0 00 a1 00 b1 00)`.  Instead, we pre-shuffle the data
layout as `(a0 b0 a1 b1 c0 d0 c1 d1)` so that we can unpack the
"low" and "high" parts as

```text,no_run
(a0 00 b0 00 c0 00 d0 00)
(a1 00 b1 00 c1 00 d1 00)
```

The data layout for a vector of four field elements \\( (a,b,c,d)
\\) with limbs \\( a_0, a_1, \ldots, a_9 \\) is as `[u32x8; 5]` in
the form

```text,no_run
(a0 b0 a1 b1 c0 d0 c1 d1)
(a2 b2 a3 b3 c2 d2 c3 d3)
(a4 b4 a5 b5 c4 d4 c5 d5)
(a6 b6 a7 b7 c6 d6 c7 d7)
(a8 b8 a9 b9 c8 d8 c9 d9)
```

Since this breaks cleanly into two 128-bit lanes, it may be possible
to adapt it to 128-bit vector instructions such as NEON without too
much difficulty.  Going the other direction, to extend this to AVX512,
we could either run two point operations in parallel in lower and upper
halves of the registers, or use 2-way parallelism within a field operation.

# Avoiding Overflow in Doubling

To analyze the size of the field element coefficients during the
computations, we can parameterize the bounds on the limbs of each
field element by \\( b \in \mathbb R \\) representing the excess bits
above that limb's radix, so that each limb is bounded by either
\\(2\^{25+b} \\) or \\( 2\^{26+b} \\), as appropriate.

The multiplication routine requires that its inputs are bounded with
\\( b < 1.75 \\), in order to fit a multiplication by \\( 19 \\)
into 32 bits.  Since \\( \lg 19 < 4.25 \\), \\( 19x < 2\^{32} \\)
when \\( x < 2\^{27.75} = 2\^{26 + 1.75} \\).  However, this is only
required for one of the inputs; the other can grow up to \\( b < 2.5
\\).

In addition, the multiplication and squaring routines do not
canonically reduce their outputs, but can leave some small uncarried
excesses, so that their reduced outputs are bounded with
\\( b < 0.007 \\).

The non-parallel portion of the doubling formulas is
$$
\begin{aligned}
(S\_5 &&,&& S\_6 &&,&& S\_8 &&,&& S\_9 )
&\gets
(S\_1 + S\_2 &&,&& S\_1 - S\_2 &&,&& S\_1 + 2S\_3 - S\_2 &&,&& S\_1 + S\_2 - S\_4)
\end{aligned}
$$

Computing \\( (S\_5, S\_6, S\_8, S\_9 ) \\) as
$$
\begin{matrix}
 & S\_1 & S\_1 & S\_1 & S\_1 \\\\
+& S\_2 &      &      & S\_2 \\\\
+&      &      & S\_3 &      \\\\
+&      &      & S\_3 &      \\\\
+&      & 2p   & 2p   & 2p   \\\\
-&      & S\_2 & S\_2 &      \\\\
-&      &      &      & S\_4 \\\\
=& S\_5 & S\_6 & S\_8 & S\_9
\end{matrix}
$$
results in bit-excesses \\( < (1.01, 1.60, 2.33, 2.01)\\) for
\\( (S\_5, S\_6, S\_8, S\_9 ) \\).  The products we want to compute
are then
$$
\begin{aligned}
X\_3 &\gets S\_8 S\_9 \leftrightarrow (2.33, 2.01) \\\\
Y\_3 &\gets S\_5 S\_6 \leftrightarrow (1.01, 1.60) \\\\
Z\_3 &\gets S\_8 S\_6 \leftrightarrow (2.33, 1.60) \\\\
T\_3 &\gets S\_5 S\_9 \leftrightarrow (1.01, 2.01)
\end{aligned}
$$
which are too large: it's not possible to arrange the multiplicands so
that one vector has \\(b < 2.5\\) and the other has \\( b < 1.75 \\).
However, if we flip the sign of \\( S\_4 = S\_0\^2 \\) during
squaring, so that we output \\(S\_4' = -S\_4 \pmod p\\), then we can
compute
$$
\begin{matrix}
 & S\_1 & S\_1 & S\_1 & S\_1 \\\\
+& S\_2 &      &      & S\_2 \\\\
+&      &      & S\_3 &      \\\\
+&      &      & S\_3 &      \\\\
+&      &      &      & S\_4' \\\\
+&      & 2p   & 2p   &      \\\\
-&      & S\_2 & S\_2 &      \\\\
=& S\_5 & S\_6 & S\_8 & S\_9
\end{matrix}
$$
resulting in bit-excesses \\( < (1.01, 1.60, 2.33, 1.60)\\) for
\\( (S\_5, S\_6, S\_8, S\_9 ) \\).  The products we want to compute
are then
$$
\begin{aligned}
X\_3 &\gets S\_8 S\_9 \leftrightarrow (2.33, 1.60) \\\\
Y\_3 &\gets S\_5 S\_6 \leftrightarrow (1.01, 1.60) \\\\
Z\_3 &\gets S\_8 S\_6 \leftrightarrow (2.33, 1.60) \\\\
T\_3 &\gets S\_5 S\_9 \leftrightarrow (1.01, 1.60)
\end{aligned}
$$
whose right-hand sides are all bounded with \\( b < 1.75 \\) and
whose left-hand sides are all bounded with \\( b < 2.5 \\),
so that we can avoid any intermediate reductions.

# Comparison to non-vectorized formulas

In theory, the parallel Edwards formulas seem to allow a \\(4\\)-way
speedup from parallelism.  However, an actual vectorized
implementation has several slowdowns that cut into this speedup.

First, the parallel formulas can only use a \\( 32 \times 32
\rightarrow 64 \\)-bit integer multiplier, so the speedup from
vectorization must overcome the disadvantage of losing the \\( 64
\times 64 \rightarrow 128\\)-bit (serial) integer multiplier.  The
effect of this slowdown is microarchitecture-dependent, since it
requires accounting for the total number of multiplications and
additions and their relative costs.  In the future, it will probably
be possible to avoid this slowdown by using the `IFMA52` instructions,
whose parallelism is perfectly suited to these formulas.

Second, the parallel doubling formulas incur both a theoretical and
practical slowdown.  The parallel formulas described above work on the
\\( \mathbb P\^3 \\) “extended” coordinates.  The \\( \mathbb P\^2 \\)
model introduced earlier by [Bernstein, Birkner, Joye, Lange, and
Peters][bbjlp08] allows slightly faster doublings, so HWCD suggest
mixing coordinate systems while performing scalar multiplication
(attributing the idea to [a 1998 paper][cmo98] by Cohen, Miyagi, and
Ono).  The \\( T \\) coordinate is not required for doublings, so when
doublings are followed by doublings, its computation can be skipped.
More details on this approach and the different coordinate systems can
be found in the [`curve_models` module documentation][curve_models].

Unfortunately, this optimization is not compatible with the parallel
formulas, which cannot save time by skipping a single variable, so the
parallel doubling formulas do slightly more work when counting the
total number of field multiplications and squarings.

In addition, the parallel doubling formulas have a less regular
pattern of additions and subtractions than the parallel addition
formulas, so the vectorization overhead is proportionately greater.
Both the parallel addition and parallel doubling formulas also require
some shuffling to rearrange data within the vectors, which places more
pressure on the shuffle unit than is desirable.

This means that the speedup from using a vectorized implementation of
parallel Edwards formulas is likely to be greatest in applications
that do fewer doublings and more additions (like a large multiscalar
multiplication) rather than applications that do fewer additions and
more doublings (like a double-base scalar multiplication).

Third, current Intel CPUs perform thermal throttling when using wide
vector instructions.  A detailed description can be found in §15.26 of
[the Intel Optimization Manual][intel], but using wide vector
instructions prevents the core from operating at higher frequencies.
The core can return to the higher-frequency state after 2
milliseconds, but this timer is reset every time high-power
instructions are used.

Any speedup from vectorization therefore has to be weighed against a
slowdown for the next few million instructions.  For a mixed workload,
where point operations are interspersed with other tasks, this can
reduce overall performance.  This implementation is therefore probably
not suitable for basic applications, like signatures, but is
worthwhile for complex applications, like zero-knowledge proofs, which
do sustained work.

For this reason, the AVX2 backend is not enabled by default, but can
be selected using the `avx2_backend` feature.

# Future work

There are several directions for future improvement:

* Using the vectorized field arithmetic code to parallelize across
  point operations rather than within a single point operation.  This
  is less flexible, but would give a speedup both from allowing use of
  the faster mixed-model arithmetic and from reducing shuffle
  pressure.  One approach in this direction would be to implement
  batched scalar-point operations using vectors of points (AoSoA
  layout).  This less generally useful but would give a speedup for
  Bulletproofs.

* Extending the implementation to use the full width of AVX512, either
  handling the extra parallelism internally to a single point
  operation (by using a 2-way parallel implementation of field
  arithmetic instead of a wordsliced one), or externally,
  parallelizing across point operations.  Internal parallelism would
  be preferable but might require too much shuffle pressure.

* Generalizing the implementation to non-AVX2 instructions,
  particularly NEON.  The current point arithmetic code is written in
  terms of field element vectors, which are in turn implemented using
  platform SIMD vectors.  It should be possible to write an alternate
  implementation of the `FieldElement2625x4` using NEON without changing
  the point arithmetic.  NEON has 128-bit vectors rather than 256-bit
  vectors, but this may still be worthwhile compared to a serial
  implementation.


[sandy2x]: https://eprint.iacr.org/2015/943.pdf
[avx2trac]: https://trac.torproject.org/projects/tor/ticket/8897#comment:28
[hwcd08]: https://www.iacr.org/archive/asiacrypt2008/53500329/53500329.pdf
[curve_models]: https://doc-internal.dalek.rs/curve25519_dalek/curve_models/index.html
[bbjlp08]: https://eprint.iacr.org/2008/013
[cmo98]: https://link.springer.com/content/pdf/10.1007%2F3-540-49649-1_6.pdf
[intel]: https://software.intel.com/sites/default/files/managed/9e/bc/64-ia-32-architectures-optimization-manual.pdf