Below are some notes on Ristretto, which are not an authoritative
writeup and which may have errors.  See also the [Decaf
paper][decaf_paper], the [libdecaf
implementation of Ristretto][ristretto_libdecaf], and its [Sage
script][ristretto_sage].

Decaf constructs a prime-order group from a cofactor-\\(4\\) Edwards
curve by defining an encoding of a related Jacobi quartic, then
transporting the encoding from the Jacobi quartic to the Edwards curve
by means of an isogeny.  Ristretto uses a different Jacobi quartic and
a different isogeny, but is otherwise similar.

These notes only describe Ristretto, and focus on the cofactor-\\(8\\)
case.

## The Jacobi Quartic

The Jacobi quartic curve is parameterized by \\(e, A\\), and is of the
form $$ \mathcal J\_{e,A} : t\^2 = es\^4 + 2As\^2 + 1, $$ with
identity point \\((0,1)\\).  For more details on the Jacobi quartic,
see the [Decaf paper][decaf_paper] or
[_Jacobi Quartic Curves Revisited_][hwcd_jacobi] by Hisil, Wong,
Carter, and Dawson).

When \\(e = a\^2\\) is a square, \\(\mathcal J\_{e,A}\\) has full
\\(2\\)-torsion (i.e., \\(\mathcal J[2] \cong \mathbb Z /2 \times
\mathbb Z/2\\)), and
we can write the \\(\mathcal J[2]\\)-coset of a point \\(P =
(s,t)\\) as
$$
P + \mathcal J[2] = \left\\{
(s,t),
(-s,-t),
(1/as, -t/as\^2),
(-1/as, t/as\^2)
\right\\}.
$$
Notice that replacing \\(a\\) by \\(-a\\) just swaps the last two
points, so this set does not depend on the choice of \\(a\\).  In
what follows we require \\(a = \pm 1\\).

## Encoding \\(\mathcal J / \mathcal J[2]\\)

To encode points on \\(\mathcal J\\) modulo \\(\mathcal J[2]\\),
we need to choose a canonical representative of the above coset.
To do this, it's sufficient to make two independent sign choices:
the Decaf paper suggests choosing \\((s,t)\\) with \\(s\\)
non-negative and finite, and \\(t/s\\) non-negative or infinite.

The encoding is then the (canonical byte encoding of the)
\\(s\\)-value of the canonical representative.

## The Edwards Curve

The primary internal model in `curve25519-dalek` for Curve25519 points
is the [_Extended Twisted Edwards Coordinates_][hwcd_edwards] of
Hisil, Wong, Carter, and Dawson.  These correspond to the affine model
$$
\mathcal E\_{a,d} : ax\^2 + y\^2 = 1 + dx\^2y\^2.
$$
In projective coordinates, we represent a point as \\((X:Y:Z:T)\\)
with
$$
XY = ZT, \quad aX\^2 + Y\^2 = Z\^2 + dT\^2.
$$
(For more details on this model, see the
[`curve_models`][curve_models] documentation). The case \\(a = 1\\) is
the _untwisted_ case; we only consider \\(a = \pm 1\\), and in
particular we focus on the twisted Edwards form of Curve25519, which
has \\(a = -1, d = -121665/121666\\).  When not otherwise specified,
we write \\(\mathcal E\\) for \\(\mathcal E\_{-1, -121665/121666}\\).

When both \\(d\\) and \\(ad\\) are nonsquare (which forces \\(a\\)
to be square), the curve is *complete*.  In this case the
four-torsion subgroup is cyclic, and we
can write it explicitly as
$$
\mathcal E\_{a,d}[4] = \\{ (0,1),\\; (1/\sqrt a, 0),\\; (0, -1),\\; (-1/\sqrt{a}, 0)\\}.
$$
These are the only points with \\(xy = 0\\); the points with \\( y
\neq 0 \\) are \\(2\\)-torsion.  The \\(\mathcal
E\_{a,d}[4]\\)-coset of \\(P = (x,y)\\) is then
$$
P + \mathcal E\_{a,d}[4] = \\{ (x,y),\\; (y/\sqrt a, -x\sqrt a),\\; (-x, -y),\\; (-y/\sqrt a, x\sqrt a)\\}.
$$
Notice that if \\(xy \neq 0 \\), then exactly two of
these points have \\( xy \\) non-negative, and they differ by the
\\(2\\)-torsion point \\( (0,-1) \\).  This means that we can select
a representative modulo \\(\mathcal E\_{a,d}[2] \\)
by requiring \\(xy\\) nonnegative and \\(y \neq
0\\), and we can ensure this condition by conditionally adding a
\\(4\\)-torsion point if \\(xy\\) is negative or \\(y = 0\\).

This procedure gives a canonical lift from \\(\mathcal E / \mathcal
E[4]\\) to \\(\mathcal E / \mathcal E[2]\\).  Since it involves a
conditional rotation, we refer to it as *torquing* the point.

The structure of the Curve25519 group is \\( \mathcal E(\mathbb
F\_p) \cong \mathbb Z / 8 \times \mathbb Z / \ell\\), where \\( \ell
= 2\^{252} + \cdots \\) is a large prime.  Because \\(\mathcal E[8]
\cong \mathbb Z / 8\\), we have \\(\[2\](\mathcal E[8]) = \mathcal
E[4]\\), \\(\mathcal E[4] \cong \mathbb Z / 4
\\) and \\( \mathcal E[2] \cong \mathbb Z / 2\\).  In particular
this tells us that the group
$$
\frac{\[2\](\mathcal E)}{\mathcal E[4]}
$$
is well-defined and has prime order \\( (8\ell / 2) / 4 = \ell \\).
This is the group we will construct using Ristretto.

## The Isogeny

For \\(a = \pm 1\\), we have a \\(2\\)-isogeny
$$
\theta\_{a,d} : \mathcal J\_{a\^2, -a(a+d)/(a-d)} \longrightarrow \mathcal E\_{a,d}
$$
(or simply \\(\theta\\)) defined by
$$
\theta\_{a,d} : (s,t) \mapsto \left( \frac{1}{\sqrt{ad-1}} \cdot \frac{2s}{t},\quad \frac{1+as\^2}{1-as\^2} \right).
$$
Its dual is 
$$
\hat{\theta}\_{a,d} : \mathcal E\_{a,d} \longrightarrow \mathcal J\_{a\^2, -a(a+d)/(a-d)},
$$
defined by
$$
\hat{\theta}\_{a,d} : (x,y) \mapsto \left( \sqrt{ad-1} \cdot \frac{xy}{1-ax\^2}, \frac{y^2 + ax^2}{1-ax^2} \right)
$$

The kernel of the isogeny is \\( \{(0, \pm 1)\} \\).
The image of the isogeny is \\(\[2\](\mathcal E)\\).  To see this,
first note that because \\( \theta \circ \hat{\theta} = [2] \\), we
know that \\( \[2\](\mathcal E) \subseteq \theta(\mathcal J)\\); then, to see that
\\(\theta(\mathcal J)\\) is exactly \\(\[2\](\mathcal E)\\),
recall that isogenous elliptic curves over a finite field have the
same number of points (exercise 5.4 of Silverman), so that
$$
\\# \theta(\mathcal J) = \frac {\\# \mathcal J} {\\# \ker \theta}
= \frac {\\# \mathcal E}{2} = \\# \[2\](\mathcal E).
$$

To determine the image \\(\theta(\mathcal J[2])\\) of the
\\(2\\)-torsion, we consider the image of the coset
\\(\theta((s,t) + \mathcal J[2])\\).
Let \\((x,y) = \theta(s,t)\\); then
\\(\theta(-s,-t) = (x,y)\\) and
\\(\theta(1/as, -t/as\^2) = (-x, -y)\\),
so that \\(\theta(\mathcal J[2]) = \mathcal E[2]\\).

The Decaf paper recalls that, for a group \\( G \\) with normal
subgroup \\(G' \leq G\\), a group homomorphism \\( \phi : G
\rightarrow H \\) induces a homomorphism
$$
\bar{\phi} : \frac G {G'} \longrightarrow \frac {\phi(G)}{\phi(G')} \leq \frac {H} {\phi(G')},
$$
and that the induced homomorphism \\(\bar{\phi}\\) is injective if
\\( \ker \phi \leq G' \\).  In our context, the kernel of
\\(\theta\\) is \\( \\{(0, \pm 1)\\} \leq \mathcal J[2] \\),
so \\(\theta\\) gives an isomorphism
$$
\frac {\mathcal J} {\mathcal J[2]}
\cong
\frac {\theta(\mathcal J)} {\theta(\mathcal J[2])}
\cong
\frac {\[2\](\mathcal E)} {\mathcal E[2]}.
$$

We can use the isomorphism to transfer the encoding of \\(\mathcal
J / \mathcal J[2] \\) defined above to \\(\[2\](\mathcal E)/\mathcal
E[2]\\), by encoding the Edwards point \\((x,y)\\) using the Jacobi
quartic encoding of \\(\theta\^{-1}(x,y)\\).

Since \\(\\# (\[2\](\mathcal E) / \mathcal E[2]) = (\\#\mathcal
E)/4\\), if \\(\mathcal E\\) has cofactor \\(4\\), we're done.
Otherwise, if \\(\mathcal E\\) has cofactor \\(8\\), as in the
Curve25519 case, we use the torquing procedure to lift \\(\mathcal E
/ \mathcal E[4]\\) to \\(\mathcal E / \mathcal E[2]\\), and then
apply the encoding for \\( \[2\](\mathcal E) / \mathcal E[2] \\).

## The Ristretto Encoding

We can write the above encoding/decoding procedure concretely (in affine
coordinates) as follows:

### Encoding

On input \\( (x,y) \in \[2\](\mathcal E)\\), a representative for a
coset in \\( \[2\](\mathcal E) / \mathcal E[4] \\):

1. Check if \\( xy \\) is negative or \\( x = 0 \\); if so, torque
   the point by setting \\( (x,y) \gets (x,y) + P_4 \\), where
   \\(P_4\\) is a \\(4\\)-torsion point.

2. Check if \\(x\\) is negative or \\( y = -1 \\); if so, set
   \\( (x,y) \gets (x,y) + (0,-1) = (-x, -y) \\).

3. Compute $$ s = +\sqrt {(-a) \frac {1 - y} {1 + y} }, $$ choosing
   the positive square root.

The output is then the (canonical) byte-encoding of \\(s\\).

If \\(\mathcal E\\) has cofactor \\(4\\), we skip the first step,
since our input already represents a coset in
\\( \[2\](\mathcal E) / \mathcal E[2] \\).

To see that this corresponds to the encoding procedure above, notice
that the first step lifts from \\( \mathcal E / \mathcal E[4] \\) to
\\(\mathcal E / \mathcal E[2]\\).  To understand steps 2 and 3,
notice that the \\(y\\)-coordinate of \\(\theta(s,t)\\) is
$$
y = \frac {1 + as\^2}{1 - as\^2},
$$
so that the \\(s\\)-coordinate of \\(\theta\^{-1}(x,y)\\) has
$$
s\^2 = (-a)\frac {1-y}{1+y}.
$$
Since
$$
x = \frac 1 {\sqrt {ad - 1}} \frac {2s} {t},
$$
we also have
$$
\frac s t = x \frac {\sqrt {ad-1}} 2,
$$
so that the sign of \\(s/t\\) is determined by the sign of \\(x\\).

Recall that to choose a canonical representative of \\( (s,t) +
\mathcal J[2] \\), it's sufficient to make two sign choices: the
sign of \\(s\\) and the sign of \\(s/t\\).  Step 2 determines the
sign of \\(s/t\\), while step 3 computes \\(s\\) and determines its
sign (by choosing the positive square root).  Finally, the check
that \\(y \neq -1\\) prevents division-by-zero when encoding the
identity; it falls out of the optimized formulas below.

### Decoding

On input `s_bytes`, decoding proceeds as follows:

1. Decode `s_bytes` to \\(s\\); reject if `s_bytes` is not the
   canonical encoding of \\(s\\).

2. Check whether \\(s\\) is negative; if so, reject.

3. Compute
$$
y \gets \frac {1 + as\^2}{1 - as\^2}.
$$

4. Compute
$$
x \gets +\sqrt{ \frac{4s\^2} {ad(1+as\^2)\^2 - (1-as\^2)\^2}},
$$
choosing the positive square root, or reject if the square root does
not exist.

5. Check whether \\(xy\\) is negative or \\(y = 0\\); if so, reject.

## Encoding in Extended Coordinates

The formulas above are given in affine coordinates, but the usual
internal representation is extended twisted Edwards coordinates \\(
(X:Y:Z:T) \\) with \\( x = X/Z \\), \\(y = Y/Z\\), \\(xy = T/Z \\).
Selecting the distinguished representative of the coset
requires the affine coordinates \\( (x,y) \\), and computing \\( s
\\) requires an inverse square root.
As inversions are expensive, we'd like to be able to do this
whole computation with only one inverse square root, by batching
together the inversion and the inverse square root.

However, it is not obvious how to do this, since the inverse square
root computation depends on the affine coordinates (which select the
distinguished representative).

In what follows we consider only the case
\\(a = -1\\); a similar argument applies to the case \\( a = 1\\).

Since \\(y = Y/Z\\), in extended coordinates the formula for \\(s\\) becomes
$$
s = \sqrt{ \frac{ 1 - Y/Z}{1+Y/Z}} = \sqrt{\frac{Z - Y}{Z+Y}}
= \frac {Z - Y} {\sqrt{Z\^2 - Y\^2}}.
$$

Here \\( (X:Y:Z:T) \\) are the coordinates of the distinguished
representative of the coset.
Write \\( (X\_0 : Y\_0 : Z\_0 : T\_0) \\)
for the coordinates of the initial representative.  Then the
torquing procedure in step 1 replaces \\( (X\_0 : Y\_0 : Z\_0 :
T\_0) \\) by \\( (iY\_0 : iX\_0 : Z\_0 : -T\_0) \\).  This means we
want to obtain either
$$
\frac {1} { \sqrt{Z\_0\^2 - Y\_0\^2}}
\quad \text{or} \quad
\frac {1} { \sqrt{Z\_0\^2 + X\_0\^2}}.
$$

We can relate these using the identity
$$
(a-d)X\^2Y\^2 = (Z\^2 - aX\^2)(Z\^2 - Y\^2),
$$
which is valid for all curve points.  To see this, recall from the curve equation that
$$
-dX\^2Y\^2 = Z\^4 - aZ\^2X\^2 - Z\^2Y\^2,
$$
so that
$$
(a-d)X\^2Y\^2 = Z\^4 - aZ\^2X\^2 - Z\^2Y\^2 + aX\^2Y\^2 = (Z\^2 - Y\^2)(Z\^2 + X\^2).
$$

The encoding procedure is as follows:

1. \\(u\_1 \gets (Z\_0 + Y\_0)(Z\_0 - Y\_0) = Z\_0\^2 - Y\_0\^2 \\)
2. \\(u\_2 \gets X\_0 Y\_0 \\)
3. \\(I \gets \mathrm{invsqrt}(u\_1 u\_2\^2) = 1/\sqrt{X\_0\^2 Y\_0\^2 (Z\_0\^2 - Y\_0\^2)} \\)
4. \\(D\_1 \gets u\_1 I = \sqrt{(Z\_0\^2 - Y\_0\^2)/(X\_0\^2 Y\_0\^2)} \\)
5. \\(D\_2 \gets u\_2 I = \pm \sqrt{1/(Z\_0\^2 - Y\_0\^2)} \\)
6. \\(Z\_{inv} \gets D\_1 D\_2 T\_0 = (u\_1 u\_2)/(u\_1 u\_2\^2) T\_0 = T\_0 / X\_0 Y\_0 = 1/Z\_0 \\)
7. If \\( T\_0 Z\_{inv} = x\_0 y\_0 \\) is negative:
    1. \\( X \gets iY\_0 \\)
    2. \\( Y \gets iX\_0 \\)
    3. \\( D \gets D\_1 / \sqrt{a-d} = 1/\sqrt{Z\_0\^2 + X\_0\^2} \\)
8. Otherwise:
    1. \\( X \gets X\_0 \\)
    2. \\( Y \gets Y\_0 \\)
    3. \\( D \gets D\_2 = \pm \sqrt{1/(Z\_0\^2 - Y\_0\^2)} \\)
9. If \\( X Z\_{inv} = x \\) is negative, set \\( Y \gets - Y\\)
10. Compute \\( s \gets (Z - Y) D = (Z - Y) / \sqrt{Z\^2 - Y\^2} \\) and return.

## Decoding to Extended Coordinates

## Equality Testing

## Elligator

## The Double-Ristretto Encoding

It's possible to do batch encoding of \\( [2]P \\) using the dual
isogeny \\(\hat{\theta}\\).  Defer this for now.

## ???

[ristretto_sage]: https://sourceforge.net/p/ed448goldilocks/code/ci/master/tree/aux/ristretto/ristretto.sage
[ristretto_libdecaf]: https://sourceforge.net/p/ed448goldilocks/code/ci/master/tree/
[decaf_paper]: https://eprint.iacr.org/2015/673.pdf
[hwcd_jacobi]: https://eprint.iacr.org/2009/312.pdf
[hwcd_edwards]: https://eprint.iacr.org/2008/522.pdf
[edwards_edwards]: https://www.ams.org/journals/bull/2007-44-03/S0273-0979-07-01153-6/S0273-0979-07-01153-6.pdf
[twisted_edwards]: https://eprint.iacr.org/2008/013.pdf
[curve_models]: ../../curve_models/index.html