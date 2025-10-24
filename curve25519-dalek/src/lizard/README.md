# Computing Preimages of Ristretto255 Points Under the Elligator2 Map

# Introduction

The [Elligator2][elligator] map provides a way to map field elements to elliptic curve points with a nearly uniform distribution. When adapted for [Ristretto255][ristretto], it maps elements of the field $\mathbb{F}_p$ (where $p = 2^{255} - 19$) to points in the Ristretto255 group. This mapping is not injective; each Ristretto255 point can be the image of up to eight distinct field elements.

Some use cases, however, require an injective map into the Ristretto group with an easy-to-compute inverse. This is handy if, e.g., we want to encrypt data with the [ElGamal](https://en.wikipedia.org/wiki/ElGamal_encryption) encryption scheme, where plaintexts are curve points. This injection is precisely what the ["Lizard"][lizard] encoding provides.

In this document, we describe the Lizard encoding/decoding algorithms. Along the way we will describe an efficient method for computing preimages of the Elligator2 map. These algorithms are implemented in `src/lizard/` in this repo.

# Lizard
The Lizard encoding is an injective map into the Ristretto255 group $\mathcal{R}$ built on the Elligator2 map, $E_2$.

## Encoding: Make Elligator2 an injection

As mentioned above, $E_2$ is not injective and thus cannot work directly as an encoding function.

Instead we create an injective function from $E_2$ by "tagging" each input $x$ so it is distinguished among the other inverses of $E_2(x)$. This requires restricting the map's domain: rather than mapping $\mathbb{F} \to \mathcal{R}$, we define a map $\lbrace 0,1 \rbrace^{128} \to \mathcal{R}$ (i.e., half the input length), as follows:
1. Given bitstring $b \in \lbrace 0,1 \rbrace^{128}$, compute its hash $h = \mathsf{H}(b)$ where $\mathsf{H}$ is a hash function with a 32-byte digest.
2. Let `s` be the 32-byte value `h[0:8] || b || h[24:32]`.
3. Clear the least significant bit: `s[0] &= 254`. This is done so that the field element represented by `s` is "positive" (defined in next section).
4. Clear the most significant two bits: `s[31] &= 63`. This is done so that the field element represented by `s` does not exceed $p$.
5. Interpret `s` as a field element (little endian), and output $E_2(s)$

## Decoding: Invert the injection

The tag allows us to decode points $P \in \mathcal{R}$ as follows:
1. Compute the set of preimages $E_2^{-1}(P)$ using the procedure described in the rest of this document. This gives us a set of up to 8 scalars that are candidates to be the correct inverse.
2. For each candidate scalar, check whether it adheres to the above form. Namely check that it is positive and has byte representation `h[0:8] || b || h[24:32]`, where $h = \mathsf{H}(b)$, and the appropriate bits are cleared.
3. If such a candidate is found, this is the decoded value.

The above procedures are exactly what the `lizard_encode` and `lizard_decode` functions do in `src/lizard/lizard_ristretto.rs`.

## Security argument

It is not a-priori clear that the function described is an injection. 
We repeat [Bas Westerbaan's argument](https://github.com/bwesterb/go-ristretto/blob/7c80df9e61a54045aedb2ccad99d1e636a4b4c90/ristretto.go#L224) for why this method produces an injection with overwhelming probability:

> There are some (and with high probability at most 80) inputs to SetLizard() which cannot be decoded. The chance that you hit such an input is around 1 in 2^122.

> In Lizard there are $256 - 128 - 3 = 125$ check bits to pick out the right preimage among at most eight.  Conservatively assuming there are seven other preimages, the chance that one of them passes the check as well is given by:

> $$
\begin{align}
1 - (1 - 2^{-125})^7
&= 7\cdot 2^{-125} + 21\cdot 2^{-250} - ...
\\\\&\approx 2^{-125 - 2\log(7)}
\\\\&= 2^{-122.192\ldots}
\end{align}
$$

> Presuming a random hash function, the number of "bad" inputs is binomially distributed with $n=2^{128}$ and $p=2^{-122.192}\ldots$ For such large $n$, the Poisson distribution with $\lambda=np=56$ is a  very good approximation. In fact: the cumulative distribution function (CDF) of the Poission distribution is larger than that of the binomial distribution for $k > \lambda$.[^1]  The value of the former on $k=80$ is larger than 0.999 and so with a probability of 99.9%, there are fewer than 80 bad inputs.

# Inverting $E_2$
 
 Methods for efficiently implementing the Elligator2 map $E_2$ have been carefully documented on the [Ristretto255][ristretto] website, and using this the implementation of Lizard *encoding* is straightforward. Lizard *decoding*, on the other hand requires efficiently inverting $E_2$ and we describe that process here.

## Background and Notation

The computations will involve a family of related curves all defined over the prime field of order $p = 2^{255} - 19$ which we denote by $\mathbb{F}$. We will adopt the definition of [Decaf][decaf] and define an element of $\mathbb{F}$ to be *positive* if the low bit of its least positive representative is set.

### Fundamental Curves

**The Twisted Edwards Curve $\mathcal{E}$.**
Much of our work will take place in the Twisted Edwards Curve $\mathcal{E}_{a,d}$ given by

$$
ax^2+y^2=1+dx^2y^2.
$$

where $a = -1$ and $d =-121665/121666$. In what follows we will simply denote this curve by $\mathcal{E}$, but we will refer to $a$ and $d$ explicitly when it helps clarify the relationships between curves and dispel any magic behind the apparently magic numbers.

The addition law on $\mathcal{E}$ is given by $(x_1, y_1) + (x_2,y_2) = (x_3,y_3)$ where:

$$
x_3 = \frac{x_1y_2 + x_2y_1}{1 + d x_1 y_1 x_2 y_2}, \quad y_3 = \frac{ y_1 y_2 - a x_1 x_2}{1 - d x_1 y_1 x_2 y_2}.
$$

The 4-torsion subgroup will be of particular interest. It is cyclic and consists of the points:

$$
\mathcal{E}[4] = \lbrace (0,1), (1,0), (0,-1), (-1, 0) \rbrace.
$$

The size of $\mathcal{E}$ is $|\mathcal{E}| = 8\ell$ where $\ell = 2^{252}+27742317777372353535851937790883648493$ is prime.

**The Jacobi Quartic $\mathcal{J}$.**
We also consider the Jacobi quartic $\mathcal{J}_{e,A}$ given by

$$
t^2=es^4+2As^2+1,
$$

where $e = (-a)^2 = 1$ and $A = -a - 2ad/(a-d) = 243329$.
We denote this curve by $\mathcal{J}$.

$\mathcal{J}$ is 2-isogenous to $\mathcal{E}$ through the mapping  $\theta:\mathcal{J} \rightarrow \mathcal{E}$:

$$
\theta(s,t) = \left(\frac{1}{\sqrt{-d-1}}\cdot\frac{2s}{t}, \frac{1-s^2}{1+s^2} \right).
$$

The addition law on $\mathcal{J}$ is given by $(s_1, t_1)+(s_2, t_2) = (s_3, t_3)$ where

$$
s_3 = \frac{s_1 t_2 + s_2 t_1}{1 - e s_{1}^2 s_{2}^2},\quad t_3 = \frac{(t_1 t_2 + 2A s_1 s_2)(1 + e s_1^2s_2^2) + 2e s_1  s_2 (s_1^2 + s_2^2)}{(1 - e s_1^2 s_2^2)^2}
$$

$\mathcal{J}$ has full 2-torsion, that is, $|\mathcal{J}[2]| = 4$ and given a point $(s,t)\in\mathcal{J}$, its coset for the 2-torsion subgroup of $\mathcal{J}$ is given by

$$
(s,t) + \mathcal{J}[2] = \lbrace (s,t), (-s,-t), (1/as, -t/as^2), (-1/as, t/as^2) \rbrace
$$

The size of $\mathcal{J}$ is $|\mathcal{J}| = 8\ell$.

**The Montgomery Curve $\mathcal{M}$.**
Although we will not use it in this document, it is convenient to know that $\mathcal{E}$ and $\mathcal{J}$ are closely related to Curve25519, the Montgomery curve given by the equation

$$
  y^{2}=x^{3}+486662x^{2}+x = x^3 + 2\frac{a+d}{a - d}x^2 + x
$$

In particular $\mathcal{M}$ is birationally equivalent to $\mathcal{E}$ and is 2-isogenous to $\mathcal{J}$.
The size of $\mathcal{M}$ is $|\mathcal{M}| = 8\ell$ 

### Ristretto

The Ristretto255 group is the group $\mathcal{R} = [2]\mathcal{E}/\mathcal{E}[4]$ of prime order $\ell$. Each element of $\mathcal{R}$ can be represented by an even point $(x,y)\in\mathcal{E}_{a,d}$. Writing the four-element coset out in full:

$$
(x,y) + \mathcal{E}_{a,d}[4] = \left\lbrace (x,y), (\frac{y}{\sqrt{a}}, -x\sqrt{a}), (-x,-y), (\frac{-y}{\sqrt{a}}, x\sqrt{a}) \right\rbrace.
$$

With our parameter choice of $a = -1$ this simplifies to

$$
\lbrace (x,y), (-x,-y), (\mathrm{i} y, \mathrm{i} x), (-\mathrm{i} y, -\mathrm{i} x) \rbrace,
$$

where $\mathrm{i} = \sqrt{-1}$ is the imaginary unit in $\mathbb{F}$.

## The Components of Elligator2

$E_2$ is built from four functions:

1. A map from field elements to a Jacobi quartic: $e: \mathbb{F} \rightarrow \mathcal{J}$.
1. The quotient map: $q_\mathcal{J}: \mathcal{J} \rightarrow \mathcal{J}/\mathcal{J}[2]$
1. A 2-isogeny from the Jacobi quartic to the even points on the Edwards curve: $\theta: \mathcal{J} \rightarrow [2]\mathcal{E}$. Note that we only know that the image of $\theta$ consists of even points because the torsion group $\mathcal{E}[8]$ is cyclic. See discussion below.
1. The quotient map into the Ristretto group: $q_\mathcal{E}: [2]\mathcal{E}/\mathcal{E}[2] \rightarrow \mathcal{R}$, where $P \mapsto P + \mathcal{E}[4]/\mathcal{E}[2]$.

Now since $\mathsf{ker}(\theta) \leqslant \mathcal{J}[2]$, [the Decaf paper][decaf] shows that the map

$$
\hat{\theta}: \frac{\mathcal{J}}{\mathcal{J}[2]} \rightarrow \frac{\theta(\mathcal{J})}{\theta(\mathcal{J}[2])} = \frac{[2]\mathcal{E}}{\mathcal{E}[2]}, \qquad P + \mathcal{J}[2] \mapsto \theta(P) + \mathcal{E}[2]
$$ 

<div id="eq-reduced-theta" align="right">(1)</div>


is an isomorphism.

The full map is $E_2 = q_\mathcal{E} \circ \hat{\theta} \circ q_\mathcal{J} \circ e$. Our goal is to compute the preimage set $E_2^{-1}(P)$ for a given Ristretto point $P \in \mathcal{R}$.

Since $q_\mathcal{E}$ is 2-to-1, $\hat{\theta}$ is 1-to-1, and $q_\mathcal{J}$ is 4-to-1, we expect to find $4 \times 2 = 8$ preimages on the Jacobi quartic $\mathcal{J}$. Each of these 8 points on $\mathcal{J}$ will then correspond to two field elements, one positive and one negative, via the inverse of $e$ (thus there is a unique corresponding positive field element via $e^{-1}$). This section explains how to find these 16 field elements.

We now describe how to invert each of these components before presenting an efficient algorithm to compute the full inverse of $E_2$.

### The Quotient Maps and their Inverses

Given a point $(x,y) + \mathcal{E}[2] \in \mathcal{E}/\mathcal{E}[2]$, $q_\mathcal{E}$ maps it to its coset in the quotient group in $\mathcal{E}/\mathcal{E}[4]$:

$$
q_\mathcal{E}(\lbrace (x,y), (-x,-y)\rbrace) = \lbrace (x,y), (-x,-y), (\mathrm{i} y, \mathrm{i} x), (-\mathrm{i} y, -\mathrm{i} x) \rbrace.
$$

From which we can see it is a 2-to-1 map, since $\lbrace (x,y), (-x,-y) \rbrace$ and $\lbrace (\mathrm{i} y, \mathrm{i} x), (-\mathrm{i} y, -\mathrm{i} x) \rbrace$ map to the same point.

When its domain is restricted to the even points $[2]\mathcal{E}/\mathcal{E}[2]$ we see that $|[2]\mathcal{E}/\mathcal{E}[2]| = 2\ell$ so its range must have size $\ell$ - the size of $\mathcal{R}$. Thus $q_\mathcal{E}$ maps onto $\mathcal{R}$. $q$ is also simple to invert:

$$
q_\mathcal{E}^{-1}((x,y) + \mathcal{E}[4]) = \left\lbrace \lbrace(x,y), (-x,-y)\rbrace, \lbrace(\mathrm{i} y, \mathrm{i} x), (-\mathrm{i} y, -\mathrm{i} x)\rbrace \right\rbrace.
$$

Note the extra braces here. $q_\mathcal{E}^{-1}(P)$ contains two elements of $\mathcal{E}/\mathcal{E}[2]$ and each of these elements is a coset of size two.

This formula is valid for all points in $\mathcal{E}/\mathcal{E}[4]$, but for points that are not in $\mathcal{R} = [2]\mathcal{E}/\mathcal{E}[4]$ their preimages will not be in the range of $\hat{\theta}$, described next, and we will not be able to continue the inversion of $E_2$. This is expected since these are not validly encoded points.

The quotient map $q_\mathcal{J}$ is also simple to describe and invert

$$
q_\mathcal{J}((s,t)) = (s,t) + \mathcal{J}[2] = \lbrace (s,t), (-s,-t), (-1/s, t/s^2), (1/s, -t/s^2) \rbrace.
$$

So

$$
q_\mathcal{J}^{-1}((s,t) + \mathcal{J}[2]) = \lbrace (s,t), (-s,-t), (-1/s, t/s^2), (1/s, -t/s^2) \rbrace.
$$


### The Isogeny $\theta$ and its Inverse

The Elligator2 construction for Ristretto255 uses the Jacobi quartic curve $\mathcal{J}$ defined by the equation $t^2 = s^4 + A s^2 + 1$, which is 2-isogenous to our twisted Edwards curve $\mathcal{E}$. The 2-isogeny $\theta: \mathcal{J} \rightarrow \mathcal{E}$ is given by:

$$
\theta(s,t) = (x,y) = \left( \frac{2s}{t\sqrt{c}}, \frac{1-s^2}{1+s^2} \right)
$$

where for a twisted Edwards curve $ax^2+y^2=1+dx^2y^2$, the constant $c = a-d$. For Ristretto255, $a=-1$, so $c = -1-d$. Note that $\theta(s, t) = \theta(-s, -t)$, so this map is inherently 2-to-1 from the points on $\mathcal{J}$ to points on $\mathcal{E}$.

#### The Projected Map, $\hat{\theta}$

By a special case of Tate's Isogeny Theorem,[^2] since the isogenous curves $\mathcal{J}$ and $\mathcal{E}$ are both defined over $\mathbb{F}$, they have the same number of rational points, i.e., they have the same number of points in $\mathbb{F}$. Since $\theta$ is 2-to-1, this means that $\theta(\mathcal{J})$ is a subgroup of $\mathcal{E}$ of index 2. Since $\mathcal{E}$ is cyclic, $[2]\mathcal{E}$ is the only index-2 subgroup and we see that $\theta(\mathcal{J}) = [2]\mathcal{E}$.

We also see that  because 2-torsion points must map to 2-torsion points we have $\theta(\mathcal{J}[2]) \leqslant \mathcal{E}[2]$. Also, since $\mathcal{J}[2]$ has 4 points and $|\mathsf{ker(\theta)}| = 2$, at least one point in $\mathcal{J}[2]$ does not map to zero and $|\theta(\mathcal{J}(2))| \geq 2$. But $|\mathcal{E}[2]| = 2$ so it follows that $\theta(\mathcal{J}[2]) = \mathcal{E}[2]$.

Thus we are justified in talking about the projected map $\hat{\theta}$ defined in [Equation 1](#eq-reduced-theta).

#### Inverting $\theta$ (and $\hat{\theta}$)

Given a point $(x,y) \in \mathcal{E}$, we can invert $\theta$ to find its two preimages on $\mathcal{J}$. From the $y$-coordinate, we have:

$$
y = \frac{1-s^2}{1+s^2} \implies s^2 = \frac{1-y}{1+y}
$$

This gives two possible values for $s$, which we denote $s_0$ and $-s_0$. From the $x$-coordinate, we can then find the corresponding $t$ value:

$$
x = \frac{2s}{t\sqrt{c}} \implies t = \frac{2s}{x\sqrt{c}}
$$

Therefore, for each Edwards point $(x,y)$:

$$
\theta^{-1}((x,y)) = \lbrace (s_0,t_0), (-s_0, -t_0) \rbrace
$$

where $s_0 = \sqrt{\frac{1-y}{1+y}}$ and $t_0 = \frac{2s_0}{x\sqrt{c}}$.

Note that when writing an Edwards point in projective coordinates, $X:Y:Z$ this becomes

$$
s_0 = \sqrt{\frac{Z-Y}{Z+Y}},\qquad t_0 = \frac{2Z}{X\sqrt{c}}\sqrt{\frac{Z-Y}{Z+Y}}
$$

 These formulas allow us to write the inverse for $\hat{\theta}$ as well. Note that an equivalence class in $[2]\mathcal{E}/\mathcal{E}[2]$ is given by

 $$
 [X:Y:Z] + \mathcal{E}[2] = \left\lbrace [X:Y:Z], [-X:-Y:Z]\right\rbrace
 $$

So

 $$
 \hat{\theta}^{-1}(\lbrace [X:Y:Z], [-X:-Y:Z] \rbrace) = \left\lbrace (s_0, t_0), (-s_0, -t_0), \left(\frac{1}{s_0}, -\frac{t_0}{s_0^2}\right), \left(-\frac{1}{s_0}, \frac{t_0}{s_0^2}\right) \right\rbrace  = (s_0,t_0) + \mathcal{J}[2]
 $$

 Note that this inverse will exist if and only if $[X:Y:Z] \in [2]\mathcal{E}$.

### $e$ and its Inverse
<div id="subsec-e-and-inverse"></div>


The Elligator2 map from $\mathbb{F}$ to $\mathcal{J}$ is computed as follows. On input $r_0$, let $r = \mathrm{i}r_0^2$—either $0$ or a non-residue. Then compute

$$
\begin{align}
(s,t) &= \left( + \sqrt{ \frac{ (r+1)(d - 1)(d + 1) }{ (d r +1)(r + d) } } , \frac{ (r-1)(d - 1)^2 }{ (d r + 1)(r + d) } - 1 \right)
\end{align}
$$

or

$$
\begin{align}
(s,t) &= \left( - \sqrt{ \frac{ r(r+1)(d - 1)(d + 1) }{ (d r + 1)(r + d) } } , \frac{ -r(r-1)(-1 + d)^2 }{ (d r + 1)(r + d) } - 1 \right)
\end{align}
$$

depending on which square root exists, preferring the second when $r = 0$ and both are square.

#### The case $s > 0$

We want to invert this and will begin with the first case, where $s > 0$. First note that

$$
\frac{t+1}{s^2} = \frac{d-1}{d+1}\frac{r-1}{r+1}
$$

<div id="eq-a-over-s2" align="right">(2)</div>

We introduce the value $\alpha = \frac{d+1}{d-1}(t+1)$, which is denoted `a` in the source code. This gives

$$
\frac{\alpha}{s^2} = \frac{r-1}{r+1}
$$

from which we solve for $r$:

$$
r = \frac{s^2 + \alpha}{s^2 - \alpha}
$$

Thus our inverse will be

$$
r_0 = \pm\sqrt{-\mathrm{i}\frac{s^2 + \alpha}{s^2 - \alpha}}
$$

<div id="eq-r0case1" align="right">(3)</div>

#### The case $s\leq 0$

When considering the second case, $s \leq 0$, note that [Equation 2](#eq-a-over-s2) just negates the right hand side

$$
\frac{t+1}{s^2} = -\frac{d-1}{d+1}\frac{r-1}{r+1}
$$

leading to the formula

$$
r =  \frac{s^2 - \alpha}{s^2 + \alpha}
$$

Thus our inverse will be

$$
r_0 = \pm\sqrt{-\mathrm{i}\frac{s^2 - \alpha}{s^2 + \alpha}}
$$

<div id="eq-r0case2" align="right">(4)</div>

# Algorithm for Computing All 16 Preimages of a Point

We can combine these computations to invert $E_2$.

First, when inverting $q_\mathcal{E}$, observe that if a point $P\in\mathcal{R}$ has a representative with projective coordinates $[X:Y:Z]$ then its inverse under $q_\mathcal{E}$ is given by

$$
q_\mathcal{E}^{-1}(P) = \lbrace \lbrace [X:Y:Z], [-X:-Y:Z] \rbrace, \lbrace [Y:X:\mathrm{i}Z], [-Y:-X:\mathrm{i}Z] \rbrace \rbrace.
$$

Above we showed how, given a point $X:Y:Z \in [2]\mathcal{E}/\mathcal{E}[2]$ we can compute its preimage 

$$
\hat{\theta}^{-1}([X:Y:Z] + \mathcal{E}[2]) = \left\lbrace (s_0, t_0), (-s_0, -t_0), \left(\frac{1}{s_0}, -\frac{t_0}{s_0^2}\right), \left(-\frac{1}{s_0}, \frac{t_0}{s_0^2}\right) \right\rbrace
$$

We can repeat this process to compute preimage of $[Y:X:\mathrm{i}Z] + \mathcal{E}[2]$, the other point in $q_\mathcal{E}^{-1}(P)$:

$$
\hat{\theta}^{-1}([Y:X:\mathrm{i}Z] + \mathcal{E}[2]) = \left\lbrace (s_2, t_2), (-s_2, -t_2), \left(\frac{1}{s_2}, -\frac{t_2}{s_2^2}\right), \left(-\frac{1}{s_2}, \frac{t_2}{s_2^2}\right) \right\rbrace
$$


This already yields an algorithm to compute inverses of $E_2$ and complete the Lizard decoding, but we can make some significant optimizations.

## Step 1: Find Four Non-Dual Jacobi Points That Map to a Ristretto Point
<div id="subsec-step1"></div>

Based on the calculations above, once we compute the the four points $(s_i, t_i)$ as follows

$$
\begin{align}
    s_0 = \sqrt{\frac{Z-Y}{Z+Y}},&\quad& t_0 = \frac{2Z}{X\sqrt{c}}\sqrt{\frac{Z-Y}{Z+Y}} \\
    s_1 = \frac{1}{s_0},&\quad& t_1 = -\frac{t_0}{s_0^2} \\
    s_2 = \sqrt{\frac{\mathrm{i}Z-X}{\mathrm{i}Z+X}},&\quad& t_0 = \frac{2\mathrm{i}Z}{Y\sqrt{c}}\sqrt{\frac{\mathrm{i}Z-X}{\mathrm{i}Z+X}} \\
    s_3 = \frac{1}{s_2},&\quad& t_3 = -\frac{t_2}{s_2^2} \\
\end{align}
$$

we easily get all eight preimages of the Ristretto point $[X:Y:Z] + \mathcal{E}[4]$ by taking their "dual" points, where the *dual* of $(s,t)$ is $(-s,-t)$: 
$\lbrace \pm(s_i, t_i) \rbrace$.

This computation is performed by the function `to_jacobi_quartic_ristretto` in `src/lizard/lizard_ristretto.rs`. We describe that computation now.


### Sharing Computation

We can compute $s_0$ and  $s_1$ more efficiently together by precomputing $1/\sqrt{Z^2 - Y^2}$, then multiplying by $(Z-Y)$ and $(Z+Y)$ respectively. Similarly we can compute $s_2$ and $s_3$ together by precomputing $1/\sqrt{X^2 + Z^2}$ then multiplying by $(\mathrm{i}Z-X)$ and $(\mathrm{i}Z+X)$ respectively.

It turns out that we can perform both of these precomputations while only computing one square root. In particular, compute the following value:

$$
\gamma = \frac{1}{\sqrt{Y^4X^2(Z^2-Y^2)}}
$$

Then we can easily compute $s_0$ and $s_1$ with inexpensive field operations:

$$
s_0 = \gamma Y^2 (Z-Y) X, \quad s_1 = \gamma Y^2 (Z+Y) X
$$

Now $\gamma Y^2 = 1/\sqrt{X^2(Z^2 - Y^2)}$ and, when we are computing $s_2, s_3$ the analog of this value is $-i/\sqrt{Y^2(X^2 + Z^2)}$. So we can compute

$$
\begin{align}
    \sqrt{\frac{-1}{Y^2(X^2 + Z^2)}} &=& \sqrt{\frac{Z^2 - Y^2}{(X^2 + Z^2)(Y^2 - Z^2)}} \\
         &=& \sqrt{\frac{Z^2 - Y^2}{X^2Y^2 + dX^2Y^2}} \\
         &=& \frac{1}{\sqrt{d+1}}\sqrt{\frac{Z^2-Y^2}{X^2Y^2}} \\
         &=&  \frac{1}{\sqrt{d+1}} \gamma (Z^2 - Y^2)
\end{align}
$$

Where the equality in the second line comes from using the curve equation for $\mathcal{E}$: $Y^2Z^2 - X^2Z^2 = Z^4 + dX^2Y^2$. The quantity $1/\sqrt{d+1}$ is a constant that can be precomputed, so $\sqrt{-1/(Y^2(X^2 + Z^2))}$ —and hence $(s_2,t_2)$ and $(s_3,t_3)$—can be computed from $\gamma$ without computing an additional square root.

### Step by Step Through the Rust Implementation

With that background, we can understand the code in `src/lizard/lizard_ristretto.rs`. The following steps can be found in the `RistrettoPoint::to_jacobi_quartic_ristretto()` function:

1. $\gamma \leftarrow 1/\sqrt{Y^4X^2(Z^2 - Y^2)}$
1. $D \leftarrow \gamma Y^2$
1. $\mathsf{s\\_over\\_x} = D(Z-Y)$, $\mathsf{sp\\_over\\_xp} = D(Z+Y)$
1. $s_0 = \mathsf{s\\_over\\_x}\cdot X$, $s_1 = \mathsf{sp\\_over\\_xp}\cdot X$. Note that

$$
s_0 = D(Z-Y)X = \frac{X(Z-Y)}{\sqrt{X^2(Z^2 - Y^2)}} = \sqrt{\frac{Z-Y}{Z+Y}}
$$

as required.

5. $\mathsf{tmp} \leftarrow \frac{-2}{\sqrt{-d-1}}Z$
5. $t_0 \leftarrow \mathsf{tmp}\cdot \mathsf{s\\_over\\_x}$, $t_1 \leftarrow \mathsf{tmp}\cdot \mathsf{sp\\_over\\_xp}$
5. $(s_0,t_0)$ and $(-s_0, -t_0)$ are preimages of $X:Y:Z$ while $(s_1,t_1)$ and $(-s_1,-t_1)$ are preimages of $-X:-Y:Z$.
5. $D \leftarrow (Z^2 - Y^2)\gamma \cdot -1/\sqrt{-d-1}$ (This equals $\frac{1}{\sqrt{-d-1}}\sqrt{-\frac{Z^2 - Y^2}{Y^4X^2}}$)
5. $\mathsf{s\\_over\\_y} \gets D(\mathrm{i}Z - X)$
5. $\mathsf{sp\\_over\\_yp} \leftarrow D (\mathrm{i}Z + X)$
5. $s_2 \leftarrow \mathsf{s\\_over\\_y} \cdot Y$, $s_3 \leftarrow \mathsf{sp\\_over\\_yp} \cdot Y$
5. $\mathsf{tmp} \leftarrow \frac{-2}{\sqrt{-d-1}}\mathrm{i}Z$
5. $t_2 \leftarrow \mathsf{tmp}\cdot \mathsf{s\\_over\\_y}$, $t_3 \leftarrow \mathsf{tmp}\cdot \mathsf{sp\\_over\\_yp}$
5. $(s_2,t_2)$ and $(-s_2, -t_2)$ are preimages of $Y:X:\mathrm{i}Z$ while $(s_3,t_3)$ and $(-s_3,-t_3)$ are preimages of $-Y:-X:\mathrm{i}Z$.

Altogether this gives us eight candidate Jacobi Quartic points:

$$
(s_0, t_0),(s_1, t_1),(s_2, t_2),(s_3, t_3),
(-s_0, -t_0),(-s_1, -t_1),(-s_2, -t_2),(-s_3, -t_3)
$$

Note the `to_jacobi_quartic_ristretto()` function only returns the first 4 points. The remaining ones are derived in `RistrettoPoint::elligator_ristretto_flavor_inverse()` in the same file.

The conditional assignments in `to_jacobi_quartic_ristretto()` are explained below.

### Handling Special Cases

The formulas above assume non-zero denominators. The special cases occur when the input point is a 2-torsion or 4-torsion point.

If the input point is the identity element, its representatives are $(0,1)$, $(0,-1)$, $(\mathrm{i}, 0)$, and $(-\mathrm{i}, 0)$.

1. For $(0,1)$, we have $y=1$, so $s^2 = 0 \implies s=0$. This gives the Jacobi point $(0,1)$.
1. For $(0,-1)$, we have $y=-1$, so $s^2$ is undefined (division by zero). However, this 1. corresponds to $s^2 \to \infty$. In the code we simply repeat the point $(0,1)$ in this 1. This repetition is harmless since this point has no preimage under the Elligator2 map from $\mathbb{F}$ to $\mathcal{J}$ and cannot correspond to a Lizard encoded bitstring.
1. For $(\mathrm{i}, 0)$, we have $y=0$, so $s^2=1 \implies s=\pm 1$. The preimages are $(\pm 1, \frac{2\mathrm{i}}{\sqrt{-d-1}})$.
1. For $(-\mathrm{i}, 0)$, we have $y=0$, so $s^2=1 \implies s=\pm 1$. The preimages are $(\pm 1, \mp\frac{2\mathrm{i}}{\sqrt{-d-1}}))$.



## Step 3: Compute the 16 Field Element Preimages

The computation of $e^{-1}$ [described above](#subsec-e-and-inverse) required breaking the computation into two cases. To facilitate performing these computations efficiently in constant time, we perform both computations at once. This code can be found in `src/lizard/jacobi_quartic.rs` in `JacbobiPoint::e_inv()`.

We begin by computing the value

$$
y = \frac{1}{\sqrt{\mathrm{i} (s^4 - \alpha^2)}}
$$

Note that
1. $\frac{1}{\mathrm{i} (s^4 - \alpha^2)}$ is a quadratic residue if and only if $(s^4 - \alpha^2)$ is not a quadratic residue.
1. $s^4 - \alpha^2$ is not a quadratic residue if and only if exactly one of $s^2 - \alpha$ and $s^2 + \alpha$ is a quadratic residue.
1. exactly one of $s^2 - \alpha$ and $s^2 + \alpha$ is a quadratic residue if and only if both $\frac{s^2 - \alpha}{s^2 + \alpha}$ and $\frac{s^2 + \alpha}{s^2 - \alpha}$ are non-residues.
1. Both $\frac{s^2 - \alpha}{s^2 + \alpha}$ and $\frac{s^2 + \alpha}{s^2 - \alpha}$ are non-residues if and only if $\sqrt{-\mathrm{i}\frac{s^2 + \alpha}{s^2 - \alpha}}$ and $\sqrt{-\mathrm{i}\frac{s^2 - \alpha}{s^2 + \alpha}}$ exist.

Hence we see that $(s,t)$ has a preimage if and only if $y$, as defined above, exists.

With $y$ computed we can now compute the final preimage. Let $\mathsf{sgn}(s)$ denote the sign function. Then we can consolidate Equations [3](#eq-r0case1) and [4](#eq-r0case2) into

$$
r_0 =  \pm(\alpha + \mathsf{sgn}(s)s^2) y
$$

### Relation to the Formulas in Decaf

These computations can also be seen in [Decaf][decaf], which also defines the map $e: \mathbb{F} \rightarrow \mathcal{J}$, but we need to clarify an important difference in notation. In that work, they use variables $a$ and $d$ as parameters for a different, but isogenous, twisted Edwards curve. If we let $\hat{a}$ and $\hat{d}$ denote the Edwards curve parameters from Decaf we have the relations

$$
\hat{a} = -a, \quad \hat{d} = \frac{ad}{a-d}
$$

Note that in this notation we have

$$
2\hat{d} - \hat{a} =
\frac{d-1}{d+1}
$$

hence the formula given in for the inverse of $e$ can be rewritten

$$
nr_0^2 = r = \frac{(2\hat{d} - \hat{a})s^2 + c(t+1)}{(2\hat{d} - \hat{a})s^2 - c(t+1)} = \frac{cs^2 + (t+1)\frac{d+1}{d-1}}{cs^2 - (t+1)\frac{d+1}{d-1}}
$$

where $c = \mathsf{sgn}(s)$. There is another detail we need to take care of. The map in Decaf is defined parameterized by a non-square $n\in\mathbb{F}_{p}$. We take $n = \sqrt{-1}$ as the non-residue parameter.

You can see this choice of $n$, in the implementation of `RistrettoPoint::elligator_ristretto_flavor()`.

[^1]: Anderson, T. W. and Samuels, S. M., Some Inequalities Among Binomial and Poisson Probabilities _Proc. Fifth Berkeley Symp. on Math. Statist. and Prob._, Vol. 1. Univ. of Calif. Press (1967).
[^2]: Tate, J. Endomorphisms of abelian varieties over finite fields. _Invent Math_ 2, 134–144 (1966). https://doi.org/10.1007/BF01404549 [[pdf](https://pazuki.perso.math.cnrs.fr/index_fichiers/Tate66.pdf)]

[elligator]: https://elligator.org/
[ristretto]: https://ristretto.group/
[lizard]: https://arxiv.org/abs/1911.02674
[decaf]: https://eprint.iacr.org/2015/673
