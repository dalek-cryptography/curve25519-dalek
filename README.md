
# curve25519-dalek [](https://docs.rs/curve25519-dalek/badge.svg)

**A low-level cryptographic library for point, group, field, and scalar
operations on a curve isomorphic to the twisted Edwards curve defined by x²+y²
= 121665/121666 x²y² over GF(2²⁵⁵ - 19).**

**SPOILER ALERT:** *The Twelfth Doctor's first encounter with the Daleks is in
his second full episode, "Into the Dalek". A beleaguered ship of the "Combined
Galactic Resistance" has discovered a broken Dalek that has turned "good",
desiring to kill all other Daleks. The Doctor, Clara and a team of soldiers
are miniaturized and enter the Dalek, which the Doctor names Rusty. They
repair the damage, but accidentally restore it to its original nature, causing
it to go on the rampage and alert the Dalek fleet to the whereabouts of the
rebel ship. However, the Doctor manages to return Rusty to its previous state
by linking his mind with the Dalek's: Rusty shares the Doctor's view of the
universe's beauty, but also his deep hatred of the Daleks. Rusty destroys the
other Daleks and departs the ship, determined to track down and bring an end
to the Dalek race.*

Significant portions of this code are ported from
[Adam Langley's Golang ed25519 library](https://github.com/agl/ed25519), along
with referencing the ref10 implementation.

## TODO

 * Implement hashing to a point on the curve.
 * Maybe implement Mike Hamburg's Decaf point compression format.
