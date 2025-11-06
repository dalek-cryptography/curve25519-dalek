# Python script to compute inverse and format for Verus
from math import gcd

# IMPORTANT: Make sure these match your Verus definitions EXACTLY
montgomery_radix = 2**260
group_order = (
    2**252 + 27742317777372353535851937790883648493
)  # your group order value here


print(f"Montgomery radix: 2^260 = {montgomery_radix}")
print(f"Group order: {group_order}")
print()

# Check if inverse exists
g = gcd(montgomery_radix, group_order)
print(f"gcd(montgomery_radix, group_order) = {g}")

if g != 1:
    print("ERROR: Modular inverse does not exist! gcd must be 1")
    print("This means montgomery_radix and group_order are not coprime")
    exit(1)

print("✓ Inverse exists (gcd = 1)")
print()

# Compute modular inverse
inv = pow(montgomery_radix, -1, group_order)

# CRITICAL: Verify the result
result = (inv * montgomery_radix) % group_order
print(f"Verification: (inv * R) % N = {result}")

if result != 1:
    print(f"ERROR: Verification failed! Expected 1, got {result}")
    exit(1)

print("✓ Verification passed!")
print()

# Print the inverse
print(f"inv_montgomery_radix = 0x{inv:x}")
print(f"inv_montgomery_radix = {inv}")
print()

# Format as limbs
print("// Copy this into Verus:")
print("pub open spec fn inv_montgomery_radix() -> nat {")
limbs = []
temp = inv
while temp > 0:
    limbs.append(temp & 0xFFFFFFFFFFFFFFFF)
    temp >>= 64

parts = []
for i, limb in enumerate(limbs):
    if limb != 0:
        if i == 0:
            parts.append(f"0x{limb:x}_u64 as nat")
        else:
            parts.append(f"pow2({i * 64}) * 0x{limb:x}_u64 as nat")

print("    " + " +\n    ".join(parts))
print("}")
