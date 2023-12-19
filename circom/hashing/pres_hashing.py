circom_P = 21888242871839275222246405745257275088548364400416034343698204186575808495617 
P = circom_P

r = ((P // 17) + 19) % P

# Consider the string a to be the coefficient sequence of a single-variable polynomial F
# Then evaluate F at a random point (in our case, r)
#
# To encounter a collision using this hash (two different strings mapping to the same value), 
# it means we have two different polynomials F and G such that F(r) = G(r)
#
# But: 
# - in general a non-zero polynomial of degree N in a certain field has at most N roots in the field
# - F(r) = G(r) => (F - G)(r) == 0. But (F - G) is a non-zero polynomial of degree at most N, so
# there are at most N values of r for which the two evaluations can coincide.
#
# In our case, N = len(a) and the field is Z(P), so the probability of a collision for a random r
# is at most (len(a) / P). In our case, P ~= 2 ^ 256, so this is completely negligible.

def fingerprint_str(a: str) -> int:
    n = len(a)
    powers = [r ** i for i in range(n)]
    return sum([powers[i] * ord(a[i]) for i in range(n)]) % P

def fingerprint_concat(h_a: int, len_a: int, h_b: int, len_b: int) -> int:
    len_ab = len_a + len_b
    h_ab = h_a + h_b * (r ** len_a)
    return h_ab % P

first = "abc"
second = "def"

assert ( 
    fingerprint_str(first + second) 
    == 
    fingerprint_concat(
        fingerprint_str(first), 
        len(first), 
        fingerprint_str(second), 
        len(second)
    )
)

def fingerprint_set(s: list[int]) -> int:
    res = 1
    for elem in s:
        res = (res * (r - elem)) % P
    return res

print(fingerprint_set([1, 2, 3, 3, 3]))
print(fingerprint_set([2, 3, 1, 3, 3]))
print(fingerprint_set([1, 2, 3, 3]))
print(fingerprint_set([3, 5, 7, 9]))