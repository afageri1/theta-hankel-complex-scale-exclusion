from fractions import Fraction
from mpmath import iv

iv.dps = 40
N = 1000
dx = iv.mpf(2) / N
a = iv.mpf(1) / 4

def phi(u):
    """Explicit series for the project's differential kernel."""
    t = iv.exp(2 * u)
    total = iv.mpf(0)
    for n in range(1, 7):
        p = iv.pi * n * n
        total += (8*p*p*t*t - 12*p*t) * iv.exp(u/2 - p*t)

    # Upper bound for n >= 7, using n^4 <= exp(n^2)
    # and n^2 >= 49 + 15*(n-7).
    c = iv.pi*t - 1
    tail = (
        8*iv.pi**2 * iv.exp(iv.mpf(9)/2*u)
        * iv.exp(-49*c) / (1 - iv.exp(-15*c))
    )
    return total + iv.mpf([0, 1])*tail

M0 = M2 = M4 = E = J = iv.mpf(0)

for j in range(N):
    lo = iv.mpf(j)*dx
    hi = iv.mpf(j+1)*dx
    u = iv.mpf([j, j+1])*dx
    p = phi(u)

    M0 += p*dx
    M2 += p*(hi**3 - lo**3)/3
    M4 += p*(hi**5 - lo**5)/5
    E += p**2*(hi**2 - lo**2)/2

    # Integral of Phi(x+y) over [0,a]^2.
    if j < 125:
        J += p*(hi**2 - lo**2)/2
    elif j < 250:
        J += p*(2*a*dx - (hi**2 - lo**2)/2)

# Global envelope:
# Phi(u) <= 300*exp(9*u/2 - pi*exp(2*u)), u >= 0.
envelope_constant = (
    8*iv.pi**2*iv.exp(1)
    / (1 - iv.exp(-3*(iv.pi-1)))
)
assert envelope_constant.b < 300

# Tangent bound for exp(2*u) gives exponential tails beyond L.
L = iv.mpf(2)
k = 2*iv.pi*iv.exp(2*L) - iv.mpf(9)/2
assert k.a > 0
C = 300*iv.exp(iv.mpf(9)/2*L - iv.pi*iv.exp(2*L))

M2 += iv.mpf([0, 1])*C*(
    L**2/k + 2*L/k**2 + 2/k**3
)
E += iv.mpf([0, 1])*C**2*(
    L/(2*k) + 1/(4*k*k)
)

# f = indicator_[0,a]/sqrt(a); T = <A f, f>.
T = J/a

assert M0.a > iv.mpf(12)/25
assert M4.a > iv.mpf(7)/2500
assert M2.b < iv.mpf(3)/125
assert E.b < iv.mpf(17)/200
assert T.a > iv.mpf(6)/25

for name, value in [
    ("M0", M0), ("M2", M2), ("M4", M4), ("E", E), ("T", T)
]:
    print(name, value)

# Q >= T^4, hence theta = Q/E^2 >= theta_lower.
theta_lower = Fraction(6, 25)**4 / Fraction(17, 200)**2

# M4*M0/(3*M2^2) > 7/9.
assert 0 < theta_lower < 1
lhs_lower = Fraction(7, 9)/(1 - theta_lower)
assert lhs_lower > 1

print("theta_lower =", theta_lower)
print("correct_LHS_lower =", lhs_lower)
print("decimal =", float(lhs_lower))
print("PASS: external interval bounds for scaled obstruction")
print("Not a Lean kernel certificate.")
