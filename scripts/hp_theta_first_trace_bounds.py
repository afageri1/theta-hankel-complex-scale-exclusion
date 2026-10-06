from decimal import (
    Decimal as D, Context, ROUND_FLOOR,
    ROUND_CEILING, localcontext
)
from fractions import Fraction as Q

LO = Context(prec=45, rounding=ROUND_FLOOR)
HI = Context(prec=45, rounding=ROUND_CEILING)

class I:
    """Closed interval with outward-rounded arithmetic."""

    def __init__(self, a, b=None):
        self.lo = D(a)
        self.hi = D(a if b is None else b)

    def __add__(a, b):
        b = iv(b)
        return I(LO.add(a.lo, b.lo), HI.add(a.hi, b.hi))

    __radd__ = __add__

    def __neg__(a):
        return I(a.hi.copy_negate(), a.lo.copy_negate())

    def __sub__(a, b):
        return a + (-iv(b))

    def __mul__(a, b):
        b = iv(b)
        pairs = [
            (x, y)
            for x in (a.lo, a.hi)
            for y in (b.lo, b.hi)
        ]
        return I(
            min(LO.multiply(x, y) for x, y in pairs),
            max(HI.multiply(x, y) for x, y in pairs),
        )

    __rmul__ = __mul__

    def __truediv__(a, b):
        b = iv(b)
        assert b.lo > 0
        return a * I(
            LO.divide(D(1), b.hi),
            HI.divide(D(1), b.lo),
        )

    def exp(a):
        # Decimal.exp is correctly rounded, half-even.
        # Expand each endpoint by one representable step.
        with localcontext(HI):
            return I(
                a.lo.exp().next_minus(),
                a.hi.exp().next_plus(),
            )

    def __str__(a):
        return f"[{a.lo}, {a.hi}]"

def iv(x):
    return x if isinstance(x, I) else I(x)

def rat(q):
    return I(
        LO.divide(D(q.numerator), D(q.denominator)),
        HI.divide(D(q.numerator), D(q.denominator)),
    )

def atan_bounds(d, n):
    # Alternating-series enclosure for atan(1/d).
    s = sum(
        (Q((-1)**j, (2*j+1)*d**(2*j+1))
         for j in range(n)),
        Q(0),
    )
    t = s + Q((-1)**n, (2*n+1)*d**(2*n+1))
    return I(rat(min(s, t)).lo, rat(max(s, t)).hi)

# Machin identity; no floating-point value of pi.
pi = 16*atan_bounds(5, 42) - 4*atan_bounds(239, 14)
assert pi.lo > 3

N = 6
cells = 256
U = I(2)
step = rat(Q(2, cells))

# h(a) <= 64 exp(-a/2).
# For n=N+1+k:
# n^2 >= (N+1)^2 + (2N+3)k.
series_tail = (
    (-I("1.5")*((N+1)**2)).exp()
    / (I(1) - (-I("1.5")*(2*N+3)).exp())
)

def endpoint_sum(u):
    t = (2*u).exp()
    total = I(0)
    for n in range(1, N+1):
        a = pi*n*n*t
        total = total + (4*a*a - 6*a)*(-a).exp()
    return total

m0 = I(0)
m2 = I(0)
energy = I(0)

for j in range(cells):
    left = rat(Q(2*j, cells))
    right = rat(Q(2*(j+1), cells))

    # h decreases for a >= 3.
    lower = (
        2*(left/2).exp()*endpoint_sum(right)
    ).lo

    upper = (
        2*(right/2).exp()*endpoint_sum(left)
        + 128*(right/2).exp()*series_tail
    ).hi

    assert lower >= 0
    p = I(lower, upper)
    u = I(left.lo, right.hi)

    m0 = m0 + step*p
    m2 = m2 + step*u*u*p
    energy = energy + step*u*p*p

# Phi(u) <= 256 exp(u/2 - 1.5 exp(2u)).
# For u=2+t, exp(4)>50 and exp(2t)>=1+2t
# give Phi(2+t) <= C exp(-q t).
assert I(4).exp().lo > 50
assert (-I("4.5")).exp().hi < D("0.5")

c = 256*I(1).exp()*(-I(75)).exp()
q = I("149.5")

tail0 = c/q
tail2 = c*(
    U*U/q + 2*U/(q*q) + I(2)/(q*q*q)
)
tail_energy = c*c*(
    U/(2*q) + I(1)/(4*q*q)
)

m0 = m0 + I(0, tail0.hi)
m2 = m2 + I(0, tail2.hi)
energy = energy + I(0, tail_energy.hi)

ratio = m2/(2*m0)

print("PI enclosure:", pi)
print("Integral Phi:", m0)
print("Integral u^2 Phi:", m2)
print("E = integral u Phi^2:", energy)
print("R = M2/(2 M0):", ratio)

assert energy.lo > D("0.07")
assert ratio.hi < D("0.03")

print("PASS: E > 0.07 > 0.03 > R")
print("External interval computation; not a Lean kernel proof.")
