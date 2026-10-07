"""Check manuscript threshold arithmetic; does not certify analytic integrals."""

from fractions import Fraction as F

a = F(27, 1000)
b = F(27, 10000)
m = F(12, 25)
e = F(17, 200)
t = F(117, 500)

margin = 3*a*a*t**4 - (3*a*a - b*m)*e*e
assert margin == F(7476945327, 62500000000000000)
assert margin > 0

rho_lower = t**4 / e**2
assert rho_lower == F(187388721, 451562500)
assert 3*(1-rho_lower) == F(792521337, 451562500)
assert b*m/a**2 == F(16, 9)
assert 3*(1-rho_lower) < b*m/a**2

m2_limit_squared = b*m*e**2 / (3*(e**2-t**4))
assert m2_limit_squared == F(195075, 264173779)
assert a*a < m2_limit_squared


from fractions import Fraction as F

m0_upper = F(501, 1000)
m2_lower = F(227, 10000)
m4_upper = F(3, 1000)
gap = 3*m2_lower**2 - m0_upper*m4_upper
assert gap == F(4287, 100000000)
assert gap > 0
assert gap/3 == F(1429, 100000000)

tail = F(1, 50000000)
assert F(125142475349, 250000000000) <= m0_upper-tail
assert F(11394869437, 500000000000) >= m2_lower
assert F(1499664107, 500000000000) <= m4_upper-tail

print("PASS: both manuscript appendix arithmetic checks")
