#!/usr/bin/env python3
"""Exact quartic smooth-moment and twelve-variable certificate.

Only Python's standard library is used. The field analytic premises are
proved in the quartic section of the article; this script checks every number.
"""
from fractions import Fraction as F

b3, b4 = F(161, 50), F(461, 100)
phi3, phi4, phi5 = F(109, 1000), F(7, 50), F(3, 16)

def update(pair):
    a, b = pair
    t3 = max(3 + 2*phi3,
             1 + F(3, 2)*phi3 + F(1, 2)*(1-phi3)*b)
    t4 = max(1 + a + (6-a)*phi4,
             F(5, 4) + F(11, 4)*phi4 + F(3, 4)*(1-phi4)*b)
    return t3, t4

out3, out4 = update((b3, b4))
assert out3 == F(1609, 500)          # 3.218
assert out4 == F(57615, 12500)       # 4.6092
assert b3-out3 == F(1, 500)
assert b4-out4 == F(1, 1250)
rho = F(43, 50)
assert F(1, 2)*(1-phi3) <= rho
assert 1-phi4 == rho
assert F(3, 4)*(1-phi4) <= rho
assert 4*rho**64 < min(b3-out3, b4-out4)

# A finite iteration, rather than an unperformed limiting argument.
pair = (F(6), F(8))
for _ in range(64):
    pair = update(pair)
assert pair[0] < b3 and pair[1] < b4

# Ordinary Hua interpolation supplies b5=27/4 and b6=17/2.
assert F(3, 4)*5 + F(1, 4)*12 == F(27, 4)
assert F(1, 2)*5 + F(1, 2)*12 == F(17, 2)
b6 = F(17, 2)
floor = F(5, 2) + F(13, 16)*b4
assert floor == F(9993, 1600)

def cubic(c):
    major = F(31, 16) + F(13, 32)*c + F(13, 64)*b6
    return max(floor, major)

c = F(27, 4)
history = []
for _ in range(3):
    c = cubic(c)
    history.append(c)
assert history == [F(205, 32), F(6417, 1024), F(9993, 1600)]
assert 4*(1-phi5) == F(13, 4) > 2
assert 1-4*phi5 == F(1, 4) > 0

delta = c-6
assert delta == F(393, 1600) < F(1, 4)
D = 2-8*delta
assert D == F(7, 200) > 0
assert D/20 == F(7, 4000)

# Even U12 bootstrap and mixed f^2 h^10 minor integral.
weights = (F(1, 10), F(2, 5), F(1, 2))
assert sum(weights) == 1
assert 20*weights[0] == 2
assert 10*weights[1] + 12*weights[2] == 10
minor_exp = 15*weights[0] + c*weights[1] + 8*weights[2]
assert minor_exp == 8-F(7, 4000)
assert F(2, 12)+F(10, 12) == 1
assert 12 > 2*4

print('VERIFIED: 64 finite seed iterations and 3 finite cubic refinements.')
print('Seed supersolution:', b3, b4)
print('Tenth moment:', c, '=', float(c))
print('Excess:', delta, '; bootstrap margin:', D)
print('Minor-arc saving before epsilon:', D/20)
