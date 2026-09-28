"""Exact scalar margins; analytic entropy and logarithm inequalities are premises."""
from fractions import Fraction as F

a = F(2 * 40**2, 3 * 750**2)
b = F(4 * 22**2, 3 * 750**2)
q = 2 * a / 3
assert q == F(64, 50625)
assert 64**3 * 2**29 >= 50625**3  # implies log2(1/q) <= 29/3
margin = (F(488, 1000)**2 - a) / 3 - b / (2 * F(69, 100))
margin -= (F(32, 3) + F(100, 69)) * q + F(1, 16)
assert margin == F(141043, 1397250000) > 0
print("Exact constant-750 logarithm threshold and rational sector margin passed.")
