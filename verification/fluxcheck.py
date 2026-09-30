"""Finite staircase counts for the restricted flux proposition.

The universal phase inequality and Riemann-sum limit are manuscript proofs,
not consequences of these finite regressions.
"""
if not __debug__:
    raise SystemExit("This check uses assert statements; run it without python -O.")
import math

for M in (6,7,12,48,64):
    for t in range(5,M+4):
        region={(M-1,M-1)} | {(M-1,j) for j in range(1,M-1)}
        region |= {(i,j) for i in range(M-2) for j in range(M-1) if i+j<=t+M-8}
        h=M+3-t
        assert len(region)==(M-1)**2-h*(h+1)//2
    small={(0,M-2)} | {(i,j) for i in range(M) for j in range(M) if i+j<=M-3}
    assert len(small)==1+(M-1)*(M-2)//2
constant=2*math.pi**2*math.sqrt(2)*math.log(1+math.sqrt(2))/4
for M in (100,1000,10000):
    minimum=1+(M-1)*(M-2)//2
    total=1/minimum+sum(1/((M-1)**2-h*(h+1)/2) for h in range(M-1))
    lower=2*M*(-math.expm1(-2*math.pi**2*total/8))
    upper=2*math.pi**2*M*total/4+4*math.pi**2*M**3/minimum**2
    assert 0<lower<upper
    if M==10000: assert abs(lower-constant)<.01 and abs(upper-constant)<.03
print('Restricted flux: five exact staircase-count regressions and three asymptotic-bound samples passed.')
