"""Check the analytic corner formulas used in the manuscript, separately from source data."""
if not __debug__:
    raise SystemExit("Verification requires assertions; run without -O/-OO or PYTHONOPTIMIZE.")
from independent_corner import Corner,inverse
import json
checks=0
for M in [5,8,12,17,24]:
    C=Corner(M)
    for i in range(M):
        x=M-1-i;Di_inv=inverse(C.b[i,M-1])
        for v in range(1,M+2):
            assert Di_inv[v-1]+1==(v+1 if v<=x+3 else v+M-x)
    for d in range(3,M-2):
        ucount=ecount=0
        for i in range(M):
            for j in range(M):
                x=M-1-i;y=M-1-j;c=(i,j)
                def F(v):
                    r=y+4
                    if v<r:return v+x+1
                    if v<=r+x:return r+x+1-v
                    return v
                predA=(d+1,d+2) if d<=x+1 else (F(d-x),F(d-x+1))
                if d<=y+1:predB=(d+1,d+2)
                else:
                    def H(v):return v+1 if v<=x+3 else v+M-x
                    predB=(H(d-y)+y,H(d-y+1)+y)
                a=tuple(z+1 for z in C.lamp('a',d,c));b=tuple(z+1 for z in C.lamp('b',d,c))
                assert a==predA,(M,d,c,a,predA)
                assert b==predB,(M,d,c,b,predB)
                uf=set(a)!=set(b);assert uf==(x+y<=d-3);ucount+=uf
                dest,q=C.evaluate('Ba',c);qi=inverse(q)
                transported={qi[z] for z in C.lamp('a',d,dest)}
                ef=set(C.lamp('a',d,c))!=transported
                region=(y==M-1 and x<=d-2) or (0<=y<=d-3 and (d-3-y)//2<=x<=d-3-y)
                assert ef==region,(M,d,c,ef,region)
                ecount+=ef;checks+=1
        assert ucount==(d-1)*(d-2)//2
        assert ecount==d*d//4+d-2
        print(json.dumps({'M':M,'d':d,'U_clocks':ucount,'E_clocks':ecount,'all_coordinate_formulas':True}),flush=True)
print('CLOCK_DEPTH_CASES_CHECKED',checks)
