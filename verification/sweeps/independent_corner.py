"""Independent coordinate-permutation corner engine, from PDF Proposition 6.1.
No imported source code. Colorings are never enumerated.
"""
if not __debug__:
    raise SystemExit("Verification requires assertions; run without -O/-OO or PYTHONOPTIMIZE.")
import json,random,time
from pathlib import Path
def compose(p,q):return tuple(q[x] for x in p)
def inverse(p):
    z=[0]*len(p)
    for i,x in enumerate(p):z[x]=i
    return tuple(z)
def trans(n,i,j):
    z=list(range(n));z[i],z[j]=z[j],z[i];return tuple(z)
class Corner:
    def __init__(self,M):
        self.M=M;ell=2*M+2;n=3*ell;self.n=n;self.id=tuple(range(n));self.tau=trans(n,0,1)
        def cycle(r):return tuple([r-1]+list(range(r-1))+list(range(r,n)))
        D=[cycle(2*ell-M+1)]
        for i in range(M-1):
            p=inverse(cycle(ell-i-(M-1)))
            for q in [self.tau,D[-1],cycle(ell-i)]:p=compose(p,q)
            D.append(p)
        self.a={(i,j):cycle(ell-i-j) for i in range(M) for j in range(M)}
        self.b={(i,j):D[i] if j==M-1 else cycle(2*ell-j) for i in range(M) for j in range(M)}
        self.cache={}
    def evaluate(self,word,c):
        p=self.id;i,j=c;M=self.M
        for g in word:
            if g=='a':q=self.a[i,j];i=(i+1)%M
            elif g=='b':q=self.b[i,j];j=(j+1)%M
            elif g=='A':i=(i-1)%M;q=inverse(self.a[i,j])
            elif g=='B':j=(j-1)%M;q=inverse(self.b[i,j])
            else:q=self.tau
            p=compose(p,q)
        return (i,j),p
    def lamp(self,g,d,c):
        key=(g,d,c)
        if key not in self.cache:
            dest,p=self.evaluate(g*d,c);pi=inverse(p)
            self.cache[key]=(pi[0],pi[1])
        return self.cache[key]
    def block_perm(self,L,g,c):
        # Products of transported involutions, sparse support updates.
        p={}
        for q,kind in L:
            x,y=self.lamp(g,q+kind,c)
            p={k:(y if v==x else x if v==y else v) for k,v in p.items()}
            if x not in p:p[x]=y
            if y not in p:p[y]=x
            p={k:v for k,v in p.items() if k!=v}
        return p
    def failures(self,L):
        return [(i,j) for i in range(self.M) for j in range(self.M) if self.block_perm(L,'a',(i,j))!=self.block_perm(L,'b',(i,j))]
    def relators(self):
        R=['ss','sasA'*3,'saasAASaaSAA','abABS','asAbSB']
        counts=[]
        for w in R:
            counts.append(sum(self.evaluate(w,(i,j))!=((i,j),self.id) for i in range(self.M) for j in range(self.M)))
        return counts
    def word_failures(self,w,swap=False):
        if swap:w=w.translate(str.maketrans('aAbB','bBaA'))
        return sum(self.evaluate(w,(i,j))!=((i,j),self.id) for i in range(self.M) for j in range(self.M))
def main():
    rng=random.Random(481516);start=time.monotonic()
    for M in [5,8,12,20]:
        C=Corner(M);r=C.relators();assert r==[0,0,0,1,0],r
        print(json.dumps({'M':M,'relator_failure_clock_counts':r}),flush=True)
    for K in [4,6,8,10,12,16,24,32]:
        C=Corner(K+4)
        for name,L in [('single',[(K,1)]),('double_cancel',[(K,1)]*2),('triple',[(K,1)]*3)]:
            F=C.failures(L)
            expected=0 if name=='double_cancel' else K*(K-1)//2
            assert len(F)==expected,(K,name,len(F),expected)
            print(json.dumps({'K':K,'M':C.M,'list':L,'name':name,'failing_clocks':len(F),'doubled_r4_lower':2*len(F),'sample_offsets':F[:8]}),flush=True)
    C=Corner(16)
    for n in range(12):
        L=sorted([(rng.randrange(13),rng.randrange(2)) for _ in range(rng.randrange(1,18))])
        F=C.failures(L);deep=max(q+c for q,c in L)
        print(json.dumps({'random_list':n,'L':L,'deepest':deep,'failing_clocks':len(F),'claimed_deepest_formula':(deep-1)*(deep-2)//2 if deep>=2 else 0}),flush=True)
    for k in [4,6,8,10,12,14,20,30,40]:
        vals=[]
        for M in sorted(set([5,6,7,k//2+1,k+4])):
            C=Corner(M);w='a'*k+'s'+'A'*k+'B'+'a'+'a'*k+'S'+'A'*k+'A'+'b'
            vals.append((M,C.word_failures(w),C.word_failures(w,True)))
        print(json.dumps({'strip_depth':k,'counts_M_original_swapped':vals,'maximum':max(max(a,b) for M,a,b in vals)}),flush=True)
    print('TOTAL_SECONDS',round(time.monotonic()-start,3),flush=True)
if __name__=='__main__':main()

