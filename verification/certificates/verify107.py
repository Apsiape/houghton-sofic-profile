"""Independent 107 verifier: no builder imports; original five relators only.

Recomputes every target, checks both auxiliary and expanded lists, and derives
the substitution matrix from the lists rather than trusting archive metadata.
"""
from collections import Counter
from pathlib import Path
import gzip
import json

INV = dict(zip('aAbBxX', 'AaBbXx'))
def inv(w): return ''.join(INV[c] for c in w[::-1])
def red(w):
    stack=[]
    for c in w:
        assert c in INV
        if stack and stack[-1]==INV[c]: stack.pop()
        else: stack.append(c)
    return ''.join(stack)
def power(c,n): return c*n if n>=0 else INV[c]*(-n)
def sigma(n): return power('a',n)+'x'+power('a',-n)
def comm(u,v): return u+v+inv(u)+inv(v)
REL={'r1':'xx','r2':'xaxA'*3,'r3':comm('x',sigma(2)),
     'r4':'abABX','r5':'axAbXB'}
t,q='Ba',sigma(-2)
AUX=dict(REL,r6=comm(q,'b'))
def double(w):
    image={'a':'aa','b':'bb','x':comm('aa','bb')}
    image.update({INV[c]:inv(v) for c,v in list(image.items())})
    return ''.join(image[c] for c in w)
def formal_inverse(w): return w.swapcase()[::-1]
def substitute(w,it,iq):
    image={'t':it,'q':iq,'T':formal_inverse(it),'Q':formal_inverse(iq)}
    return ''.join(image[c] for c in w)
def letters(w): return ''.join({'t':t,'T':inv(t),'q':q,'Q':inv(q)}[c] for c in w)
DT='ttq'
DQ='TqTqttqTQt'
OT=substitute(DT,'ttqT','q')
OQ=substitute(DQ,'ttqT','q')
def normal(n):
    if n==1: return 't'
    return substitute(normal(n//2),OT,OQ)+'t' if n%2 else substitute(normal(n//2),DT,DQ)
def target(name):
    if name=='r6': return AUX['r6']
    if name.startswith('D'): return double(AUX['r'+name[1:]])
    if name.startswith('F'):
        k=int(name[1:])
        return comm('x',sigma(2)) if k==2 else comm(sigma(k),'x')
    if name.startswith('N'): return comm(sigma(-int(name[1:])),'b')
    if name.startswith('h'):
        n=int(name[1:]); return power('b',-n)+power('a',n)+inv(letters(normal(n)))
    input_word=double(t if name[1]=='t' else q)
    if name[0]=='o': input_word='B'+input_word+'b'
    output={'dt':DT,'dq':DQ,'ot':OT,'oq':OQ}[name]
    return input_word+inv(letters(output))
def verify_cells(cells,relators):
    acc=''
    for z,r,s in cells:
        assert r in relators and s in (-1,1)
        rr=relators[r] if s==1 else inv(relators[r])
        acc=red(acc+z+rr+inv(z))
    return acc
def counts(cells):
    c=Counter(r for _,r,_ in cells)
    assert not c['r2']
    return [c['r'+str(i)] for i in (1,3,4,5,6)]
def verify():
    path=Path(__file__).parent/'out/certificates107.json.gz'
    with gzip.open(path,'rt') as stream: entries=json.load(stream)['certificates']
    names=['r6','D1','D3','D4','D5','D6','dt','dq','ot','oq']
    names += ['F'+str(n) for n in range(2,7)]+['N3','N4']+['h'+str(n) for n in range(1,9)]
    assert {e['name'] for e in entries}==set(names) and len(entries)==len(names)
    for e in entries:
        expected=red(target(e['name']))
        assert e['word']==expected
        assert verify_cells(e['cells'],REL)==expected
        assert verify_cells(e['aux_cells'],AUX)==expected
        print(e['name'],len(e['cells']),'original cells: VERIFIED')
    byname={e['name']:e for e in entries}
    matrix=[counts(byname['D'+str(i)]['aux_cells']) for i in (1,3,4,5,6)]
    assert matrix==[[4,3,8,4,0],[4,72,120,104,96],[0,0,0,0,0],[2,16,36,24,12],[2,10,24,8,12]]
    weights=[25,616,1,133,78]
    dot=lambda x,y:sum(a*b for a,b in zip(x,y))
    assert all(dot(row,weights)<=107*w for row,w in zip(matrix,weights))
    assert all(w>=c for w,c in zip(weights,[1,1,1,1,9]))
    assert max(dot(counts(byname[key]['aux_cells']),weights) for key in ('dt','dq','ot','oq'))==2315
    assert 2315+29*26+29<=107*29
    # Verify the characteristic polynomial by six integer evaluations of its
    # degree-five identity; also isolate four distinct real roots exactly.
    from itertools import permutations
    def det(a):
        out=0
        for p in permutations(range(5)):
            sign=(-1)**sum(p[i]>p[j] for i in range(5) for j in range(i+1,5))
            term=sign
            for i in range(5): term*=a[i][p[i]]
            out+=term
        return out
    quartic=lambda x:x**4-112*x**3+572*x*x+3328*x-14208
    for x in range(6):
        assert det([[(x if i==j else 0)-matrix[i][j] for j in range(5)] for i in range(5)])==x*quartic(x)
    assert all(quartic(a)*quartic(b)<0 for a,b in [(-6,-5),(3,4),(7,8),(106,107)])
    print('Matrix, original-cell domination, rule costs and 107 recurrence: VERIFIED')

if __name__=='__main__': verify()
