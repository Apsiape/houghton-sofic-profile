"""Reconstruct the auxiliary-relator 107 certificates from five relators.

No missing external certificate package is consumed. Run verify107.py separately.
The r6 symbol is kept atomic during lifts and expanded only at final export.
"""
from collections import Counter
from pathlib import Path
import gzip
import json

from vk import (RELATORS, REL, Lemma, Deriv, S, inv, red, comm, psi,
                apow, bpow, conj_find, check_cert)
from lemmas_small import build_small


class Eq:
    def __init__(self, u, v, cells=()):
        self.u, self.v, self.cells = red(u), red(v), list(cells)
        assert check_cert(self.u + inv(self.v), self.cells)

    def then(self, other):
        assert self.v == other.u, (self.v, other.u)
        return Eq(self.u, other.v, self.cells + other.cells)

    def reverse(self):
        return Eq(self.v, self.u, [(z, r, -s) for z, r, s in reversed(self.cells)])

    def conjugate(self, p):
        return Eq(p + self.u + inv(p), p + self.v + inv(p),
                  [(red(p + z), r, s) for z, r, s in self.cells])

    def inverse(self):
        return Eq(inv(self.u), inv(self.v),
                  [(red(inv(self.u)+z), r, -s) for z, r, s in reversed(self.cells)])

    def mul(self, other):
        return Eq(self.u + other.u, self.v + other.v, self.cells +
                  [(red(self.v + z), r, s) for z, r, s in other.cells])


def primitive(u, v, lemma):
    if red(u) == red(v):
        return Eq(u, v)
    c, e = conj_find(u + inv(v), lemma.word)
    return Eq(u, v, [(red(c + z), r, s) for z, r, s in lemma.cells_signed(e)])


def product(eqs):
    ans = Eq('', '')
    for eq in eqs:
        ans = ans.mul(eq)
    return ans


def aslemma(name, eq):
    return Lemma(name, eq.u + inv(eq.v), eq.cells)


def commute(u, toks, lookup):
    """Fill [u, product(toks)] by explicit swaps (also supports inverse words)."""
    d = Deriv('commute', [u] + toks + [inv(u)] + [inv(w) for w in reversed(toks)])
    for j, w in enumerate(toks):
        d.apply_run(j, j + 2, [w, u], lookup(u, w))
    d.free([])
    return d.done()


def comm_eq(eq, v):
    return product([eq, Eq(v, v), eq.inverse(), Eq(inv(v), inv(v))])


def counts(cells):
    c = Counter(r for _, r, _ in cells)
    return [c['r' + str(i)] for i in (1, 3, 4, 5, 6)]


def build():
    # Independent pre-existing nine-cell derivation in the original presentation.
    r6_original = build_small()['B(2)']
    q, t = S(-2), 'Ba'
    assert r6_original.word == comm(q, 'b')
    assert Counter(r for _, r, _ in r6_original.cells) == Counter(r1=3, r2=1, r4=4, r5=1)
    RELATORS['r6'] = comm(q, 'b')
    r6 = Lemma('r6', RELATORS['r6'], [('', 'r6', 1)])
    F = {2: REL['r3']}
    J, C, N = {}, {0: Eq('x', 'x')}, {2: r6}
    all_eqs = {'r6': Eq(r6_original.word, '', r6_original.cells)}

    def farlookup(u, v):
        for candidate in F.values():
            if conj_find(comm(u, v), candidate.word):
                return candidate
        raise AssertionError(('missing far commutator', u, v))

    for j in range(4):
        BA = primitive('baB', 'Xa', REL['r4'])
        BX = primitive('bxB', S(1), REL['r5'])
        first = product([BA] * j + [BX] + [BA.inverse()] * j)
        Q = [inv(S(i)) for i in range(j)]
        d = Deriv('J', Q + [S(j+1)] + [inv(w) for w in reversed(Q)] + [inv(S(j+1))])
        for i in range(j-1, -1, -1):
            d.apply_run(i, i+2, [S(j+1), Q[i]], F[j+1-i])
        d.free([])
        J[j] = aslemma('J', first.then(Eq(first.v, S(j+1), d.done().cells)))
        C[j+1] = primitive(S(j+1), 'b' + S(j) + 'B', J[j]).then(C[j].conjugate('b'))
        m = j + 1
        converted = comm_eq(C[m], q)  # [sigma_m,q] -> [beta_m,q]
        beta = bpow(m) + 'x' + bpow(-m)
        cb = commute(q, ['b']*m + ['x'] + ['B']*m,
                     lambda u, v: F[2] if v == 'x' else r6)
        finish = primitive(comm(beta, q), '', cb)
        inverse_orientation = converted.then(finish)
        F[m+2] = aslemma('F', inverse_orientation.conjugate(apow(2)))
        # Its target has reverse commutator orientation; primitive handles that.
    for m in (3, 4):
        prev = Eq(N[m-1].word, '', N[m-1].cells).conjugate('A')
        base = commute(S(-m), [S(-1), 'Aba'],
                       lambda u,v: farlookup(u,v) if v == S(-1) else aslemma('prev', prev))
        replacement = primitive('b', S(-1)+'Aba', REL['r4'])
        eq = product([Eq(S(-m),S(-m)), replacement,
                      Eq(inv(S(-m)),inv(S(-m))), replacement.inverse()])
        N[m] = aslemma('N', eq.then(Eq(eq.v,'',base.cells)))

    T = psi('x')
    stoks = [S(1), 'x', S(2), inv(S(1))]
    sw = red(''.join(stoks))
    from lemmas_psi import lemma_CONV
    conv6 = lemma_CONV()
    tail = Deriv('conv8-tail', [S(1), S(2), 'x', S(1), inv(sw)])
    tail.apply_run(1,3,['x',S(2)],F[2])
    tail.apply_run(3,4,[inv(S(1))],REL['r1'])
    tail.free([])
    conv = Eq(T, red(S(1)+S(2)+'x'+S(1)), conv6.cells).then(Eq(tail.T, '', tail.done().cells).mul(Eq(sw,sw)))
    assert conv.v == sw and counts(conv.cells) == [1,1,4,2,0]

    def subst_eq(word, replacement):
        return product([replacement if c == 'x' else replacement.inverse() if c == 'X'
                        else Eq(psi(c),psi(c)) for c in word])

    images = {}
    for i in (1,3,4,5,6):
        e = subst_eq(RELATORS['r'+str(i)], conv)
        if i == 1:
            d = Deriv('D1', [S(1),'x',S(2),'x',S(2),inv(S(1))])
            d.apply_run(2,4,['x',S(2)],F[2])
            d.apply_run(1,3,[],REL['r1'])
            d.apply_run(1,3,[],REL['r1'])
            d.free([])
            end = Eq(e.v,'',d.done().cells)
        elif i == 3:
            toks2 = [red('aaaa'+w+'AAAA') for w in stoks]
            d = Deriv('D3', stoks+toks2+[inv(w) for w in reversed(stoks)]+[inv(w) for w in reversed(toks2)])
            for j in range(4):
                for k in range(4):
                    pos = 3 + j - k
                    u,v = d.cur[pos:pos+2]
                    d.apply_run(pos,pos+2,[v,u],farlookup(u,v))
            d.free([])
            end = Eq(e.v,'',d.done().cells)
        elif i == 4:
            # This image is free BEFORE replacing T. Do not pay for conv.
            images[i] = Eq(psi(RELATORS['r4']),'')
            continue
        elif i == 5:
            h2eq = primitive('BBaa', t+t+q, REL['r4'])
            H = {}
            for j in range(3):
                ce = comm_eq(h2eq,S(j))
                # Commute sigma_j through t,t,q, then invert orientation.
                cc = commute(S(j),[t,t,q],lambda u,v: J[j] if v==t else F[j+2])
                H[j] = aslemma('H',ce.then(primitive(ce.v,'',cc)))
            cc = commute('BBaa',stoks,lambda u,v: H[0] if v=='x' else H[2] if v==S(2) else H[1])
            end = primitive(e.v,'',cc)
        else:
            neg = [red('AAAA'+w+'aaaa') for w in stoks]
            cc = commute('b',neg,lambda u,v: N[4] if v==S(-4) else N[2] if v==q else N[3])
            cc2 = commute(''.join(neg),['b','b'],lambda u,v:cc)
            end = primitive(e.v,'',cc2)
        images[i] = e.then(end)
    matrix = [[4,3,8,4,0],[4,72,120,104,96],[0,0,0,0,0],
              [2,16,36,24,12],[2,10,24,8,12]]
    assert [counts(images[i].cells) for i in (1,3,4,5,6)] == matrix

    u1, u2 = red(inv(t)+q+t), red(inv(t)*2+q+t*2)
    neg3 = primitive(S(-3),u1,r6)
    n_u1 = comm_eq(neg3.reverse(),'b').then(Eq(N[3].word,'',N[3].cells))
    neg4 = neg3.conjugate('A').then(primitive('A'+u1+'a',u2,aslemma('n_u1',n_u1)))
    dt = primitive(psi(t),t+t+q,REL['r4'])
    dq = conv.conjugate('AAAA').then(product([neg3,neg4,Eq(q,q),neg3.inverse()]))
    et = dt.conjugate('').mul(Eq(inv(t),inv(t)))
    assert et.u == red('B'+t+'b')
    eq = primitive('B'+q+'b',q,r6)
    # Formal words use a separate alphabet, never confuse q with alpha.
    def si(w): return w.swapcase()[::-1]
    def sr(w):
        st=[]
        for c in w:
            if st and st[-1]==c.swapcase(): st.pop()
            else: st.append(c)
        return ''.join(st)
    def ss(w, it, iq):
        return sr(''.join({'t':it,'T':si(it),'q':iq,'Q':si(iq)}[c] for c in w))
    def letters(w):
        return red(''.join({'t':t,'T':inv(t),'q':q,'Q':inv(q)}[c] for c in w))
    dwords={'t':'ttq','q':sr('Tqt'+'TTqtt'+'q'+si('Tqt'))}
    rules={'dt':dt,'dq':dq}
    for c, start in [('t',dt),('q',dq)]:
        ew=product([et if z=='t' else et.inverse() if z=='T' else eq if z=='q' else eq.inverse()
                    for z in dwords[c]])
        rules['o'+c] = start.conjugate('B').then(ew)
    owords={c:ss(w,'ttqT','q') for c,w in dwords.items()}
    assert [len(dwords['t']),len(dwords['q']),len(owords['t']),len(owords['q'])]==[3,10,7,26]
    assert [counts(rules[c].cells) for c in ('dt','dq','ot','oq')]==[
        [0,0,1,0,0],[1,2,6,2,6],[0,0,3,0,1],[1,2,12,2,10]]
    all_eqs.update({'D'+str(i):images[i] for i in images})
    all_eqs.update(rules)
    for m in range(2,7): all_eqs['F'+str(m)]=Eq(F[m].word,'',F[m].cells)
    for m in (3,4): all_eqs['N'+str(m)]=Eq(N[m].word,'',N[m].cells)

    cache={1:('', 't', Eq(t,t))}
    def normal(n):
        if n in cache: return cache[n]
        _,w,prev=normal(n//2)
        cells=[]
        for z,r,s in prev.cells:
            li=aslemma('image',images[int(r[1:])])
            cells.extend((red(psi(z)+zz),rr,ss_) for zz,rr,ss_ in li.cells_signed(s))
        lifted=Eq(psi(prev.u),psi(prev.v),cells)
        odd=n%2
        if odd: lifted=lifted.conjugate('B')
        rw=product([rules[('o' if odd else 'd')+z.lower()] if z.islower()
                    else rules[('o' if odd else 'd')+z.lower()].inverse() for z in w])
        result=lifted.then(rw)
        nw=ss(w,*(owords.values() if odd else dwords.values()))
        if odd:
            result=result.mul(Eq(t,t)); nw=sr(nw+'t')
        assert result.u==red(bpow(-n)+apow(n)) and result.v==letters(nw)
        cache[n]=('',nw,result)
        return cache[n]
    for n in range(1,9): all_eqs['h'+str(n)]=normal(n)[2]

    exported=[]
    for name, e in all_eqs.items():
        expanded=[]
        for z,r,s in e.cells:
            if r=='r6':
                expanded.extend((red(z+zz),rr,ss_) for zz,rr,ss_ in r6_original.cells_signed(s))
            else: expanded.append((z,r,s))
        assert check_cert(e.u+inv(e.v),expanded)
        exported.append(dict(name=name,word=red(e.u+inv(e.v)),aux_cells=e.cells,cells=expanded))
    out=Path(__file__).parent/'out/certificates107.json.gz'
    with out.open('wb') as f:
        with gzip.GzipFile(fileobj=f,mode='wb',mtime=0,filename='') as gz:
            gz.write(json.dumps(dict(certificates=exported),separators=(',',':')).encode('ascii'))
    print('Built',len(exported),'107 certificates;',sum(len(e['cells']) for e in exported),'expanded cells.')


if __name__=='__main__': build()
