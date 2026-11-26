#!/usr/bin/env python3
"""All-Boolean-board primal AND dual certificates, independent of the paper's constructions.
HiGHS only locates coefficients: integer arithmetic certifies both feasible witnesses.
S_m x S_n symmetry is used (averaging preserves the cost). Entries N[a,c] count
boards in orbit a satisfying representative c. The orbit-total primal weights x
therefore obey N x = |a|, cost sum |x|; dual y requires |N.T y| <= 1 and scores
sum |a| y_a. Matching rational objectives prove the tiny LP values exactly.
"""
import math,itertools,json
from fractions import Fraction as F
from collections import Counter
import numpy as np
from scipy.linalg import qr
from sympy import Matrix
from scipy.optimize import linprog
from scipy.sparse import csr_array,hstack
def ints(v):
    f=[F(float(x)).limit_denominator(10**6) for x in v]
    L=math.lcm(*(x.denominator for x in f))
    return [int(z*L) for z in f],L
def solve(m,n,partial=False):
    d=1<<n; full=(1<<(m*n))-1;perms=list(itertools.permutations(range(n)))
    bit={p:{z:sum(((z>>i)&1)<<p[i] for i in range(n)) for z in range(d)} for p in perms}
    def norm(rows): return min(tuple(sorted((bit[p][x],bit[p][y]) for x,y in rows)) for p in perms)
    boards=np.arange(full+1); all_rows=[tuple(((i>>(n*r))%(1<<n),0) for r in range(m)) for i in boards.tolist()]
    ok=[z for z,rows in zip(boards,all_rows) if not partial or (all(x.bit_count()<=1 for x,y in rows) and all(sum((x>>j)&1 for x,y in rows)<=1 for j in range(n)))]
    boards=np.asarray(ok);classes={};group=[]
    for z in boards:
        c=norm(all_rows[z]);group.append(classes.setdefault(c,len(classes)))
    group=np.array(group);count=np.bincount(group); types=[(x,y) for x in range(d) for y in range(d) if not x&y]
    cols={}
    for rows in itertools.combinations_with_replacement(types,m):
        plain=any(y==d-1 for x,y in rows) or any(sum((x>>j)&1 for x,y in rows)>1 for j in range(n))
        functional=any(x.bit_count()>1 for x,y in rows)
        if not (plain or functional):continue
        c=norm(rows)
        if c in cols:continue
        x=sum(w<<(r*n) for r,(w,v) in enumerate(c));y=sum(v<<(r*n) for r,(w,v) in enumerate(c))
        hit=group[((boards&x)==x)&((boards&y)==0)]
        if len(hit):cols[c]=(plain,np.bincount(hit,minlength=len(count)))
    answers={}
    for tag in ['plain','functional']:
        L=[v for plain,v in cols.values() if plain or tag=='functional']; N=np.asarray(L,dtype=int).T; H=csr_array(N)
        r=linprog(np.ones(N.shape[1]*2),A_eq=hstack([H,-H]),b_eq=count,method='highs')
        assert r.success,r.message
        x,D=ints(r.x[:N.shape[1]]-r.x[N.shape[1]:]); y,E=ints(r.eqlin.marginals)
        # Use python integers (no overflow) and check every board and every weakening orbit.
        Nx=N.astype(object)
        if list(Nx@x)!=[D*int(t) for t in count]:
            sf=np.flatnonzero(np.abs(r.x[:N.shape[1]]-r.x[N.shape[1]:])>1e-7);V=N[:,sf];q,rr,pm=qr(V.T.astype(float),mode='economic',pivoting=True); row=pm[:len(sf)]
            sol=Matrix(V[row].tolist()).inv()*Matrix([int(count[j]) for j in row])
            D=math.lcm(*(int(f.q) for f in sol));x=[0]*N.shape[1]
            for k,t in zip(sf,sol):x[k]=int(t*D)
        assert list(Nx@x)==[D*int(t) for t in count]
        if not all(abs(t)<=E for t in Nx.T@y):
            vals=r.eqlin.marginals;sf=np.flatnonzero(np.abs(vals)>1e-9)
            charged=N.T@vals; tight=np.flatnonzero(np.abs(np.abs(charged)-1)<2e-8)
            V=N[np.ix_(sf,tight)];q,rr,pm=qr(V.astype(float),mode='economic',pivoting=True); row=pm[:len(sf)]
            sol=Matrix(V[:,row].T.tolist()).inv()*Matrix([1 if charged[tight[j]]>0 else -1 for j in row])
            E=math.lcm(*(int(f.q) for f in sol));y=[0]*len(count)
            for k,t in zip(sf,sol):y[k]=int(t*E)
        assert all(abs(t)<=E for t in Nx.T@y),(m,n,partial,tag)
        cost=F(sum(map(abs,x)),D); lower=F(sum(u*int(t) for u,t in zip(y,count)),E)
        assert cost==lower
        answers[tag]=dict(exact=str(cost),primal_nonzero=sum(k!=0 for k in x),dual_nonzero=sum(k!=0 for k in y),cube_orbits=N.shape[1])
    if partial: assert answers['plain']['exact']==answers['functional']['exact']
    else:assert F(answers['plain']['exact'])>=F(answers['functional']['exact'])>=n*n
    return dict(m=m,n=n,partial=partial,concrete_boards=len(boards),board_orbits=len(count),values=answers)
if __name__=='__main__':
    out=[solve(m,n,partial) for m,n in [(2,1),(3,1),(4,1),(3,2),(4,2),(5,2),(6,2),(4,3),(5,3)] for partial in ((False,True) if (m,n)!=(5,3) else (True,))]
    for z in out:
        m,n=z['m'],z['n']
        if z['partial'] and (m>=n+2 or n>=4):
            expected=F(sum(math.comb(m,j) for j in range(n+1)),math.comb(m-1,n))
            assert expected==F(z['values']['plain']['exact'])
    print(json.dumps(out,indent=2))
