#!/usr/bin/env python3
"""Checker and generator for the finite certificate, 51 <= p <= 109.

This is the certificate of Section 4 of the note uniform_minor_bound.pdf.
Each line of the certificate is one row for one value of p.  It gives an
integer density c and one choice of blocks for each order n = R+2, ..., c of
a reduced graph, where R = floor(25c/67) - 1.  A choice of blocks is either

    ["u", k, an, ad]                    blocks of size k with A = an/ad
                                        (Lemma 1 of the note), or
    ["m", N2, N3, a2n, a2d, a3n, a3d]   N2 pairs and N3 triples with
                                        A2 = a2n/a2d and A3 = a3n/a3d
                                        (Lemma 2 of the note).

The check verifies c^2 < (16/5)^2 p^2 l_p for a rational lower bound l_p on
ln p, verifies R >= p - 2, and evaluates the bound B of Lemma 1 or Lemma 2
with q = floor((n - R)/2) and verifies B > p - 3.  It uses only Python's
standard library and integer and Fraction arithmetic.

Usage:
    python3 global_finite_checker.py check global_finite_certificate.jsonl
    python3 global_finite_checker.py gen FILE

The optional generator uses floating point to propose the choices of
blocks, and checks every proposed choice again exactly.  The printed
decimal values are diagnostics only and are not used to accept a row.
"""
import argparse
from fractions import Fraction as Q
from functools import lru_cache
import json
import math
import time

C=Q(16,5)
SCALE=10**6

class CheckError(Exception): pass

def require(ok,msg):
    if not ok: raise CheckError(msg)

def log_lower(p):
    """Rational lower bound on ln(p) from the atanh series (Section 5.1).

    With m = bit_length(p) - 1, ln(p) = m ln(2) + 2 atanh(z) for
    z = (p - 2^m)/(p + 2^m), and ln(2) = 2 atanh(1/3).  The first 24 terms of
    each series have positive terms and give a lower bound.
    """
    require(isinstance(p,int) and p>=1,'log argument')
    m=p.bit_length()-1
    def series(z):
        z2=z*z;term=z;out=Q(0)
        for j in range(24):
            out+=2*term/(2*j+1);term*=z2
        return out
    return m*series(Q(1,3))+series(Q(p-(1<<m),p+(1<<m)))

@lru_cache(maxsize=None)
def threshold_ok(p,c):
    """Check c < (16/5) p sqrt(ln p) and R >= p - 2, and return R."""
    require(isinstance(p,int) and 51<=p<=109,'p range')
    require(isinstance(c,int) and c>0,'integer density')
    require(c*c<C*C*p*p*log_lower(p),'density exceeds target')
    R=(25*c)//67-1
    require(R>=p-2,'complete graphs too small')
    return R

def exact_bound(n,q,entry):
    """The bound B of Lemma 1 or Lemma 2 of the note, as an exact fraction."""
    require(isinstance(n,int) and isinstance(q,int) and n>0 and 0<q<n,'graph parameters')
    pi=Q(q,n)
    if entry[0]=='u':
        require(len(entry)==4,'uniform encoding')
        k,an,ad=entry[1:]
        require(all(isinstance(x,int) for x in entry[1:]) and ad>0 and an>0,'uniform integers')
        require(2<=k<n,'uniform k')
        N=n//k;A=Q(an,ad)
        require(N>=2,'uniform block count')
        F=(2**(k-1)-1)*Q(q,n-k+1)**(k-1)
        M=Q(N*(N-1),2)*(A*Q(n,n-k))**k*pi**(k*k)
        return N*(1-F-1/A)-M
    require(entry[0]=='m' and len(entry)==7,'mixed encoding')
    N2,N3,a2n,a2d,a3n,a3d=entry[1:]
    require(all(isinstance(x,int) for x in entry[1:]),'mixed integers')
    require(N2>=1 and N3>=1 and 2*N2+3*N3<=n,'mixed block count')
    require(min(a2n,a2d,a3n,a3d)>0,'mixed domination factors')
    A2=Q(a2n,a2d);A3=Q(a3n,a3d)
    F2=Q(q,n-1);F3=3*Q(q,n-2)**2
    M22=Q(N2*(N2-1),2)*(A2*Q(n,n-2))**2*pi**4
    M23=N2*N3*(A2*Q(n,n-2))**3*pi**6
    M33=Q(N3*(N3-1),2)*(A3*Q(n,n-3))**3*pi**9
    return N2*(1-F2-1/A2)+N3*(1-F3-1/A3)-M22-M23-M33

# The generator: floating point proposals, each checked exactly afterwards.

def float_uniform(n,q,k):
    N=n//k
    if N<2:return -math.inf,None
    pi=q/n
    F=(2**(k-1)-1)*(q/(n-k+1))**(k-1)
    logc=math.log(N*(N-1)/2)+k*math.log(n/(n-k))+k*k*math.log(pi)
    A=math.exp((math.log(N/k)-logc)/(k+1))
    val=N*(1-F)-(1+1/k)*N/A
    return val,['u',k,max(1,round(A*SCALE)),SCALE]

def float_mixed(n,q,N2):
    N3=(n-2*N2)//3
    if N2<=0 or N3<=0:return -math.inf,None
    pi=q/n
    F2=q/(n-1);F3=3*(q/(n-2))**2
    a22=N2*(N2-1)/2*(n/(n-2))**2*pi**4
    a23=N2*N3*(n/(n-2))**3*pi**6
    a33=N3*(N3-1)/2*(n/(n-3))**3*pi**9
    A3=(N3/(3*a33))**.25 if a33 else 1e8
    lo=0.;hi=1.
    while 2*a22*hi**3+3*a23*hi**4<N2:hi*=2
    for _ in range(40):
        A=(lo+hi)/2
        if 2*a22*A**3+3*a23*A**4<N2:lo=A
        else:hi=A
    A2=(lo+hi)/2
    val=N2*(1-F2-1/A2)+N3*(1-F3-1/A3)-a22*A2**2-a23*A2**3-a33*A3**3
    return val,['m',N2,N3,max(1,round(A2*SCALE)),SCALE,max(1,round(A3*SCALE)),SCALE]

def generate(path):
    t0=time.monotonic();count=0;mix=0;minmargin=None
    with open(path,'w') as out:
        for p in range(51,110):
            c=math.ceil(float(C)*p*math.sqrt(math.log(p)))-1
            R=threshold_ok(p,c)
            entries=[]
            for n in range(R+2,c+1):
                q=(n-R)//2
                best,entry=max((float_uniform(n,q,k) for k in range(2,9)),key=lambda z:z[0])
                if best<=p-3+0.1:
                    for j in range(1,20):
                        val,ent=float_mixed(n,q,(j*n)//40)
                        if val>best:best,entry=val,ent
                exact=exact_bound(n,q,entry)
                require(exact>p-3,f'failed p={p}, n={n}, bound={float(exact)}')
                margin=exact-(p-3)
                if minmargin is None or margin<minmargin:minmargin=margin
                count+=1;mix+=entry[0]=='m';entries.append(entry)
            out.write(json.dumps({'p':p,'c':c,'entries':entries},separators=(',',':'))+'\n')
            out.flush()
            if p%10==0 or p in [51,109]:print(f'p={p}: {count} cases, {mix} mixed, elapsed {time.monotonic()-t0:.2f}s',flush=True)
    require(minmargin>Q(1,10),'margin less than certified summary')
    print(f'GENERATED {count} cases ({mix} mixed); minimum margin > 1/10; {path}',flush=True)

def check(path):
    t0=time.monotonic();expected=51;count=0;mix=0;minmargin=None
    with open(path) as inp:
        for line in inp:
            cert=json.loads(line)
            p,c,entries=cert['p'],cert['c'],cert['entries']
            require(p==expected,'p coverage')
            R=threshold_ok(p,c)
            require(isinstance(entries,list) and len(entries)==c-R-1,'n coverage')
            for n,entry in zip(range(R+2,c+1),entries):
                q=(n-R)//2
                B=exact_bound(n,q,entry)
                require(B>p-3,f'not enough branches at p={p}, n={n}')
                margin=B-(p-3)
                if minmargin is None or margin<minmargin:minmargin=margin
                count+=1;mix+=entry[0]=='m'
            expected+=1
    require(expected==110,'p endpoint')
    print(f'PASS: all integers 51 <= p <= 109; {count} cases (p, n), {mix} of them with pairs and triples.',flush=True)
    require(minmargin>Q(1,10),'margin less than certified summary')
    print(f'Minimum B-(p-3) > 1/10 (approximately {float(minmargin):.12g}); elapsed {time.monotonic()-t0:.2f}s.',flush=True)

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__,formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('command',choices=['gen','check']);ap.add_argument('file')
    args=ap.parse_args()
    (generate if args.command=='gen' else check)(args.file)
