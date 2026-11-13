#!/usr/bin/env python3
"""Checker and generator for the interval certificate, 110 <= p <= 10^44.

This is the certificate of Section 5 of the note uniform_minor_bound.pdf.
The density is D = (16/5) p sqrt(ln p), and alpha_0 is replaced by 67/25.
Each line of the certificate is an interval L <= p <= U with a list of
cells.  For p in [L, U] and a reduced graph with n vertices put x = n/D.
The checker computes rho, the larger of the two lower bounds on R/D of the
note, so that every reduced graph has rho <= x <= 1.  A cell
[bn, bd, k, pn, pd] covers the x interval [a, bn/bd], where a is the right
end of the previous cell, or rho for the first cell.  It uses blocks of size
k and the penalty P = pn/pd.  The checker verifies that the cells cover
[rho, 1] and that B/p > 1 - 3/U on every cell, which gives B > p - 3.  It
also verifies that the intervals cover every integer 110 <= p <= 10^44, and
that ln(10^44) > 100, so that Section 6 of the note covers every larger p.

Usage:
    python3 global_medium_checker.py check global_medium_certificate.jsonl
    python3 global_medium_checker.py gen FILE

The check uses only Python's standard library and integer and Fraction
arithmetic, with exact bounds on logarithms and square roots.  The optional
generator uses floating point to propose cells and penalties, and checks
every proposed cell again exactly.
"""
import argparse
import functools
from fractions import Fraction as Q
import json
import math
import time

C=Q(16,5)
ALPHA=Q(67,25)
SCALE=10**12
PSCALE=10**9
XSCALE=10**9
LOG_TERMS=24

class CheckError(Exception): pass

def require(ok,msg):
    if not ok: raise CheckError(msg)

def atanh_bounds(z):
    """Lower and upper bounds for 2 atanh(z), 0 <= z < 1 (Section 5.1).

    The lower bound is the sum of the first LOG_TERMS terms of the series,
    which are positive.  The upper bound adds a geometric bound on the tail.
    """
    require(0 <= z < 1,'atanh argument')
    z2=z*z
    term=z
    lower=Q(0)
    for j in range(LOG_TERMS):
        lower += 2*term/(2*j+1)
        term *= z2
    upper=lower+2*term/((2*LOG_TERMS+1)*(1-z2))
    return lower,upper

LOG2=atanh_bounds(Q(1,3))

@functools.lru_cache(maxsize=None)
def log_bounds(n):
    """Bounds for ln(n) = m ln(2) + 2 atanh(z), m = bit_length(n) - 1."""
    require(isinstance(n,int) and n>=1,'integer log argument')
    m=n.bit_length()-1
    a,b=atanh_bounds(Q(n-(1<<m),n+(1<<m)))
    return m*LOG2[0]+a,m*LOG2[1]+b

@functools.lru_cache(maxsize=None)
def sqrtlog_bounds(n):
    """Rationals s- <= sqrt(ln n) < s+ with denominator SCALE, by integer square roots."""
    lo,hi=log_bounds(n)
    lowint=math.isqrt(lo.numerator*SCALE*SCALE//lo.denominator)
    highint=math.isqrt(hi.numerator*SCALE*SCALE//hi.denominator)+1
    return Q(lowint,SCALE),Q(highint,SCALE)

def parameters(L,U):
    """s_L, s_U and rho for the interval [L, U]."""
    sl=sqrtlog_bounds(L)[0]
    su=sqrtlog_bounds(U)[1]
    Dlow=C*L*sl
    rho=1/ALPHA-(1/ALPHA+2)/Dlow
    clow=(Dlow.numerator+Dlow.denominator-1)//Dlow.denominator-1
    rlow=(clow*25)//67-1
    rho=max(rho,Q(rlow)/(C*U*su))
    require(rho>0,'positive rho')
    return sl,su,rho

def exact_cell(L,U,a,b,k,penalty,pars=None):
    """Check one cell exactly, and return its lower bound for B/p."""
    require(isinstance(L,int) and isinstance(U,int) and 51<=L<=U,'p interval')
    require(isinstance(k,int) and k>=2,'block size')
    sl,su,rho=parameters(L,U) if pars is None else pars
    require(rho<=a<b<=1,'x interval')
    nl=C*L*sl*a
    nu=C*U*su*b
    require(nl>k and nl/k>=2,'block count')
    pi=(1-rho/b)/2
    require(0<=pi<Q(1,2),'nonneighbor proportion')
    F=(2**(k-1)-1)*(pi/(1-Q(k-1)/nl))**(k-1)
    power=(1+Q(1,k))**(k+1)*(nu/2)*(nl/(nl-k))**k*pi**(k*k)
    require(penalty>=0 and penalty**(k+1)>=power,'penalty power bound')
    require(F+penalty<1,'positive surviving fraction')
    lower=(C*sl*a/k-Q(1,L))*(1-F-penalty)
    require(lower>1-Q(3,U),'not enough branch sets')
    return lower

# The generator: floating point proposals, each checked exactly afterwards.

def float_cell(L,U,a,b,k,pars):
    sl,su,rho=pars
    nl=float(C)*L*sl*a
    nu=float(C)*U*su*b
    if nl<=k: return -math.inf,math.inf
    pi=(1-rho/b)/2
    if pi<0: pi=0
    F=(2**(k-1)-1)*(pi/(1-(k-1)/nl))**(k-1)
    if pi==0:
        pen=0.
    else:
        exponent=(math.log(nu/2)+k*math.log(nl/(nl-k))+k*k*math.log(pi))/(k+1)
        pen=(1+1/k)*math.exp(exponent)
    return (float(C)*sl*a/k-1/L)*(1-F-pen),pen

def build_interval(L,U,maxcells=1000,goal=None):
    if goal is None: goal=1-3/U+0.000001
    pars=parameters(L,U)
    fp=tuple(map(float,pars))
    a=pars[2]
    cells=[]
    minlower=math.inf
    maxk=max(12,math.ceil(2*float(pars[1])+8))
    for _ in range(maxcells):
        af=float(a)
        bestb,bestk=af,None
        for k in range(2,maxk+1):
            value,_=float_cell(L,U,af,af,k,fp)
            if value<=goal: continue
            lo=af;hi=1.
            if float_cell(L,U,af,hi,k,fp)[0]>goal:
                lo=hi
            else:
                for _ in range(42):
                    mid=(lo+hi)/2
                    if float_cell(L,U,af,mid,k,fp)[0]>goal: lo=mid
                    else: hi=mid
            if lo>bestb:bestb,bestk=lo,k
        if bestk is None or bestb-af<2/XSCALE: return None
        b=Q(1) if bestb==1 else Q(math.floor(bestb*XSCALE)-1,XSCALE)
        value,pen=float_cell(L,U,af,float(b),bestk,fp)
        penalty=Q(math.ceil(pen*PSCALE)+1,PSCALE)
        try:
            lower=exact_cell(L,U,a,b,bestk,penalty,pars)
        except CheckError:
            return None
        minlower=min(minlower,float(lower))
        cells.append([b.numerator,b.denominator,bestk,penalty.numerator,penalty.denominator])
        if b==1:
            return {'L':L,'U':U,'cells':cells},minlower
        a=b
    return None

def generate(start,end,path):
    L=start
    width=0.1
    count=0
    nrect=0
    t0=time.monotonic()
    with open(path,'w') as out:
        while L<=end:
            U=min(end,int(L*math.exp(width)))
            if U<L:U=L
            result=build_interval(L,U)
            if result is None:
                width/=2
                require(width>1e-8,'could not certify near p='+str(L))
                continue
            cert,lower=result
            out.write(json.dumps(cert,separators=(',',':'))+'\n');out.flush()
            count+=1;nrect+=len(cert['cells'])
            print(f'interval {count}: p=[{L},{U}], cells={len(cert["cells"])}, logwidth={width:.4g}, lower={lower:.9f}, elapsed={time.monotonic()-t0:.1f}s',flush=True)
            L=U+1
            width=min(2.,width*1.15)
    print(f'generated {count} p intervals, {nrect} cells; {path}',flush=True)

def check(path,start=110,end=10**44):
    nxt=start
    ncert=0;nrect=0
    minlower=None
    minmargin=None
    t0=time.monotonic()
    with open(path) as inp:
        for line in inp:
            cert=json.loads(line)
            L,U=cert['L'],cert['U']
            require(L==nxt,'p coverage gap or overlap')
            require(isinstance(U,int) and U>=L,'p endpoint')
            pars=parameters(L,U)
            a=pars[2]
            for c in cert['cells']:
                require(len(c)==5 and all(isinstance(v,int) for v in c),'cell encoding')
                bn,bd,k,pn,pd=c
                require(bd>0 and pd>0,'positive denominator')
                b=Q(bn,bd);penalty=Q(pn,pd)
                lower=exact_cell(L,U,a,b,k,penalty,pars)
                if minlower is None or lower<minlower:minlower=lower
                margin=lower-(1-Q(3,U))
                if minmargin is None or margin<minmargin:minmargin=margin
                a=b;nrect+=1
            require(a==1,'x coverage incomplete')
            nxt=U+1;ncert+=1
    require(nxt==end+1,'p coverage endpoint')
    require(log_bounds(end)[0]>100,'no overlap with analytic tail')
    print(f'PASS: {ncert} p intervals; {nrect} cells; all integers {start} <= p <= {end}.',flush=True)
    print(f'Minimum certified margin for B/p-(1-3/U): {float(minmargin):.12g}; elapsed {time.monotonic()-t0:.1f}s.',flush=True)

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__,formatter_class=argparse.RawDescriptionHelpFormatter)
    sub=ap.add_subparsers(dest='cmd',required=True)
    g=sub.add_parser('gen');g.add_argument('file');g.add_argument('--start',type=int,default=110);g.add_argument('--end',type=int,default=10**44)
    v=sub.add_parser('check');v.add_argument('file');v.add_argument('--start',type=int,default=110);v.add_argument('--end',type=int,default=10**44)
    args=ap.parse_args()
    if args.cmd=='gen':generate(args.start,args.end,args.file)
    else:check(args.file,args.start,args.end)
