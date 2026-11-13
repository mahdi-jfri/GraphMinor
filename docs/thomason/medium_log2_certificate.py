#!/usr/bin/env python3
"""Interval certificate in base 2 for 110 <= p <= 10^44, as checked by Lean.

The Lean formalization uses this certificate, not
global_medium_certificate.jsonl, for 110 <= p <= 10^44 (see Section 8 of the
note uniform_minor_bound.pdf).  It follows the method of
global_medium_checker.py (Section 5 of the note), but for the density
D = 2.68 p sqrt(log2 p) of Graph Minors XIII (5.5) itself, in place of
(16/5) p sqrt(ln p).  The bounds on logarithms are then integer power
comparisons:
    2^aL <= L^BL  gives  log2 L >= aL/BL,
    U^BU <= 2^aU  gives  log2 U <= aU/BU,
and sL, sU are rationals with sL^2 <= aL/BL and sU^2 >= aU/BU.

For p in [L,U] put x = n/D.  With c = floor(D) and R = floor(25c/67) - 1,
we have R >= D (25/67 - 159/(67 D)), because c > D - 1.  Since
D >= (67/25) L sL, this gives R >= rho D whenever
    rho <= 25/67 - 3975/(4489 L sL).
A cell [a,b] of x carries a block size k, a penalty P and a bound
pi >= (1 - rho/b)/2 on the proportion of nonneighbors.  With C = 67/25,
    nlo = C L sL a,  nhi = C U sU b,
    F   = (2^(k-1)-1) (pi nlo/(nlo-k+1))^(k-1),
    H   = ((k+1)/k)^(k+1) (nhi/2) (nlo/(nlo-k))^k pi^(k^2),
the cell is accepted when nlo > k, H <= P^(k+1), F + P < 1 and
    (C sL a/k - 1/L) (1 - F - P) > 1 - 3/U.
Lean uses blocks of size k and A = (k+1)/(k P) in the random block lemma.
The Lean theorem `GraphMinor.Thomason.Uniform.cell_bound_of_cellOK` proves
that an accepted cell gives B > p - 3, and the Lean function `intervalOK`
repeats the checks of `check_interval` below with denominators cleared.
The script gen_lean_medium.py writes the Lean data modules.

Usage:
    python3 medium_log2_certificate.py check medium_log2_certificate.jsonl
    python3 medium_log2_certificate.py gen FILE

The check uses only integer and Fraction arithmetic.  The generator uses
floating point to propose cells, and checks every proposed cell again
exactly.
"""
import argparse, json, math, sys, time
from fractions import Fraction as Q

C = Q(67, 25)
BL = BU = 1000
SS = 10**12
XSCALE = 10**9
PSCALE = 10**9
PISCALE = 10**12
RSCALE = 10**12

class CheckError(Exception): pass
def require(ok, msg):
    if not ok: raise CheckError(msg)

def log2_lower_num(L):
    return (L**BL).bit_length() - 1          # 2^a <= L^BL

def log2_upper_num(U):
    return (U**BU - 1).bit_length()          # U^BU <= 2^a

def parameters(L, U):
    aL = log2_lower_num(L); aU = log2_upper_num(U)
    sL = Q(math.isqrt(aL * SS * SS // BL), SS)
    sU = Q(math.isqrt(aU * SS * SS // BU) + 1, SS)
    rho_true = Q(25, 67) - Q(3975, 4489) / (L * sL)
    rho = Q(math.floor(rho_true * RSCALE), RSCALE)
    return aL, aU, sL, sU, rho

def cell_quantities(L, U, sL, sU, a, b, k, pi):
    nlo = C * L * sL * a
    nhi = C * U * sU * b
    F = (2**(k-1) - 1) * (pi * nlo / (nlo - k + 1))**(k-1)
    H = Q(k+1, k)**(k+1) * (nhi / 2) * (nlo / (nlo - k))**k * pi**(k*k)
    return nlo, nhi, F, H

def check_cell(L, U, sL, sU, rho, a, b, k, P, pi):
    require(k >= 1, 'k')
    require(rho <= a < b <= 1, 'x interval')
    require(2 * pi * b >= b - rho, 'pi bound')
    require(pi >= 0 and P >= 0, 'signs')
    nlo, nhi, F, H = cell_quantities(L, U, sL, sU, a, b, k, pi)
    require(nlo > k, 'nlo > k')
    require(H <= P**(k+1), 'penalty')
    require(F + P < 1, 'positive fraction')
    lower = (C * sL * a / k - Q(1, L)) * (1 - F - P)
    require(lower > 1 - Q(3, U), 'not enough blocks')
    return lower - (1 - Q(3, U))

def check_interval(cert):
    L, U = cert['L'], cert['U']
    require(110 <= L <= U, 'interval')
    aL, aU, sL, sU, rho = parameters(L, U)
    require(Q(cert['sL'][0], cert['sL'][1]) == sL and Q(cert['sU'][0], cert['sU'][1]) == sU, 's')
    require(Q(cert['rho'][0], cert['rho'][1]) == rho and cert['aL'] == aL and cert['aU'] == aU, 'rho')
    require(2**aL <= L**BL and U**BU <= 2**aU, 'log2 bounds')
    require(sL > 0 and sL * sL * BL <= aL and sU * sU * BU >= aU, 'square roots')
    require(0 < rho < 1 and rho <= Q(25, 67) - Q(3975, 4489) / (L * sL), 'rho')
    a = rho; m = None
    for (bn, bd, k, pn, pd, qn, qd) in cert['cells']:
        b = Q(bn, bd)
        mm = check_cell(L, U, sL, sU, rho, a, b, k, Q(pn, pd), Q(qn, qd))
        m = mm if m is None else min(m, mm)
        a = b
    require(a == 1, 'x coverage')
    return m

def float_cell(L, U, sL, sU, rho, a, b, k):
    nlo = float(C) * L * sL * a; nhi = float(C) * U * sU * b
    if nlo <= k + 1: return -math.inf, 0., 0.
    pi = max(0., (1 - rho / b) / 2)
    F = (2**(k-1) - 1) * (pi * nlo / (nlo - k + 1))**(k-1)
    if pi == 0: pen = 0.
    else:
        e = (math.log(nhi / 2) + k * math.log(nlo / (nlo - k)) + k * k * math.log(pi)) / (k + 1)
        pen = (1 + 1 / k) * math.exp(e)
    return (float(C) * sL * a / k - 1 / L) * (1 - F - pen), pen, pi

def build_interval(L, U, maxcells=2000):
    aL, aU, sL, sU, rho = parameters(L, U)
    fs = (float(sL), float(sU), float(rho))
    goal = 1 - 3 / U + 1e-7
    a = rho; cells = []; m = None
    maxk = max(12, math.ceil(2 * math.sqrt(math.log2(U)) + 8))
    for _ in range(maxcells):
        af = float(a); bestb, bestk = af, None
        for k in range(2, maxk + 1):
            if float_cell(L, U, *fs, af, af * (1 + 1e-12), k)[0] <= goal: continue
            lo, hi = af, 1.
            if float_cell(L, U, *fs, af, hi, k)[0] > goal: lo = hi
            else:
                for _ in range(42):
                    mid = (lo + hi) / 2
                    if float_cell(L, U, *fs, af, mid, k)[0] > goal: lo = mid
                    else: hi = mid
            if lo > bestb: bestb, bestk = lo, k
        if bestk is None or bestb - af < 2 / XSCALE: return None
        b = Q(1) if bestb == 1 else Q(math.floor(bestb * XSCALE) - 1, XSCALE)
        _, pen, pif = float_cell(L, U, *fs, af, float(b), bestk)
        pi = Q(math.ceil(max(0, (1 - rho / b) / 2) * PISCALE), PISCALE)
        P = Q(math.ceil(pen * PSCALE) + 1, PSCALE)
        try:
            mm = check_cell(L, U, sL, sU, rho, a, b, bestk, P, pi)
        except CheckError:
            return None
        cells.append([b.numerator, b.denominator, bestk, P.numerator, P.denominator,
                      pi.numerator, pi.denominator])
        m = mm if m is None else min(m, mm)
        if b == 1:
            return {'L': L, 'U': U, 'aL': aL, 'aU': aU,
                    'sL': [sL.numerator, sL.denominator], 'sU': [sU.numerator, sU.denominator],
                    'rho': [rho.numerator, rho.denominator], 'cells': cells}, m
        a = b
    return None

def generate(path, start=110, end=10**44):
    L = start; width = 0.1; t0 = time.monotonic(); n = 0; nc = 0
    with open(path, 'w') as out:
        while L <= end:
            U = min(end, max(L, int(L * math.exp(width))))
            r = build_interval(L, U)
            if r is None:
                width /= 2
                require(width > 1e-9, f'stuck at {L}')
                continue
            cert, m = r
            out.write(json.dumps(cert, separators=(',', ':')) + '\n'); out.flush()
            n += 1; nc += len(cert['cells'])
            print(f'{n}: [{L},{U}] cells={len(cert["cells"])} width={width:.3g} margin={float(m):.3g} t={time.monotonic()-t0:.0f}s', flush=True)
            L = U + 1; width = min(2., width * 1.15)
    print(f'generated {n} intervals, {nc} cells')

def check(path, start=110, end=10**44):
    nxt = start; n = 0; nc = 0; mm = None
    for line in open(path):
        cert = json.loads(line)
        require(cert['L'] == nxt, 'p coverage')
        m = check_interval(cert)
        mm = m if mm is None else min(mm, m)
        nxt = cert['U'] + 1; n += 1; nc += len(cert['cells'])
    require(nxt == end + 1, 'endpoint')
    print(f'PASS: {n} intervals, {nc} cells, {start} <= p <= {end}; min margin {float(mm):.3g}')

if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('cmd', choices=['gen', 'check']); ap.add_argument('file')
    args = ap.parse_args()
    (generate if args.cmd == 'gen' else check)(args.file)
