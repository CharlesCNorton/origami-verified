"""Search for a rational tangent-tangent witness whose degree-10 elimination
polynomial certifies Galois group S10: irreducible by a single-prime pattern,
eight real roots plus one conjugate pair, and a degree-45 squared-difference
resolvent whose factor patterns over two primes jointly exclude degrees 1..44."""
import sys, json, random
import sympy as sp

v, w, x, T, U = sp.symbols('v w x T U')

def reflect(Q, A, B, C):
    d = A*A + B*B; f = (A*Q[0] + B*Q[1] + C)
    return (Q[0]*d - 2*A*f, Q[1]*d - 2*B*f, d)

def onto(recv, Q, send):
    X, Y, D = reflect(Q, *send)
    return sp.expand(recv[0]*X + recv[1]*Y + recv[2]*D)

def sf_pat(P, p, var):
    try:
        Pm = sp.Poly(P, var, modulus=p)
        if Pm.degree() != sp.Poly(P, var).degree(): return None
        if sp.gcd(Pm, Pm.diff(var)).degree() != 0: return None
        fl = sp.factor_list(P, var, modulus=p)
        return tuple(sorted(sp.Poly(g, var).degree() for g, m in fl[1] for _ in range(m)))
    except Exception:
        return None

def sums(pattern):
    S = {0}
    for part in pattern:
        S |= {a + part for a in S}
    return S

def tangent_crease(P, X, L, t):
    xx = X[0] + L[1]*t; yy = X[1] - L[0]*t
    return (2*(xx - P[0]), 2*(yy - P[1]), P[0]**2 + P[1]**2 - xx**2 - yy**2)

def run(seed_lo, seed_hi):
    lead_bound = int(sys.argv[3]) if len(sys.argv) > 3 else 10**8
    for seed in range(seed_lo, seed_hi):
        random.seed(seed)
        def rnd(): return sp.Rational(random.randint(-6, 6), 1)
        P1 = (rnd(), rnd()); X1 = (rnd(), rnd()); L1 = (rnd(), rnd()); Q1 = (rnd(), rnd())
        P2 = (rnd(), rnd()); X2 = (rnd(), rnd()); L2 = (rnd(), rnd()); Q2 = (rnd(), rnd())
        g1 = tangent_crease(P1, X1, L1, v)
        g2 = tangent_crease(P2, X2, L2, w)
        E1 = onto(g2, Q1, g1); E2 = onto(g1, Q2, g2)
        try:
            Rs = sp.resultant(sp.Poly(E1, w), sp.Poly(E2, w), w)
        except Exception:
            continue
        if Rs == 0: continue
        for f0, mm in sp.factor_list(sp.expand(Rs), v)[1]:
            pf = sp.Poly(f0, v)
            if pf.degree() != 10: continue
            lead = pf.LC()
            if abs(lead) > lead_bound:
                print(f"  seed {seed}: deg-10 factor, lead {lead} too big", flush=True)
                continue
            cs = pf.all_coeffs()
            Fm = sp.Poly([1] + [cs[k]*lead**(k-1) for k in range(1, 11)], x)
            # gate 1: a prime where the decic is irreducible
            p10 = None
            for p in (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71):
                if sf_pat(Fm.as_expr(), p, x) == (10,):
                    p10 = p; break
            if p10 is None: continue
            # gate 2: exactly eight real roots
            if Fm.count_roots() != 8: continue
            print(f"seed {seed}: decic irred mod {p10}, 8 real roots; resolvent...", flush=True)
            # gate 3: squared-difference resolvent
            D = sp.Poly(sp.resultant(Fm.as_expr(), Fm.as_expr().subs(x, x - T), x), T)
            q, r = sp.div(D.as_expr(), T**10, T)
            if sp.expand(r) != 0: continue
            Q90 = sp.Poly(sp.expand(q), T)
            odd = [c for m, c in zip(Q90.monoms(), Q90.coeffs()) if m[0] % 2 == 1]
            if any(c != 0 for c in odd): continue
            S45 = sp.Poly(Q90.as_expr().subs(T, sp.sqrt(U)), U)
            need = set(range(1, 45))
            got = {}
            excl = set(need)
            for p in (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113):
                pat = sf_pat(S45.as_expr(), p, U)
                if pat is None: continue
                ex = need - sums(pat)
                if ex - (need - excl) and len(got) < 6:
                    pass
                got[p] = pat
                excl = excl - (need - ex) if False else excl
            # joint cover: greedy over collected patterns
            remaining = set(need)
            chosen = []
            for p, pat in sorted(got.items(), key=lambda kv: -len(need - sums(kv[1]))):
                ex = need - sums(pat)
                if ex & remaining:
                    chosen.append((p, pat))
                    remaining -= ex
                if not remaining: break
            if remaining:
                print(f"  seed {seed}: resolvent cover FAILED, remaining {sorted(remaining)}", flush=True)
                continue
            out = {
                "seed": seed,
                "instance": {k: [str(a) for a in val] for k, val in
                             dict(P1=P1, X1=X1, L1=L1, Q1=Q1, P2=P2, X2=X2, L2=L2, Q2=Q2).items()},
                "decic_coeffs_leading_first": [str(c) for c in cs],
                "monic_coeffs_leading_first": [str(c) for c in Fm.all_coeffs()],
                "irred_prime": p10,
                "resolvent_primes": [(p, list(pat)) for p, pat in chosen],
                "n_real_roots": 8,
            }
            print(json.dumps(out, indent=1), flush=True)
            with open("_galois_decic_candidate.json", "w") as fh:
                json.dump(out, fh, indent=1)
            print("WITNESS FOUND", flush=True)
            return True
        if seed % 25 == 0:
            print(f"...seed {seed}", flush=True)
    return False

if __name__ == "__main__":
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    found = run(lo, hi)
    sys.exit(0 if found else 3)
