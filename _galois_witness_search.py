import sympy as sp, random
s, w, x, T = sp.symbols('s w x T')

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

def excl(pattern, ds):
    if pattern is None: return False
    return not (set(ds) & sums(pattern))

found = 0
for seed in range(1, 200000):
    random.seed(seed)
    def rnd(): return sp.Rational(random.randint(-6,6), random.randint(1,4))
    P1=(rnd(),rnd()); Q1=(rnd(),rnd())
    P2=(rnd(),rnd()); X2=(rnd(),rnd()); L2=(rnd(),rnd()); Q2=(rnd(),rnd())
    g1=(s,-1,P1[1]-s*P1[0])
    xx=X2[0]+L2[1]*w; yy=X2[1]-L2[0]*w
    g2=(2*(xx-P2[0]), 2*(yy-P2[1]), P2[0]**2+P2[1]**2-xx**2-yy**2)
    E1=onto(g2,Q1,g1); E2=onto(g1,Q2,g2)
    Rs=sp.resultant(sp.Poly(E1,w),sp.Poly(E2,w),w)
    if Rs == 0: continue
    for f0,mm in sp.factor_list(sp.expand(Rs),s)[1]:
        pf = sp.Poly(f0,s)
        if pf.degree()!=6: continue
        lead = pf.LC()
        if lead % 2 == 0: continue
        cs = pf.all_coeffs()
        Fm = sp.Poly([1] + [cs[k]*lead**(k-1) for k in range(1,7)], x)
        fpats = {p: sf_pat(Fm.as_expr(), p, x) for p in (2,3,5,7)}
        need = {1,2,3,4,5}
        cover = set()
        for p in (2,3,5,7):
            pat = fpats[p]
            if pat is None: continue
            cover |= (need - sums(pat))
        if cover != need: continue
        R36 = sp.Poly(sp.resultant(Fm.as_expr(), Fm.as_expr().subs(x, x - T), x), T)
        c36 = R36.all_coeffs()
        if any(c != 0 for c in c36[-6:]): continue
        R30 = sp.Poly(c36[:-6], T)
        r2 = sf_pat(R30.as_expr(), 2, T)
        if not excl(r2, [1,3,5,15]): continue
        okb = [p for p in (3,5,7,11) if excl(sf_pat(R30.as_expr(), p, T), [2,6])]
        okc = [p for p in (3,5) if excl(sf_pat(R30.as_expr(), p, T), [10])]
        if not okb or not okc: continue
        if not pf.is_irreducible: continue
        roots = pf.nroots(n=30)
        if sum(1 for r in roots if abs(sp.im(r))<1e-12) != 4: continue
        ok = 0
        for r in roots:
            if abs(sp.im(r)) < 1e-12:
                E1s = sp.Poly(E1.subs(s, sp.re(r)), w)
                wr = [t for t in E1s.nroots() if abs(sp.im(t)) < 1e-8]
                if any(abs(complex(E2.subs({s: sp.re(r), w: sp.re(t)}))) < 1e-4 for t in wr):
                    ok += 1
        if ok != 4: continue
        print("SEED", seed, flush=True)
        print("fpats", fpats, flush=True)
        print("R30 mod2", r2, "pb", okb, "pc", okc, flush=True)
        print("params P1=%s Q1=%s P2=%s X2=%s L2=%s Q2=%s" % (P1,Q1,P2,X2,L2,Q2), flush=True)
        print("f_coeffs", cs, flush=True)
        found += 1
        if found >= 2: break
    if found >= 2: break
if found == 0: print("NONE", flush=True)
