"""Rule 9C probe (round AQ): the bracket's sides at the two pinned enriched members, using the
tree's own constants (Lresp, mu, Mtot, LloopSharp, LUT, KT) and the round-AQ constants
(Lalpha, KTrel, gEff). Exact rationals; the beta_T of each member is 1/2 and is varied here."""
from fractions import Fraction as Fr
import sys
sys.stdout.reconfigure(encoding="utf-8")

def consts(glo, ghi, dlo, dhi, Mx, Mm, Ms, Mcx, Mmix, Mcs, bS, q, u0, k, r, w, l, c, n, v, SigV):
    KS = (r + w) / (1 - bS * ghi)
    mu = q - bS * (SigV * dhi ** 2 + KS * Ms)
    SigC = bS * KS * Mcx / (1 - bS * ghi ** 2)
    sbar = max(SigV, SigC)
    Lresp = r + bS * (sbar * ghi * dhi + (KS + 2 * sbar) * Mmix)
    Mtot = q + bS * (SigC * dhi ** 2 + KS * Mcs)
    Lloop = ghi + dhi * Lresp / mu
    LUT = v + n + c * Lresp / mu
    La = Mtot * Lresp / (k * mu)
    return dict(KS=KS, mu=mu, Lresp=Lresp, Mtot=Mtot, Lloop=Lloop, LUT=LUT, La=La)

def probe(name, P):
    C = consts(**P)
    glo, ghi, dlo, dhi = P["glo"], P["ghi"], P["dlo"], P["dhi"]
    q, u0, k, l, c, n, v = P["q"], P["u0"], P["k"], P["l"], P["c"], P["n"], P["v"]
    print(f"== {name}: " + ", ".join(f"{a}={b}" for a, b in C.items()))
    gT = lambda bT: (v + n * u0 / q) / (1 - bT * glo)
    KT = lambda bT: C["LUT"] / (1 - bT * C["Lloop"])
    KTrel = lambda bT: (v + l * C["La"]) / (1 - bT * ghi)
    gEff = lambda bT: (v - c * C["Lresp"] / C["mu"]) / (1 - bT * (glo + dlo * C["Lresp"] / C["mu"]))
    rows = []
    for i in range(1, 400):
        bT = Fr(i, 400)
        if bT * C["Lloop"] >= 1: break
        margin = c <= bT * dlo * gT(bT)
        sharp_gT = c - l * C["mu"] / k < bT * dlo * gT(bT)
        sharp_eff = c - l * C["mu"] / k < bT * dlo * gEff(bT)
        rel_exist = l * C["Mtot"] < k * (c - n - bT * dhi * KTrel(bT))
        rel_notdef = l * C["Mtot"] < k * (c - n - bT * dhi * KT(bT))
        rows.append((bT, margin, sharp_gT, sharp_eff, rel_exist, rel_notdef))
    def first(idx): return next((r[0] for r in rows if r[idx]), None)
    def last(idx): return next((r[0] for r in reversed(rows) if r[idx]), None)
    print(f"   margin from {first(1)} ({float(first(1) or 0):.4f}); sharp@gT from {first(2)} ({float(first(2) or 0):.4f}); sharp@gEff from {first(3)} ({float(first(3) or 0):.4f})")
    print(f"   relief-equilibrium up to {last(4)} ({float(last(4) or 0):.4f}); defiance-not-eq up to {last(5)} ({float(last(5) or 0):.4f})")
    for bT in [Fr(1, 8), Fr(1, 10), Fr(1, 2)]:
        print(f"   bT={bT}: margin={c <= bT*dlo*gT(bT)} sharp_eff={c - l*C['mu']/k < bT*dlo*gEff(bT)} rel_exist={l*C['Mtot'] < k*(c-n-bT*dhi*KTrel(bT))} rel_notdef={l*C['Mtot'] < k*(c-n-bT*dhi*KT(bT))}  KTrel={KTrel(bT)} KT={KT(bT)} gEff={gEff(bT)}")

half = Fr(1, 2)
aff = dict(glo=half, ghi=half, dlo=half, dhi=half, Mx=Fr(0), Mm=Fr(0), Ms=Fr(0), Mcx=Fr(0), Mmix=Fr(0), Mcs=Fr(0),
           bS=half, q=Fr(3), u0=Fr(1), k=Fr(3), r=half, w=Fr(1), l=Fr(1), c=Fr(4), n=Fr(0), v=Fr(30), SigV=Fr(1))
qd = dict(aff, glo=Fr(2, 5), ghi=Fr(3, 5), dlo=Fr(2, 5), dhi=Fr(3, 5), Mx=Fr(1, 5), Mcs=Fr(1, 5))
probe("placableAffineCs", aff)
probe("placableQuadDiagCs", qd)
tight = dict(aff, r=Fr(0), SigV=Fr(0))
probe("tight affine rally-free (SigV=0, r=0)", tight)
