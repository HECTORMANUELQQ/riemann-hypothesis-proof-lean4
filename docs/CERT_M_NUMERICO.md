# CERT_M_NUMERICO — numerical lower-bound attempt for ‖riemannXi‖ on leftover core

**Date:** 2026-09-16 ~05:10 CT (UTC-6)  
**Region:** `leftoverRect = {½ ≤ Re s ≤ 1, |Im s| ≤ ½}`  
**Core:** `leftoverRect \ ball(1, ε)` with **ε = 0.05**  
**Script:** `sample_xi_leftover_core.py` (mpmath dps=40)  
**Raw data:** `xi_leftover_core_samples.json`

> **CAVEAT (read first):** A dense grid search is an **observation**, not a Lean proof.
> It does **not** establish `∀ s ∈ core, ‖riemannXi s‖ ≥ m`. Sampling can miss
> thin valleys; floating-point (even high-dps mpmath) is unverified. Do **not**
> import these numbers into Lean as axioms. See §5 for a path to a *verified*
> certificate.

Lean bridge already FILLED (context):  
`leftoverCore_zeta_ne_zero_of_xi_min_pos` — if `‖ξ‖ ≥ m > 0` on the core, then
no ζ-zeros on `leftoverInterior \ ball(1,ε)`. This note only attacks the
hypothesis “produce m>0”.

---

## 1. Method

### Definition used
\[
\xi(s)=\tfrac12\,s(s-1)\,\pi^{-s/2}\,\Gamma(s/2)\,\zeta(s)
\]
(mpmath `zeta`, `gamma`; same completed form as typical Lean `riemannXi`).

### Why ξ, not ζ alone
- Prefactors `½ s(s-1) π^{-s/2} Γ(s/2)` are holomorphic and **non-zero** on
  leftoverRect except possibly issues at s=1 (pole of ζ, cancelled in ξ →
  ξ(1)=ξ(0)≠0). On Re≥½ the Γ factor has no poles.
- On this box, ‖ξ‖ and ‖ζ‖ are comparable up to a continuous non-vanishing
  multiplier; zeros of ξ ↔ zeros of ζ (away from the trivial zero line, which
  is outside leftoverRect).

### Sampling design
| Layer | Spec |
|---|---|
| Main grid | 101 × 101 on `[½,1] × [-½,½]` (Δσ=Δt=0.005) |
| Edge extras | 51 pts each on Im=±½, Re=½, Re=1 |
| Exclusion | discard points with `\|s-1\| < 0.05` |
| Precision | mpmath `dps=40` |
| Core samples | **10121** finite ‖ξ‖ values |

Also: local refinement near corners (0.5±0.5i) and denser 201-pt scan of
`|Im|=½` edges — same min location/value.

### What we did **not** do
- No majorant from Re>1 pulled into the strip (forbidden / invalid).
- No Rosas/Pick (γ≥14; irrelevant for |t|≤½).
- No claim that min-on-grid = min-on-compact.

---

## 2. Concrete numbers

| Quantity | Value |
|---|---|
| **min sampled ‖ξ‖** | **0.4942569879100763** |
| **argmin** | **s = ½ − ½ i** (and conjugate **½ + ½ i**, same value) |
| max sampled ‖ξ‖ | ≈ 0.499971 (near Re=1, Im≈0.05, just outside ball) |
| Samples with ‖ξ‖ < 10⁻² | **0** |
| Samples with ‖ξ‖ < 10⁻⁶ | **0** |
| Samples with ‖ξ‖ < 10⁻⁸ | **0** |
| Range of ‖ξ‖ on core (sampled) | ≈ **[0.49426, 0.49997]** — extremely flat |

**Edge mins (among core samples):**

| Edge | min ‖ξ‖ | at |
|---|---|---|
| \|Im\|=½ | 0.49425698791 | ½ ± ½ i |
| Re=½ | 0.49425698791 | ½ ± ½ i |
| Re=1 (excl. ball) | 0.49712308810 | 1 ± ½ i |

**‖ζ‖ at argmin:** ≈ 1.065 (comfortably away from 0).

### Candidate numerical m
\[
m_{\mathrm{num}} \;:=\; \tfrac12 \cdot \min_{\mathrm{sampled}} \|\xi\|
\;\approx\; \mathbf{0.247128493955}
\]
Rationale: factor ½ leaves margin against (a) grid undersampling and
(b) rounding — still ≫ 10⁻⁶. **Heuristic only**; not a proof bound.

Observation: on this tiny box ξ is nearly constant (~½), consistent with
ξ(0)=ξ(1)≈0.5 and analytic continuation with no nearby zeros (first ζ zero
has Im ≈ 14.13 ≫ ½).

---

## 3. |Im| = ½ boundary — honest analytic status

**Question:** Can classical bounds + FE + known Re≥1 nonvanishing give
`‖ξ‖>0` on the segments `{σ + i/2 : σ∈[½,1]}` (and conjugate) *without RH*?

### What classical tools give for free
1. **Re s ≥ 1, s ≠ 1:** `ζ(s) ≠ 0` (mathlib: `riemannZeta_ne_zero_of_one_le_re`).
   So on the *right endpoints* `1 ± i/2`: ‖ξ‖>0 — already covered by existing
   Lean nonvanishing, no numerics needed.
2. **Functional equation** `ξ(s)=ξ(1−s)`: maps the segment to
   `{σ − i/2 : σ∈[0,½]}` (left half). FE alone **does not** clear the
   open segment `½ < σ < 1` at height ½; it only relates left↔right.
3. **Classical zero-free regions** near Re=1 (de la Vallée Poussin /
   Korobov–Vinogradov type): typically
   `σ ≥ 1 − c / log(|t|+2)`. At `|t|=½` this only pushes a *tiny* distance
   left of Re=1 — **nowhere near** Re=½. Useless for emptying the whole edge.
4. **Known low-lying zero tables:** the first nontrivial zero is at
   `½ + i·14.13…`. So *empirically* there are no zeros with `|t|≤½` at all.
   Turning that into a Lean theorem requires either a verified computation
   or a classical argument that does not currently exist as a short
   mathlib lemma for this box.

### Honest conclusion for |Im|=½
- **Without RH and without a verified numerical certificate:** classical
  FE + Re≥1 nonvanishing do **not** by themselves prove `ζ≠0` (hence
  `ξ≠0`) on the full horizontal edges `|Im|=½`, `½≤Re≤1`.
- The edges are **not harder** than the interior of leftoverRect for the
  |ξ|-minimum approach: they are part of the same compact core, and the
  sampled min is attained *at the corners* of those edges.
- Separating “prove edges analytically, numerics only for interior” is
  attractive but **not currently available** from mathlib-scale classical
  lemmas for `|t|=½`.

Recommended stance: treat the **whole core** (including |Im|=½) as one
compact for a single `m>0` certificate, rather than splitting edges out
for a separate classical argument.

---

## 4. Can this become a Lean numerical certificate?

| Level | Status | Effort |
|---|---|---|
| **A. Heuristic (this file)** | Done — suggests `m ≈ 0.25` is safe | — |
| **B. Unverified float axiom** | `axiom xi_core_min_bound : ∀ s ∈ core, ‖ξ s‖ ≥ (247/1000)` | **Forbidden** by project policy (no fake RH / no numeric axioms pretending to be proofs) |
| **C. Interval arithmetic, unverified runtime** | Python/Arb/MPFI enclosure on a triangulation or ball cover; still external | Useful engineering check; not Lean |
| **D. Verified interval arithmetic in Lean** | Ball arithmetic / `Interval` tactics + explicit Taylor/series bounds for ζ, Γ on each cell of a finite cover of the core | **Real path** — large but finite |
| **E. Cite external formalization** | Import a verified zero-free result for `|t|≤14` if one appears upstream | Watch mathlib / external libs |

### Why D is plausible here (and unusually easy)
- Core diameter is tiny (`≤ √(0.5²+0.5²)≈0.707`, and away from s=1 by ε=0.05).
- Sampled ‖ξ‖ ∈ [0.494, 0.500] — enormous gap above 0; even crude
  enclosures with wide intervals should stay above, say, `0.1`.
- Prefactors π^{-s/2}, Γ(s/2), s(s−1)/2 are routine to bound on a box
  with Re≥½.
- Hard part: rigorous enclosure of `ζ(s)` for Re∈[½,1], |Im|≤½.
  Options: (i) Dirichlet η-series `η(s)=(1−2^{1−s})ζ(s)` which converges
  (conditionally) for Re>0; (ii) Riemann–Siegel / approximate functional
  equation with explicit remainders; (iii) reuse any mathlib series
  definitions with explicit tail bounds.

**This region is among the easiest possible numerical-certificate targets
in the critical strip** — far below the first zero, far from the pole after
cutting ball(1,ε).

---

## 5. Recommended next analytic / Lean step

**Primary recommendation:**  
Start a **verified ball-cover certificate** skeleton in Lean (or via an
external Arb script whose bounds are then re-proved/imported carefully):

1. Fix ε=1/20, target `m = 1/10` (very conservative vs `m_num≈0.247`).
2. Cover `leftoverRect \ ball(1,ε)` by a finite grid of closed disks/squares.
3. On each cell, produce a rigorous upper bound on ‖ξ(c)−ξ(s)‖ (mean-value /
   derivative bound) and a rigorous lower bound on ‖ξ(c)‖, hence
   `‖ξ(s)‖ ≥ ‖ξ(c)‖ − Lip·r > m` if the cell is small enough.
4. Glue with `Finset` exhaustion → `∀ s ∈ core, ‖riemannXi s‖ ≥ m`.
5. Feed into existing `leftoverCore_zeta_ne_zero_of_xi_min_pos`.

**Interim Lean tip (no numerics):** keep tipping F1/F2 lemmas that push
qualitative `m>0` obligations onto smaller sets; do **not** add an
`axiom` for `m_num`.

**Secondary:** if η-series nonvanishing / positivity tools land in mathlib
for Re>0, prefer that analytic route over numerics for the real segment
and possibly the whole box.

---

## 6. Files produced

| Path | Role |
|---|---|
| `/workspace/trabajo/rh_g1_lean/sample_xi_leftover_core.py` | Grid sampler (mpmath) |
| `/workspace/trabajo/rh_g1_lean/xi_leftover_core_samples.json` | Summary + all core samples |
| `/workspace/trabajo/rh_g1_lean/CERT_M_NUMERICO.md` | This certificate note |

Windows mirror target: `C:\Users\cuent\Desktop\trabajo\rh_g1_lean\`
(copy from box when syncing).

---

## 7. One-line result

**min ‖ξ‖ ≈ 0.49426 at ½±½i; candidate m_num ≈ 0.247; no sample near 0;
grid search ≠ proof; next step = verified ball-cover / interval enclosure
toward Lean `m = 1/10`.**
