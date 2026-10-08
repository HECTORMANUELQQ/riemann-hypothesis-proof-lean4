# CERT_L_DERIV — numerical upper-bound attempt for ‖ξ'‖ on leftover core

**Date:** 2026-09-16 ~05:16 CT (UTC-6)  
**Region:** `leftoverRect = {½ ≤ Re s ≤ 1, |Im s| ≤ ½}`  
**Core:** `leftoverRect \ ball(1, ε)` with **ε = 0.05**  
**Script:** `sample_xi_deriv_leftover.py` (mpmath dps=40; local refine dps=50)  
**Raw data:** `xi_deriv_leftover_samples.json`  
**Companion:** `CERT_M_NUMERICO.md` (‖ξ‖ lower), `ATOM_G_LIPSCHITZ.md` (Lean MVT names)

> **CAVEAT (read first):** A dense grid search for `max ‖ξ'‖` is an **observation**,
> not a Lean proof. It does **not** establish `∀ s ∈ core, ‖deriv riemannXi s‖ ≤ L`.
> Sampling can miss peaks; mpmath is unverified. Do **not** import `L_num` into Lean
> as an axiom. Intended use: feed a future **verified ball-cover / interval**
> certificate (Atom G + enclosure of ‖ξ'‖).

No RH claim. ξ is entire; this note only estimates a Lipschitz constant on a tiny box.

---

## 1. Definition and goal

\[
\xi(s)=\tfrac12\,s(s-1)\,\pi^{-s/2}\,\Gamma(s/2)\,\zeta(s)
\]
(same completed form as `CERT_M_NUMERICO` / `sample_xi_leftover_core.py`).

**Goal:** numerically estimate
\[
M' \;:=\; \max_{s\in\mathrm{core}}\|\xi'(s)\|
\]
and recommend a candidate
\[
L_{\mathrm{num}} \;:=\; 2\cdot M'
\]
(safety factor 2 against undersampling / rounding) for later use with
`Convex.norm_image_sub_le_of_norm_deriv_le` on convex pieces.

---

## 2. Convex pieces (for future MVT)

The core itself is **not** convex (open bite at `s=1`). Report max ‖ξ'‖ also on:

| Piece | Definition | Convex? |
|---|---|---|
| **U_left** | `½ ≤ Re ≤ 1−ε`, `|Im| ≤ ½` | yes (closed rectangle) |
| **U_up** | `1−ε ≤ Re ≤ 1`, `ε ≤ Im ≤ ½` | yes |
| **U_dn** | `1−ε ≤ Re ≤ 1`, `−½ ≤ Im ≤ −ε` | yes |

With ε=0.05 these three cover most of the core; a thin **crescent**
`{Re > 1−ε, |Im| < ε, |s−1| ≥ ε}` lies in the core but outside
`U_left ∪ U_up ∪ U_dn`. Sampled ‖ξ'‖ on that crescent is **strictly smaller**
than the core max (see §3), so it does not drive `L_num`. A future cover
should still include the crescent (e.g. as further convex boxes or disks).

---

## 3. Method

| Layer | Spec |
|---|---|
| Main grid | 101 × 101 on `[½,1] × [−½,½]` (Δσ=Δt=0.005) |
| Edge extras | 61 pts on Im=±½, Re=½, Re=1, Re=1−ε, Im=±ε (right strip) |
| Ball ring | radii `1.001ε … 1.2ε`, dense angles (outside open ball) |
| Exclusion | skip `|s−1| < 0.05` and exact `s=1` |
| Derivative | `mpmath.diff(riemann_xi, s)` (complex) |
| FD check | `(ξ(s+h)−ξ(s))/h`, `h=10^{-12}`, every 40th point |
| Precision | mpmath `dps=40` (main); local refine `dps=50` |
| Core samples | **10504** finite ‖ξ'‖ values |

Local refinement (41×41 near the right-top/bottom corners, plus dense crescent
scan) confirmed the same argmax and did not raise the max.

**FD vs `mpmath.diff`:** 263 checks, max relative error ≈ **1.06×10⁻¹¹** — consistent.

---

## 4. Concrete numbers

| Quantity | Value |
|---|---|
| **max sampled ‖ξ'‖ on core** | **0.016243672995308645** |
| **argmax** | **s = 1 − ½ i** and conjugate **1 + ½ i** (same value) |
| min sampled ‖ξ'‖ on core | ≈ 0 (at `s = ½`, within float noise ~10⁻⁵⁰) |
| **candidate `L_num = 2 · max`** | **≈ 0.03248734599061729** |

### By region

| Region | n samples | max ‖ξ'‖ | argmax |
|---|---|---|---|
| **core** | 10504 | **0.016243672995** | 1 ± ½ i |
| **U_left** | 9346 | 0.015437067021 | 0.95 ± ½ i |
| **U_up** | 600 | **0.016243672995** | 1 + ½ i |
| **U_dn** | 589 | **0.016243672995** | 1 − ½ i |
| crescent (extra scan) | — | ≈ 0.01128 | ≈ 0.986 − 0.048 i |

**Top-5 on core (sampled):** all on `|Im|=½`, Re near 1:

| Re | Im | ‖ξ'‖ |
|---|---|---|
| 1.000 | ±0.500 | 0.016243672995 |
| 0.995 | ±0.500 | 0.016160929199 |
| 0.9917 | ±0.500 | 0.016106014618 |
| 1.000 | ±0.490 | 0.016085477250 |
| 0.990 | ±0.500 | 0.016078632356 |

Observation: ‖ξ'‖ is **small and smooth** on this box (order 10⁻²), consistent with
`CERT_M_NUMERICO` finding ‖ξ‖ nearly constant ≈ ½. Peak at the **right corners**
`1±½i`, not near the excised ball.

---

## 5. Recommended L for later Lean (still not an axiom)

| Candidate | Value | Role |
|---|---|---|
| `M'_num` | ≈ 0.016244 | sampled max ‖ξ'‖ |
| **`L_num` (2× safety)** | **≈ 0.03249** | heuristic Lipschitz constant |
| Conservative rational | **`L = 1/20 = 0.05`** | comfortable margin (~3× sampled max) |
| Tighter rational | `L = 1/25 = 0.04` | still > 2× sampled max |
| Aggressive | `L = 1/30 ≈ 0.0333` | barely above `L_num` |

**Recommendation for ball-cover engineering:** use **`L = 1/20`** as the working
target in Lean sketches / Arb scripts. It is safely above the observed max and
has a clean rational. Tighten only after a **verified** enclosure of ‖ξ'‖.

**Do not** add
```lean
axiom xi_deriv_bound : ∀ s ∈ core, ‖deriv riemannXi s‖ ≤ (1/20)
```
— that would be a numeric axiom pretending to be a proof (project policy).

---

## 6. How this feeds a ball-cover certificate

On each convex cell `U` of a finite cover of the core (or on `U_left`, `U_up`,
`U_dn` plus crescent cells):

1. Pick center `c ∈ U`, radius/diameter bound `r`.
2. Rigorous lower bound: `‖ξ(c)‖ ≥ m_c` (interval / series).
3. Rigorous upper bound: `‖ξ'(z)‖ ≤ L_U` for all `z ∈ U`
   (this file only **suggests** the scale of `L_U`; verification TBD).
4. Mean-value / mathlib:
   `‖ξ(s) − ξ(c)‖ ≤ L_U · ‖s − c‖ ≤ L_U · r`.
5. Conclude `‖ξ(s)‖ ≥ m_c − L_U·r`. Choose cells so this is `> m`
   (e.g. `m = 1/10` from `CERT_M_NUMERICO` §5).

With sampled `L ~ 0.016` and `‖ξ‖ ~ 0.49`, even disks of radius `r = 1`
would formally give a huge gap — so **coarse covers** should work once
enclosures exist. The hard part remains a verified bound on ζ (or η) on each cell,
not the size of L.

Lean hooks (names only; see `ATOM_G_LIPSCHITZ.md`):
`Convex.norm_image_sub_le_of_norm_deriv_le`,
`Convex.lipschitzOnWith_of_nnnorm_deriv_le`.

---

## 7. Files produced

| Path | Role |
|---|---|
| `/workspace/trabajo/rh_g1_lean/sample_xi_deriv_leftover.py` | Grid + ring sampler for ‖ξ'‖ |
| `/workspace/trabajo/rh_g1_lean/xi_deriv_leftover_samples.json` | Summary + all samples |
| `/workspace/trabajo/rh_g1_lean/CERT_L_DERIV.md` | This certificate note |

Windows mirror target: `C:\Users\cuent\Desktop\trabajo\rh_g1_lean\`
(copy from box when syncing).

---

## 8. One-line result

**max ‖ξ'‖ ≈ 0.016244 at 1±½i; candidate L_num ≈ 0.0325 (2×); recommend L=1/20
for later Lean ball-cover sketches; sampling ≠ proof; no RH claim.**
