# ATOM G — Lipschitz / mean-value bound for `riemannXi` on leftover core

**Date:** 2026-09-16 ~05:12 CT (UTC-6)  
**Goal:** Exact mathlib names for a Lipschitz/mean-value inequality on a convex set in ℂ, then a Lean theorem applying it to `riemannXi` on a convex open `U` containing `leftoverRect \ ball(1,ε)`.  
**Policy:** No RH claim · no numeric Lipschitz constant L as axiom · no invented numeric bound.

**Lean compile:** **Not attempted.** `lake` / `lean` unavailable on the box; Windows path `C:\Users\cuent\Desktop\trabajo\rh_g1_lean\` not mounted. Draft only (`ATOM_G_LIPSCHITZ.md`). Do **not** claim `RhG1Lean/XiLipschitz.lean` compiled.

---

## 1. Exact mathlib lemma names (verified via mathlib4 docs)

**File:** `Mathlib/Analysis/Calculus/MeanValue.lean`  
**Import:** `Mathlib.Analysis.Calculus.MeanValue`  
**Docs:** https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/MeanValue.html

These are formulated with `RCLike` / `IsRCLikeNormedField`, so they apply to **ℂ** (holomorphic = complex-differentiable) as well as ℝ.

### 1.1 One-dimensional (`deriv`) — preferred for `f : ℂ → ℂ`

| Exact name | Role |
|---|---|
| `Convex.norm_image_sub_le_of_norm_deriv_le` | Pointwise MVT: `‖f y − f x‖ ≤ C * ‖y − x‖` if `∀ z ∈ s, DifferentiableAt 𝕜 f z` and `‖deriv f z‖ ≤ C`, `Convex ℝ s` |
| `Convex.lipschitzOnWith_of_nnnorm_deriv_le` | Same → `LipschitzOnWith C f s` with `C : ℝ≥0` and `‖deriv f z‖₊ ≤ C` |
| `Convex.norm_image_sub_le_of_norm_derivWithin_le` | `DifferentiableOn` + `derivWithin` version |
| `Convex.lipschitzOnWith_of_nnnorm_derivWithin_le` | `LipschitzOnWith` + `derivWithin` |
| `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` | `HasDerivWithinAt` version |
| `Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le` | `HasDerivWithinAt` + `LipschitzOnWith` |
| `lipschitzWith_of_nnnorm_deriv_le` | Global (`univ`) version |

### 1.2 Fréchet (`fderiv`) — same file; also works on ℂ as Banach space over ℂ

| Exact name | Role |
|---|---|
| `Convex.norm_image_sub_le_of_norm_fderiv_le` | `‖f y − f x‖ ≤ C * ‖y − x‖` via `‖fderiv 𝕜 f z‖ ≤ C` |
| `Convex.lipschitzOnWith_of_nnnorm_fderiv_le` | `LipschitzOnWith C f s` via `‖fderiv 𝕜 f z‖₊ ≤ C` |
| `Convex.norm_image_sub_le_of_norm_fderivWithin_le` | `fderivWithin` pointwise |
| `Convex.lipschitzOnWith_of_nnnorm_fderivWithin_le` | `fderivWithin` + `LipschitzOnWith` |
| `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le` | `HasFDerivWithinAt` pointwise |
| `Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le` | `HasFDerivWithinAt` + `LipschitzOnWith` |
| `lipschitzWith_of_nnnorm_fderiv_le` | Global version |

**Recommended primary call for holomorphic ξ on ℂ:**  
`Convex.lipschitzOnWith_of_nnnorm_deriv_le`  
(or pointwise `Convex.norm_image_sub_le_of_norm_deriv_le`).

**Not** the right tool for this atom (different meaning of “convex”):  
`ConvexOn.lipschitzOnWith_of_abs_le` in `Mathlib/Analysis/Convex/Continuous.lean` (convex *functions* ℝ-valued).

---

## 2. Convexity caveat (important)

- `leftoverRect` itself **is** convex (closed rectangle in ℂ ≃ ℝ²).
- `leftoverRect \ ball(1,ε)` is **typically not convex** (open bite at the right face around `s=1`).
- Therefore mathlib MVT **cannot** be applied directly to the sdiff as the convex set `s`.

**Correct pattern (as requested):** introduce a **convex** set `U` (ideally open) with

```text
leftoverRect \ ball(1,ε) ⊆ U ⊆ {s | s ≠ 1 ∧ 0 < (s/2).re}
```

(or any convex `U` on which `riemannXi` is ℂ-differentiable and `‖deriv riemannXi‖` is bounded), then Lipschitz-restrict to the compact core.

Alternative: apply segment-wise MVT inside `leftoverRect` avoiding the ball (harder; not the first tip).

---

## 3. Draft theorem (no numeric `L`)

Target file when lake is available: `RhG1Lean/XiLipschitz.lean`.

```lean
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Basic
import RhG1Lean.LeftoverCompact
import RhG1Lean.LeftoverCore

open Complex Real Set Metric NNReal

namespace RhG1Lean

/-- Holomorphy of ξ on leftoverRect away from 1 lifts to DifferentiableAt
on any subset of the core (ε > 0 ⇒ points ≠ 1). -/
theorem differentiableAt_riemannXi_leftoverRect_sdiff_ball
    {ε : ℝ} (hε : 0 < ε) {s : ℂ}
    (hs : s ∈ leftoverRect \ ball (1 : ℂ) ε) :
    DifferentiableAt ℂ riemannXi s := by
  have hsR : s ∈ leftoverRect := hs.1
  have h1 : s ≠ 1 := by
    intro h
    have : s ∈ ball (1 : ℂ) ε := by
      simp [h, mem_ball, dist_self, hε]
    exact hs.2 this
  exact differentiableAt_riemannXi_leftoverRect hsR h1

/--
**Atom G (conditional Lipschitz).**
If `U` is convex, `riemannXi` is differentiable at every point of `U`, and
`‖deriv riemannXi‖₊` is bounded by an abstract `L : ℝ≥0` on `U`, then
`riemannXi` is `L`-Lipschitz on `U`.

Does **not** invent a numeric `L`. Does **not** claim RH.
Typically instantiate `U` with a convex open neighbourhood of the compact core
`leftoverRect \ ball(1,ε)` (or any convex set containing that core on which
the derivative bound is known).
-/
theorem riemannXi_lipschitz_on_convex
    {U : Set ℂ} {L : ℝ≥0}
    (hU : Convex ℝ U)
    (hdiff : ∀ s ∈ U, DifferentiableAt ℂ riemannXi s)
    (hbound : ∀ s ∈ U, ‖deriv riemannXi s‖₊ ≤ L) :
    LipschitzOnWith L riemannXi U :=
  Convex.lipschitzOnWith_of_nnnorm_deriv_le hdiff hbound hU

/-- Pointwise form (same hypotheses). -/
theorem riemannXi_norm_image_sub_le_on_convex
    {U : Set ℂ} {C : ℝ} {x y : ℂ}
    (hU : Convex ℝ U)
    (hdiff : ∀ s ∈ U, DifferentiableAt ℂ riemannXi s)
    (hbound : ∀ s ∈ U, ‖deriv riemannXi s‖ ≤ C)
    (hx : x ∈ U) (hy : y ∈ U) :
    ‖riemannXi y - riemannXi x‖ ≤ C * ‖y - x‖ :=
  Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound hU hx hy

/--
Specialisation sketch: Lipschitz on a convex `U` that swallows the leftover
core. The core itself need not be convex; the Lipschitz property on `U`
restricts to any subset (in particular the compact core).
-/
theorem riemannXi_lipschitz_on_sdiff
    {ε : ℝ} {U : Set ℂ} {L : ℝ≥0}
    (hε : 0 < ε)
    (hU : Convex ℝ U)
    (hsub : leftoverRect \ ball (1 : ℂ) ε ⊆ U)
    (hdiff : ∀ s ∈ U, DifferentiableAt ℂ riemannXi s)
    (hbound : ∀ s ∈ U, ‖deriv riemannXi s‖₊ ≤ L) :
    LipschitzOnWith L riemannXi (leftoverRect \ ball (1 : ℂ) ε) :=
  (riemannXi_lipschitz_on_convex hU hdiff hbound).mono hsub

end RhG1Lean
```

`LipschitzOnWith.mono` is the standard restriction lemma (`Mathlib.Topology.MetricSpace.Lipschitz`); if the local mathlib pin names it differently, use `LipschitzOnWith.mono` / `Set.MapsTo` style from docs — the inequality form via `norm_image_sub_le` always works by subset.

---

## 4. Proof sketch (using existing RhG1Lean + mathlib)

1. **Differentiability on the core**  
   From `differentiableAt_riemannXi_leftoverRect` (`LeftoverCompact.lean`) + `ε > 0 ⇒ s ≠ 1` on `leftoverRect \ ball(1,ε)` →  
   `differentiableAt_riemannXi_leftoverRect_sdiff_ball`.  
   Underlying: `differentiableAt_riemannXi_of` + `leftoverRect_re_half_pos`.

2. **Convex carrier `U`**  
   Hypothesize / construct convex `U ⊇ leftoverRect \ ball(1,ε)` with `1 ∉ U` (so ξ remains holomorphic).  
   *Blocker:* constructing a convenient convex open `U` that still avoids `1` while covering the bitten rectangle is a geometry obligation (e.g. slightly shrunk rectangle missing a neighbourhood of 1, or a convex hull of the core if that hull avoids 1 — for small ε the convex hull of the core **can** re-include points near 1; check carefully). Safest: take `U = leftoverRect \ closedBall(1,ε/2)` only if proven convex (usually false), or work on a **convex open subset of the left part** of the box, or apply MVT on segments that stay inside a convex open cut.

3. **Derivative bound**  
   Assume abstract `hbound : ∀ s ∈ U, ‖deriv riemannXi s‖₊ ≤ L`.  
   *Do not* plug in a float from `CERT_M_NUMERICO.md`. Producing `L` is a separate certificate (continuous `deriv riemannXi` on compact core ⇒ bounded; existence of some `L` is easy once continuity of `deriv` on a compact is formalised; an *explicit* numeric `L` is harder).

4. **Apply mathlib**  
   `Convex.lipschitzOnWith_of_nnnorm_deriv_le hdiff hbound hU`  
   → `riemannXi_lipschitz_on_convex`  
   → restrict with `mono` to get `riemannXi_lipschitz_on_sdiff`.

5. **Optional pointwise**  
   Same with `Convex.norm_image_sub_le_of_norm_deriv_le`.

6. **Bridge to zeros (out of scope for this atom)**  
   Lipschitz alone does **not** give `‖ξ‖ ≥ m > 0`. It is an intermediate for modulus-of-continuity / comparison arguments. Zero-free still needs something like `leftoverCore_zeta_ne_zero_of_xi_min_pos` + a strict lower bound.

---

## 5. Blockers

| # | Blocker | Severity |
|---|---|---|
| B1 | `leftoverRect \ ball(1,ε)` **not convex** → need convex `U` or segment argument | High (shaping) |
| B2 | No formal bound `‖deriv riemannXi‖ ≤ L` on `U` / core (existence via continuity on compact is plausible; explicit `L` not available; **do not axiomize** a float) | High (content) |
| B3 | Continuity of `deriv riemannXi` on the core not yet a FILLED lemma in local copies (holomorphy ⇒ analytic ⇒ continuous deriv, but may need a mathlib/API tip) | Medium |
| B4 | Constructing open convex `U` with `core ⊆ U` and `1 ∉ cl U` may be fiddly near the right edge | Medium |
| B5 | `lake` not available on this box; Windows project path not accessible → **no compile this turn** | Environment |
| B6 | Lipschitz does not empty zeros by itself | Scope (expected) |

---

## 6. Existing RhG1Lean hooks used

| Lemma / def | File |
|---|---|
| `leftoverRect` | `LeftoverCompact.lean` |
| `differentiableAt_riemannXi_leftoverRect` | `LeftoverCompact.lean` |
| `leftoverRect_re_half_pos` | `LeftoverCompact.lean` |
| `isCompact_leftoverRect_sdiff_open` | `LeftoverCore.lean` |
| `exists_compact_leftoverCore_cut` | `LeftoverCore.lean` |
| `exists_ball_one_leftoverRect_zeta_ne_zero` | `LeftoverCore.lean` |
| `riemannXi_eq_zero_iff_zeta_leftoverRect` | `LeftoverCore.lean` |
| `differentiableAt_riemannXi_of` | (Nonvanishing / Status FILLED) |

---

## 7. Success checklist

- [x] Exact mathlib names recorded (`Convex.norm_image_sub_le_of_norm_deriv_le`, `Convex.lipschitzOnWith_of_nnnorm_deriv_le`, plus fderiv siblings) in `Mathlib.Analysis.Calculus.MeanValue`
- [x] Draft `riemannXi_lipschitz_on_sdiff` / `riemannXi_lipschitz_on_convex` with abstract `L`, convex `U`, no numeric axiom
- [x] Proof sketch + blockers
- [ ] Lean file compiled with `lake build` — **NO** (lake unavailable; draft MD only)

---

## 8. One-line report for parent

**Mathlib:** `Convex.lipschitzOnWith_of_nnnorm_deriv_le` / `Convex.norm_image_sub_le_of_norm_deriv_le` (and fderiv twins `…_fderiv_le`) in `Mathlib/Analysis/Calculus/MeanValue.lean`.  
**Lean compiled:** no.  
**Artifact:** `/workspace/trabajo/rh_g1_lean/ATOM_G_LIPSCHITZ.md`.
