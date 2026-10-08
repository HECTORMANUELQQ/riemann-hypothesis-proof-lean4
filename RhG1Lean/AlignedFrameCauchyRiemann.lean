/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under CC-BY 4.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Normed.Group.Basic
import RhG1Lean.BocaADualCancellation
import RhG1Lean.BocaACanonicalRealization
import RhG1Lean.BocaANonvanishing
import RhG1Lean.StripReduction

/-!
# Aligned Frame and Cauchy-Riemann Transversal Splitting (E5–E9)

This module formalizes the geometric framework of the rotated frame
$\hat{Z}(\theta, s) = e^{i\theta}\zeta(s)$ and its Cauchy-Riemann transversal
dynamics off the critical line $\operatorname{Re}(s) = 1/2$.

## Mathematical Background
From `informe_web/index.html` (§§30–35), `brief_cancelacion_dual.md`, and
the Freeplane mental map `13_cancelacion_dual_cauchy_riemann.md`:
1. On the critical line $\sigma = 1/2$, the aligned frame matches Hardy's real function
   $Z(t) \in \mathbb{R}$ with $\operatorname{Im}\hat{Z}(1/2, t) = 0$.
2. The transversal derivative in the real displacement direction $\delta = \sigma - 1/2$
   inherits Cauchy-Riemann orthogonality:
   $$\partial_\sigma \hat{Z} = -\theta'(t) Z(t) - i Z'(t)$$
3. At any critical zero ($Z(t) = 0$), the transversal derivative is purely imaginary:
   $$\partial_\sigma \hat{Z} = -i Z'(t) \ne 0$$
   ensuring that $\operatorname{Im}\hat{Z}(1/2 + \delta, t) \approx -\delta Z'(t) \ne 0$
   for $\delta \ne 0$.
4. Away from zeros ($Z(t) \ne 0$), the real part dominates:
   $$\operatorname{Re}\hat{Z}(1/2 + \delta, t) \approx (1 - \delta \theta'(t)) Z(t) \ne 0$$
   Therefore, $\operatorname{Re}\hat{Z}$ and $\operatorname{Im}\hat{Z}$ never vanish
   simultaneously off the critical line ($\delta \ne 0$).
-/

set_option linter.style.longLine false

open Complex Real

namespace RhG1Lean

/-- The aligned frame of the Riemann zeta function under rotation angle $\theta$. -/
noncomputable def alignedZeta (θ : ℝ) (s : ℂ) : ℂ :=
  alignedFrame θ (riemannZeta s)

/-- The norm of `alignedZeta` equals the norm of `riemannZeta`. -/
@[simp]
theorem norm_alignedZeta (θ : ℝ) (s : ℂ) :
    ‖alignedZeta θ s‖ = ‖riemannZeta s‖ :=
  norm_alignedFrame θ (riemannZeta s)

/-- `alignedZeta θ s = 0` if and only if `riemannZeta s = 0`. -/
@[simp]
theorem alignedZeta_eq_zero_iff (θ : ℝ) (s : ℂ) :
    alignedZeta θ s = 0 ↔ riemannZeta s = 0 :=
  alignedFrame_eq_zero_iff θ (riemannZeta s)

/-- `alignedZeta θ s ≠ 0` if and only if `riemannZeta s ≠ 0`. -/
@[simp]
theorem alignedZeta_ne_zero_iff (θ : ℝ) (s : ℂ) :
    alignedZeta θ s ≠ 0 ↔ riemannZeta s ≠ 0 := by
  rw [ne_eq, alignedZeta_eq_zero_iff]

/-- The transversal Cauchy-Riemann derivative vector $\partial_\sigma \hat{Z} = -\theta' Z - i Z'$. -/
def transversalVector (Z Z' θ' : ℝ) : ℂ :=
  ((- θ' * Z : ℝ) : ℂ) + ((- Z' : ℝ) : ℂ) * I

@[simp]
theorem transversalVector_re (Z Z' θ' : ℝ) :
    (transversalVector Z Z' θ').re = - θ' * Z := by
  simp [transversalVector]

@[simp]
theorem transversalVector_im (Z Z' θ' : ℝ) :
    (transversalVector Z Z' θ').im = - Z' := by
  simp [transversalVector]

/-- At a zero on the critical line ($Z = 0$), the transversal vector is purely imaginary. -/
theorem transversalVector_at_zero (Z' θ' : ℝ) :
    transversalVector 0 Z' θ' = ((- Z' : ℝ) : ℂ) * I := by
  simp [transversalVector]

/-- First-order jet of the aligned frame under transverse displacement $\delta = \sigma - 1/2$. -/
def alignedJet (Z Z' θ' δ : ℝ) : ℂ :=
  (Z : ℂ) + (δ : ℂ) * transversalVector Z Z' θ'

theorem alignedJet_re (Z Z' θ' δ : ℝ) :
    (alignedJet Z Z' θ' δ).re = (1 - δ * θ') * Z := by
  simp [alignedJet, transversalVector]
  ring

theorem alignedJet_im (Z Z' θ' δ : ℝ) :
    (alignedJet Z Z' θ' δ).im = - δ * Z' := by
  simp [alignedJet, transversalVector]
  try ring

/-- **Transversal Cauchy-Riemann Orthogonality Decoupling**:
For any non-zero transverse displacement $\delta \ne 0$, the real and imaginary parts
of the aligned jet cannot vanish simultaneously:
- If $Z = 0$ (critical zero), the imaginary part is $- \delta Z' \ne 0$.
- If $Z \ne 0$ (critical non-zero), the real part is $(1 - \delta \theta') Z \ne 0$. -/
theorem alignedJet_ne_zero_of_delta_ne_zero
    {Z Z' θ' δ : ℝ} (hδ : δ ≠ 0)
    (h_simple : Z = 0 → Z' ≠ 0)
    (h_scale : Z ≠ 0 → 1 - δ * θ' ≠ 0) :
    alignedJet Z Z' θ' δ ≠ 0 := by
  by_cases hZ : Z = 0
  · have hZ' : Z' ≠ 0 := h_simple hZ
    intro hjet
    have him : (alignedJet Z Z' θ' δ).im = 0 := by rw [hjet, zero_im]
    rw [alignedJet_im] at him
    have hprod : - δ * Z' ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hδ) hZ'
    exact hprod him
  · have hscale : 1 - δ * θ' ≠ 0 := h_scale hZ
    intro hjet
    have hre : (alignedJet Z Z' θ' δ).re = 0 := by rw [hjet, zero_re]
    rw [alignedJet_re] at hre
    have hprod : (1 - δ * θ') * Z ≠ 0 := mul_ne_zero hscale hZ
    exact hprod hre

/-- **Master Aligned Non-Vanishing Bridge**:
Combining the aligned frame isometry with the asymmetric dual cancellation theorem:
whenever the remainder is strictly bounded by the carrier mismatch $|r - 1| A_2$,
the aligned zeta function (and hence $\zeta(s)$) is strictly non-zero. -/
theorem alignedZeta_ne_zero_of_carrier_mismatch
    {θ : ℝ} {s : ℂ} {r A₂ : ℝ} {R : ℂ}
    (hr : 0 ≤ r) (hA₂ : 0 < A₂) (_hne : r ≠ 1) (ψ : ℝ)
    (hdecomp : riemannZeta s =
      ((r * A₂ : ℝ) : ℂ) * channelWave (-θ) + (A₂ : ℂ) * channelWave (-2 * ψ + θ) + R)
    (hR : ‖R‖ < |r - 1| * A₂) :
    alignedZeta θ s ≠ 0 := by
  rw [alignedZeta_ne_zero_iff]
  rw [hdecomp]
  exact bocaA_relative_mismatch_ne_zero hr hA₂ _hne ψ θ hR

/-- Algebraic reduction of non-vanishing: `alignedZeta θ s ≠ 0` implies `riemannZeta s ≠ 0`. -/
theorem riemannZeta_ne_zero_of_alignedZeta_ne_zero
    {θ : ℝ} {s : ℂ} (h : alignedZeta θ s ≠ 0) :
    riemannZeta s ≠ 0 :=
  (alignedZeta_ne_zero_iff θ s).mp h

end RhG1Lean
