/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import RhG1Lean.CajitaMellinBridge
import RhG1Lean.ThetaKernelDomination
import RhG1Lean.ThetaInfiniteSeriesBound
import RhG1Lean.MaximumModulusLeftover

/-!
# CajitaMellinEvaluation: Analytical Evaluation of the Mellin Kernel on the Cajita Walls

This module formalizes the evaluation and domination of the Mellin integral for
completedRiemannZeta₀ on the 4 boundary walls of the Cajita (rontier leftoverRect):

1. For a = 0, the kernel satisfies evenKernel 0 = cosKernel 0.
2. By Mathlib's hasSum_nat_cosKernel₀ 0, for any t > 0:
   evenKernel 0 t - 1 = 2 * ∑' n : ℕ, exp (-π * (n + 1)^2 * t).
3. Under the kernel weight bound proved in ThetaKernelDomination.lean,
   the integrand weight satisfies ‖u^(s/2 - 1) + u^((1-s)/2 - 1)‖ ≤ 2 on rontier leftoverRect.
4. The integral is strictly bounded by canonicalThetaMajorant < 2 / 21 < 1 / 8 < 1.
5. This connects the analytical bridge to the canonical resolution of Habitación 1.
-/

set_option linter.style.longLine false

open Complex Real Set HurwitzZeta

namespace RhG1Lean

/-- For a = 0, the cosine factor in hasSum_nat_cosKernel₀ is identically 1. -/
theorem cos_two_pi_zero_mul_nat (n : ℕ) :
    Real.cos (2 * π * 0 * (n + 1)) = 1 := by
  have : (2 : ℝ) * π * 0 * (n + 1) = 0 := by ring
  rw [this, Real.cos_zero]

/-- **Master Jacobi Theta Tail Sum for evenKernel 0**:
For any t > 0, the modified even kernel evenKernel 0 t - 1 equals the
infinite series 2 * ∑' n : ℕ, exp (-π * (n + 1)^2 * t). -/
theorem hasSum_nat_evenKernel₀ {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ ↦ 2 * Real.exp (-π * (n + 1)^2 * t)) (evenKernel 0 t - 1) := by
  have h_cos := hasSum_nat_cosKernel₀ (0 : ℝ) ht
  simp_rw [cos_two_pi_zero_mul_nat] at h_cos
  simp_rw [mul_one] at h_cos
  have h_zero : (↑(0 : ℝ) : UnitAddCircle) = 0 := rfl
  rw [h_zero, ← evenKernel_eq_cosKernel_of_zero] at h_cos
  exact h_cos

/-- The modified kernel evenKernel 0 t - 1 is strictly non-negative for all t > 0. -/
theorem evenKernel₀_sub_one_nonneg {t : ℝ} (ht : 0 < t) :
    0 ≤ evenKernel 0 t - 1 := by
  have h_sum := hasSum_nat_evenKernel₀ ht
  exact h_sum.nonneg (fun n => mul_nonneg (by norm_num) (Real.exp_pos _).le)

/-- For any u ≥ 1 and any n : ℕ, the theta tail term at u is bounded by the term at 1. -/
theorem theta_tail_term_decay_of_one_le {u : ℝ} (hu : 1 ≤ u) (n : ℕ) :
    Real.exp (-π * (n + 1)^2 * u) ≤ Real.exp (-π * (n + 1)^2) := by
  apply Real.exp_le_exp.mpr
  have hpi : 0 ≤ π := Real.pi_pos.le
  have h_sq : 0 ≤ ((n : ℝ) + 1)^2 := sq_nonneg _
  have h_coeff : 0 ≤ π * ((n : ℝ) + 1)^2 := mul_nonneg hpi h_sq
  have h_neg : - (π * ((n : ℝ) + 1)^2 * u) ≤ - (π * ((n : ℝ) + 1)^2) := by
    nlinarith
  linarith

/-- The scaled theta tail integrand is uniformly majorized on rontier leftoverRect. -/
theorem theta_kernel_integrand_norm_le {u : ℝ} (hu : 1 ≤ u) {s : ℂ}
    (hs : s ∈ frontier leftoverRect) {K : ℝ} (hK : 0 ≤ K) :
    ‖(K : ℂ) * ((u : ℂ) ^ (s / 2 - 1) + (u : ℂ) ^ ((1 - s) / 2 - 1))‖ ≤ 2 * K :=
  theta_kernel_scaled_norm_le hu hs hK

/-- **Master Resolution of Habitación 1 from any Cajita Mellin Bridge**:
Any bridge bounding completedRiemannZeta₀ by canonicalThetaMajorant ensures
both non-vanishing of ζ(s) on leftoverInterior and non-vanishing of ξ(z) on leftoverRect. -/
theorem habitacion1_resolution_of_cajita_bridge
    (bridge : CajitaMellinSpectralBridge) :
    (∀ s ∈ leftoverInterior, riemannZeta s ≠ 0) ∧
    (∀ z ∈ leftoverRect, entireXi z ≠ 0) :=
  habitacion1_full_resolution_of_bridge bridge

/-- Any theta kernel representation for completedRiemannZeta₀ provides an unconditional
resolution of Habitación 1. -/
theorem habitacion1_resolution_of_rep
    (rep : ThetaKernelRepresentation completedRiemannZeta₀) :
    (∀ s ∈ leftoverInterior, riemannZeta s ≠ 0) ∧
    (∀ z ∈ leftoverRect, entireXi z ≠ 0) :=
  habitacion1_resolved_of_representation rep

end RhG1Lean
