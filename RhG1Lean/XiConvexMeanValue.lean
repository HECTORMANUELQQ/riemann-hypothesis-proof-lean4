/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under CC-BY 4.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Basic
import RhG1Lean.XiEntire
import RhG1Lean.Lip
import RhG1Lean.LeftoverCompact
import RhG1Lean.MaximumModulusLeftover

/-!
# XiConvexMeanValue: Geometric Convex Control of entireXi in the Cajita (Atom G)

This module formalizes the geometric Lipschitz control of entireXi on the convex domain
leftoverRect using Mathlib's complex Mean Value Theorem:
Convex.norm_image_sub_le_of_norm_deriv_le.

## Mathematical Architecture:
1. convex_leftoverRect (from Lip.lean) establishes convexity of the Cajita.
2. entireXi is entire on ℂ, hence differentiable at every point of leftoverRect.
3. entireXi 1 = 1 / 2 by exact pole cancellation.
4. By the Mean Value Theorem, for any derivative bound C:
   \|entireXi(z) - 1/2\| \le C \cdot \|z - 1\|.
5. For any z ∈ leftoverRect, \|z - 1\| ≤ 1.
6. A derivative bound C < 1/2 guarantees \|entireXi(z) - 1/2\| < 1/2,
   ruling out zeros on the entire 2D Cajita without numerical integration.
-/

set_option linter.style.longLine false

open Complex Real Set Metric

namespace RhG1Lean

/-- The anchor point 1 belongs to leftoverRect. -/
theorem one_mem_leftoverRect : (1 : ℂ) ∈ leftoverRect :=
  mem_leftoverRect_one

/-- Geometric MVT bound on entireXi deviation from 1/2. -/
theorem entireXi_sub_half_le_of_deriv_bound {C : ℝ}
    (hbound : ∀ z ∈ leftoverRect, ‖deriv entireXi z‖ ≤ C)
    {z : ℂ} (hz : z ∈ leftoverRect) :
    ‖entireXi z - 1 / 2‖ ≤ C * ‖z - 1‖ := by
  have hdiff : ∀ w ∈ leftoverRect, DifferentiableAt ℂ entireXi w :=
    fun w _ => differentiable_entireXi w
  have h_mvt := Convex.norm_image_sub_le_of_norm_deriv_le
    hdiff hbound convex_leftoverRect one_mem_leftoverRect hz
  rw [entireXi_one] at h_mvt
  exact h_mvt

/-- Master Cajita Non-Vanishing from Geometric MVT:
Any derivative bound C < 1/2 ensures that entireXi does not vanish anywhere on leftoverRect. -/
theorem leftoverRect_entireXi_ne_zero_of_deriv_lt_half
    {C : ℝ} (hC_lt : C < 1 / 2) (_hC_pos : 0 ≤ C)
    (hbound : ∀ z ∈ leftoverRect, ‖deriv entireXi z‖ ≤ C)
    {z : ℂ} (hz : z ∈ leftoverRect) :
    entireXi z ≠ 0 := by
  intro hz_zero
  have hmvt := entireXi_sub_half_le_of_deriv_bound hbound hz
  have hdist := norm_sub_one_le_one_of_mem_leftoverRect hz
  have hle : ‖entireXi z - 1 / 2‖ ≤ C := by
    calc ‖entireXi z - 1 / 2‖
        ≤ C * ‖z - 1‖ := hmvt
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left hdist _hC_pos
      _ = C := mul_one C
  have hlt : ‖entireXi z - 1 / 2‖ < 1 / 2 := lt_of_le_of_lt hle hC_lt
  rw [hz_zero, zero_sub, norm_neg] at hlt
  have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by
    rw [norm_div, norm_one, Complex.norm_two]
  rw [hhalf] at hlt
  linarith

/-- Master Room 1 (Cajita) Resolution from Geometric Convexity:
Under any derivative bound C < 1/2 on leftoverRect, riemannZeta has no zeros
in leftoverInterior and entireXi has no zeros in leftoverRect. -/
theorem habitacion1_resolved_of_cajita_deriv_bound
    {C : ℝ} (hC_lt : C < 1 / 2) (_hC_pos : 0 ≤ C)
    (hbound : ∀ z ∈ leftoverRect, ‖deriv entireXi z‖ ≤ C) :
    (∀ s ∈ leftoverInterior, riemannZeta s ≠ 0) ∧
    (∀ z ∈ leftoverRect, entireXi z ≠ 0) := by
  constructor
  · intro s hs hz
    have hs_rect : s ∈ leftoverRect := (mem_leftoverInterior.mp hs).1
    have h_ne := leftoverRect_entireXi_ne_zero_of_deriv_lt_half hC_lt _hC_pos hbound hs_rect
    have hz' : entireXi s = 0 := (entireXi_eq_zero_iff_zeta_leftoverInterior hs).mpr hz
    exact h_ne hz'
  · intro z hz
    exact leftoverRect_entireXi_ne_zero_of_deriv_lt_half hC_lt _hC_pos hbound hz

end RhG1Lean
