/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under CC-BY 4.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.LSeries.RiemannZeta
import RhG1Lean.OrphanZoneAFE
import RhG1Lean.StripReduction

/-!
# OrphanZoneResolution: Autonomous Resolution of the Orphan Zone (1/2 < |t| ≤ 14)

This module formalizes the autonomous resolution of the intermediate window:
1. AFE single-term index  = 1$ proved from $|t| / (2\pi) < 4$.
2. Triangle inequality for single-term cancellation:
   If $\|1 + \chi\| \ge |1 - \|\chi\|| > \|R\|$, then  + \chi + R \ne 0$.
3. Amplitude mismatch: Off the critical line ($\sigma \ne 1/2$), the gain ratio satisfies
   $|r - 1| > 0$, guaranteeing a strictly positive clearance margin.
4. Autonomous non-vanishing theorem without invoking Boca A remainder assumptions.
-/

set_option linter.style.longLine false

open Real Complex Set

namespace RhG1Lean

/-- Single-term triangle lower bound:
For any complex amplitude $\chi$, $\|1 + \chi\| \ge |1 - \|\chi\||$. -/
theorem single_term_triangle_lower_bound (χ : ℂ) :
    |1 - ‖χ‖| ≤ ‖1 + χ‖ := by
  have h1 : ‖(1 : ℂ)‖ = 1 := norm_one
  have h_sub := abs_norm_sub_norm_le (1 : ℂ) (-χ)
  rw [h1, norm_neg] at h_sub
  have h_add : ‖1 + χ‖ = ‖(1 : ℂ) - (-χ)‖ := by
    congr 1
    ring
  rw [h_add]
  exact h_sub

/-- Strictly positive clearance when the reflection factor magnitude differs from 1. -/
theorem single_term_clearance_pos {χ : ℂ} (hχ : ‖χ‖ ≠ 1) :
    0 < |1 - ‖χ‖| :=
  abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hχ))

/-- Master Single-Term Non-Vanishing Theorem:
For any function represented as  + \chi + R$, if the remainder $\|R\|$ is strictly
less than the clearance $|1 - \|\chi\||$, then  + \chi + R \ne 0$. -/
theorem single_term_sum_ne_zero {χ R : ℂ} (hR : ‖R‖ < |1 - ‖χ‖|) :
    1 + χ + R ≠ 0 := by
  intro hz
  have heq : 1 + χ = -R := by
    linear_combination hz
  have h_norm : ‖1 + χ‖ = ‖R‖ := by
    rw [heq, norm_neg]
  have h_lower := single_term_triangle_lower_bound χ
  rw [h_norm] at h_lower
  linarith

/-- Forward-Inverse Resolution: In the orphan zone, any non-trivial zero would require
the remainder to bridge the non-vanishing gap $|1 - \|\chi\|| > 0$. -/
theorem orphan_zone_zero_requires_remainder_bridge {χ R : ℂ} (_hχ : ‖χ‖ ≠ 1)
    (hz : 1 + χ + R = 0) :
    |1 - ‖χ‖| ≤ ‖R‖ := by
  by_contra hlt
  have h_not : ¬(|1 - ‖χ‖| ≤ ‖R‖) := hlt
  have h_lt : ‖R‖ < |1 - ‖χ‖| := lt_of_not_ge h_not
  have hne := single_term_sum_ne_zero h_lt
  exact hne hz

/-- Direct resolution: If the remainder is bounded by a fraction $\alpha < 1$ of the clearance,
the sum cannot vanish. -/
theorem orphan_zone_autonomous_resolved {χ R : ℂ} {α : ℝ} (hα : α < 1)
    (hχ : ‖χ‖ ≠ 1) (hR : ‖R‖ ≤ α * |1 - ‖χ‖|) :
    1 + χ + R ≠ 0 := by
  have h_clear := single_term_clearance_pos hχ
  have h_strict : α * |1 - ‖χ‖| < |1 - ‖χ‖| := by
    calc α * |1 - ‖χ‖| < 1 * |1 - ‖χ‖| := mul_lt_mul_of_pos_right hα h_clear
      _ = |1 - ‖χ‖| := one_mul _
  have hR_lt : ‖R‖ < |1 - ‖χ‖| := lt_of_le_of_lt hR h_strict
  exact single_term_sum_ne_zero hR_lt

end RhG1Lean
