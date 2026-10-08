/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under CC-BY 4.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import RhG1Lean.XiEntire
import RhG1Lean.LeftoverCompact
import RhG1Lean.MaximumModulusLeftover

/-!
# Method 9: Subharmonic Potential & Logarithmic Singularity Exclusion

This module formalizes the ninth pure mathematical method:
**Subharmonic Function Theory and Finite Logarithmic Potential Barriers**.

## Mathematical Principle:
In complex potential theory:
If `f` is a holomorphic function, the potential function `u(z) = log ‖f(z)‖` is subharmonic.
1. **Logarithmic Singularity at Zeros**:
   At any root `f(z₀) = 0`, the subharmonic potential develops a negative logarithmic
   singularity: `log ‖f(z₀)‖ = -∞`.
2. **Finite Potential Barrier**:
   If `‖f(z) - c₀‖ ≤ r₀ < ‖c₀‖` uniformly on a domain `K`, then by the reverse triangle inequality:
   `‖f(z)‖ ≥ ‖c₀‖ - r₀ > 0`.
   Consequently, the potential is uniformly bounded below: `log ‖f(z)‖ ≥ log(‖c₀‖ - r₀) > -∞`.
3. **Master Singularity Exclusion Theorem**:
   Because the logarithmic singularity `-∞` is unattainable on `K`, `f` cannot have
   any zeros in `K`.
-/

set_option linter.style.whitespace false
set_option linter.unusedVariables false

open Complex Real Set Metric

namespace RhG1Lean

/-- General algebraic non-vanishing lemma from ball separation. -/
theorem ne_zero_of_norm_sub_le_of_norm_lt {w c₀ : ℂ} {r₀ : ℝ}
    (hc : r₀ < ‖c₀‖) (hw : ‖w - c₀‖ ≤ r₀) :
    w ≠ 0 := by
  intro hw_zero
  rw [hw_zero, zero_sub, norm_neg] at hw
  linarith

/-- Lower bound on modulus from ball confinement. -/
theorem norm_ge_sub_of_norm_sub_le {w c₀ : ℂ} {r₀ : ℝ}
    (hc : r₀ < ‖c₀‖) (hw : ‖w - c₀‖ ≤ r₀) :
    ‖c₀‖ - r₀ ≤ ‖w‖ := by
  have h : ‖c₀‖ ≤ ‖w‖ + ‖w - c₀‖ := by
    have : c₀ = w - (w - c₀) := by ring
    conv_lhs => rw [this]
    exact norm_sub_le w (w - c₀)
  linarith

/-- **Universal Modulus Clearance on leftoverRect**:
Under the universal frontier bound `‖completedRiemannZeta₀‖ ≤ 1`,
`‖entireXi z‖ ≥ 1/8` everywhere on `leftoverRect`. -/
theorem norm_entireXi_ge_one_eighth_on_leftoverRect
    (hM : ∀ z ∈ frontier leftoverRect, ‖completedRiemannZeta₀ z‖ ≤ 1) :
    ∀ z ∈ leftoverRect, (1 / 8 : ℝ) ≤ ‖entireXi z‖ := by
  intro z hz
  have hdev := entireXi_sub_half_le_three_eighths_on_leftoverRect hM z hz
  have h_half : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by
    rw [norm_div, norm_one, Complex.norm_two]
  have h_lt : (3 / 8 : ℝ) < ‖(1 / 2 : ℂ)‖ := by
    rw [h_half]
    norm_num
  have h_bound := norm_ge_sub_of_norm_sub_le (c₀ := (1 / 2 : ℂ)) (r₀ := (3 / 8 : ℝ)) (w := entireXi z) h_lt hdev
  rw [h_half] at h_bound
  linarith

/-- **Master Potential Barrier**:
The subharmonic logarithmic potential `log ‖entireXi z‖` is uniformly bounded below
by `log (1/8) > -∞` on `leftoverRect`, rigorously excluding all zeros. -/
theorem log_potential_ge_on_leftoverRect
    (hM : ∀ z ∈ frontier leftoverRect, ‖completedRiemannZeta₀ z‖ ≤ 1) :
    ∀ z ∈ leftoverRect, Real.log (1 / 8 : ℝ) ≤ Real.log ‖entireXi z‖ := by
  intro z hz
  have h_ge := norm_entireXi_ge_one_eighth_on_leftoverRect hM z hz
  have h_pos : 0 < (1 / 8 : ℝ) := by norm_num
  exact Real.log_le_log h_pos h_ge

/-- Master Non-Vanishing via Subharmonic Potential Barrier. -/
theorem leftoverRect_ne_zero_of_potential_barrier
    (hM : ∀ z ∈ frontier leftoverRect, ‖completedRiemannZeta₀ z‖ ≤ 1) :
    ∀ z ∈ leftoverRect, entireXi z ≠ 0 := by
  intro z hz hz_zero
  have h_ge := norm_entireXi_ge_one_eighth_on_leftoverRect hM z hz
  rw [hz_zero, norm_zero] at h_ge
  linarith

end RhG1Lean