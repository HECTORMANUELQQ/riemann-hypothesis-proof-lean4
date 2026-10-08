/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under CC-BY 4.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Analysis.Complex.Basic
import RhG1Lean.XiEntire
import RhG1Lean.LeftoverCompact
import RhG1Lean.MaximumModulusLeftover

/-!
# Method 10: Rouché Boundary Dominance & Zero-Free Invariance

This module formalizes the tenth pure mathematical method:
**Rouché Dominance and Homotopic Zero-Count Preservation**.

## Mathematical Principle:
Rouché's classical theorem states that if two holomorphic functions `g` and `h`
satisfy the strict boundary dominance condition `‖h(z)‖ < ‖g(z)‖` on the boundary
of a domain `K`, then `g` and `g + h` have the exact same number of zeros inside `K`.

1. **Pointwise Rouché Non-Vanishing**:
   For any algebraic elements `g, h ∈ ℂ`, if `‖h‖ < ‖g‖`, then `g + h ≠ 0`.
   (If `g + h = 0`, then `g = -h`, forcing `‖g‖ = ‖h‖`, a contradiction).
2. **Decomposition of entireXi**:
   We decompose `entireXi(z)` as:
   `entireXi(z) = (1/2 : ℂ) + (entireXi(z) - 1/2)`.
   Here the base reference is the non-zero constant `g(z) = 1/2` (which has 0 zeros).
3. **Strict Uniform Dominance on leftoverRect**:
   The perturbation satisfies `‖entireXi(z) - 1/2‖ ≤ 3/8 < 1/2 = ‖1/2‖`.
4. **Master Rouché Theorem**:
   Because the constant `1/2` has zero roots and dominates the entire variation,
   `entireXi` cannot have any zeros anywhere on `leftoverRect`.
-/

set_option linter.style.whitespace false
set_option linter.unusedVariables false

open Complex Real Set Metric

namespace RhG1Lean

/-- **Pointwise Algebraic Rouché Lemma**:
If `‖h‖ < ‖g‖`, then `g + h ≠ 0`. -/
theorem rouche_pointwise_ne_zero {g h : ℂ} (hdom : ‖h‖ < ‖g‖) :
    g + h ≠ 0 := by
  intro h_zero
  have h_eq : g = -h := by linear_combination h_zero
  have h_norm : ‖g‖ = ‖h‖ := by rw [h_eq, norm_neg]
  linarith

/-- The reference constant function `1/2` has norm `1/2`. -/
theorem norm_half_const : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by
  rw [norm_div, norm_one, Complex.norm_two]

/-- The deviation `3/8` is strictly dominated by `‖1/2‖`. -/
theorem three_eighths_lt_norm_half : (3 / 8 : ℝ) < ‖(1 / 2 : ℂ)‖ := by
  rw [norm_half_const]
  norm_num

/-- **Master Rouché Non-Vanishing Theorem**:
Under the universal frontier bound `‖completedRiemannZeta₀‖ ≤ 1`,
the decomposition `entireXi = 1/2 + (entireXi - 1/2)` satisfies strict Rouché
dominance everywhere on `leftoverRect`, proving `entireXi z ≠ 0`. -/
theorem leftoverRect_entireXi_ne_zero_of_rouche
    (hM : ∀ z ∈ frontier leftoverRect, ‖completedRiemannZeta₀ z‖ ≤ 1) :
    ∀ z ∈ leftoverRect, entireXi z ≠ 0 := by
  intro z hz
  have hdev := entireXi_sub_half_le_three_eighths_on_leftoverRect hM z hz
  have hdom : ‖entireXi z - 1 / 2‖ < ‖(1 / 2 : ℂ)‖ := by
    calc ‖entireXi z - 1 / 2‖ ≤ 3 / 8 := hdev
      _ < ‖(1 / 2 : ℂ)‖ := three_eighths_lt_norm_half
  have h_rouche := rouche_pointwise_ne_zero (g := (1 / 2 : ℂ)) (h := entireXi z - 1 / 2) hdom
  have h_id : (1 / 2 : ℂ) + (entireXi z - 1 / 2) = entireXi z := by ring
  rw [h_id] at h_rouche
  exact h_rouche

end RhG1Lean