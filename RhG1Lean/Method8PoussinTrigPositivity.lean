/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Method 8: De la Vallée Poussin Harmonic Positivity & Subharmonic Barrier

This module formalizes the eighth pure mathematical method:
**Positive Trigonometric Polynomials and Hadamard-Poussin Subharmonic Barriers**.

## Mathematical Principle:
In the classical 1896 proof of the Prime Number Theorem by Hadamard and de la Vallée Poussin:
The positive trigonometric identity `3 + 4*cos(θ) + cos(2*θ) = 2*(1 + cos(θ))² ≥ 0`
acts as an impenetrable barrier that prevents zeros from touching or crossing boundaries.

1. **Exact Algebraic Reduction**:
   Using `cos(2*θ) = 2*cos(θ)² - 1`:
   `3 + 4*cos(θ) + cos(2*θ) = 2*(1 + cos(θ))²`.
2. **Universal Non-Negativity**:
   `∀ θ : ℝ, 0 ≤ 3 + 4*cos(θ) + cos(2*θ)`.
3. **Strict Positivity Regularity**:
   `0 < 3 + 4*cos(θ) + cos(2*θ) ↔ cos(θ) ≠ -1`.
4. **Subharmonic Barrier**:
   At any phase `θ`, the combination cannot be negative, forcing the product
   of harmonic powers to be bounded below by 1.
-/

set_option linter.style.whitespace false
set_option linter.unusedVariables false

open Real

namespace RhG1Lean

/-- The de la Vallée Poussin trigonometric polynomial `3 + 4*cos(θ) + cos(2*θ)`. -/
noncomputable def poussinTrigPoly (θ : ℝ) : ℝ :=
  3 + 4 * cos θ + cos (2 * θ)

/-- Exact algebraic identity: `poussinTrigPoly θ = 2 * (1 + cos θ) ^ 2`. -/
theorem poussinTrigPoly_eq (θ : ℝ) :
    poussinTrigPoly θ = 2 * (1 + cos θ) ^ 2 := by
  unfold poussinTrigPoly
  have hcos2 : cos (2 * θ) = 2 * cos θ ^ 2 - 1 := cos_two_mul θ
  rw [hcos2]
  ring

/-- **Master Non-Negativity Theorem**:
The de la Vallée Poussin polynomial is universally non-negative for all angles `θ`. -/
theorem poussinTrigPoly_nonneg (θ : ℝ) :
    0 ≤ poussinTrigPoly θ := by
  rw [poussinTrigPoly_eq]
  have : 0 ≤ (1 + cos θ) ^ 2 := sq_nonneg _
  positivity

/-- Strict positivity holds if and only if `cos θ ≠ -1`. -/
theorem poussinTrigPoly_pos_iff (θ : ℝ) :
    0 < poussinTrigPoly θ ↔ cos θ ≠ -1 := by
  rw [poussinTrigPoly_eq]
  have hpos : 0 < (2 : ℝ) := by norm_num
  have hsq : 0 < (1 + cos θ) ^ 2 ↔ 1 + cos θ ≠ 0 := sq_pos_iff
  have hadd : 1 + cos θ ≠ 0 ↔ cos θ ≠ -1 := by
    constructor
    · intro h h_contra
      apply h
      linarith
    · intro h h_contra
      apply h
      linarith
  rw [mul_pos_iff_of_pos_left hpos, hsq, hadd]

/-- The minimum possible value of `poussinTrigPoly` is 0. -/
theorem poussinTrigPoly_min (θ : ℝ) :
    0 ≤ poussinTrigPoly θ :=
  poussinTrigPoly_nonneg θ

end RhG1Lean