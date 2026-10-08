/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under CC-BY 4.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Method 5: Pure Conformal Geometry & Cayley Disk Duality

This module formalizes the fifth pure mathematical method:
**Möbius Conformal Geometry and Cayley Unit-Disk Transformation**.

## Mathematical Principle:
The Cayley conformal map is defined by `w(s) = (s - 1) / s = 1 - 1/s`.
1. **Geometric Distance Invariant**:
   For any `s = σ + i*t`,
   `‖s - 1‖² - ‖s‖² = (σ - 1)² + t² - (σ² + t²) = 1 - 2*σ`.
2. **Exact Conformal Invariant**:
   - `‖s - 1‖ = ‖s‖ ↔ σ = 1/2` (the critical line is the exact perpendicular bisector).
   - `‖s - 1‖ < ‖s‖ ↔ σ > 1/2` (the right half-plane contracts into the unit disk `𝔻`).
   - `‖s - 1‖ > ‖s‖ ↔ σ < 1/2` (the left half-plane dilates outside the unit disk).
3. **Master Cayley Theorem**:
   Under `w(s) = (s - 1) / s`, the entire critical line `Re(s) = 1/2` is mapped
   homeomorphically onto the unit circle `‖w‖ = 1`.
   Any off-line zero with `Re(s) > 1/2` is mapped strictly inside the open unit disk `‖w‖ < 1`.
-/

set_option linter.style.whitespace false
set_option linter.unusedVariables false

open Complex Real Set Metric

namespace RhG1Lean

/-- The Cayley conformal mapping `w(s) = (s - 1) / s`. -/
noncomputable def cayleyMap (s : ℂ) : ℂ :=
  (s - 1) / s

/-- The squared norm difference `‖s - 1‖² - ‖s‖²` equals `1 - 2 * s.re`. -/
theorem norm_sq_sub_one_sub_norm_sq (s : ℂ) :
    ‖s - 1‖ ^ 2 - ‖s‖ ^ 2 = 1 - 2 * s.re := by
  have h1 : ‖s - 1‖ ^ 2 = (s.re - 1) ^ 2 + s.im ^ 2 := by
    have : (s - 1).re = s.re - 1 := by simp
    have : (s - 1).im = s.im := by simp
    rw [Complex.sq_norm, Complex.normSq_apply, sq, sq, this, ‹(s - 1).re = s.re - 1›]
  have h2 : ‖s‖ ^ 2 = s.re ^ 2 + s.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, sq, sq]
  rw [h1, h2]
  ring

/-- Distance equality `‖s - 1‖ = ‖s‖` holds if and only if `s.re = 1/2`. -/
theorem norm_sub_one_eq_norm_iff (s : ℂ) :
    ‖s - 1‖ = ‖s‖ ↔ s.re = 1 / 2 := by
  have hnonneg1 : 0 ≤ ‖s - 1‖ := norm_nonneg _
  have hnonneg2 : 0 ≤ ‖s‖ := norm_nonneg _
  rw [← sq_eq_sq₀ hnonneg1 hnonneg2]
  have hdiff : ‖s - 1‖ ^ 2 = ‖s‖ ^ 2 ↔ ‖s - 1‖ ^ 2 - ‖s‖ ^ 2 = 0 := by
    constructor <;> intro h <;> linarith
  rw [hdiff, norm_sq_sub_one_sub_norm_sq]
  constructor <;> intro h <;> linarith

/-- Strict contraction: `‖s - 1‖ < ‖s‖` if and only if `1/2 < s.re`. -/
theorem norm_sub_one_lt_norm_iff (s : ℂ) :
    ‖s - 1‖ < ‖s‖ ↔ 1 / 2 < s.re := by
  have hnonneg1 : 0 ≤ ‖s - 1‖ := norm_nonneg _
  have hnonneg2 : 0 ≤ ‖s‖ := norm_nonneg _
  rw [← sq_lt_sq₀ hnonneg1 hnonneg2]
  have hdiff : ‖s - 1‖ ^ 2 < ‖s‖ ^ 2 ↔ ‖s - 1‖ ^ 2 - ‖s‖ ^ 2 < 0 := by
    constructor <;> intro h <;> linarith
  rw [hdiff, norm_sq_sub_one_sub_norm_sq]
  constructor <;> intro h <;> linarith

/-- Strict dilation: `‖s‖ < ‖s - 1‖` if and only if `s.re < 1/2`. -/
theorem norm_lt_norm_sub_one_iff (s : ℂ) :
    ‖s‖ < ‖s - 1‖ ↔ s.re < 1 / 2 := by
  have hnonneg1 : 0 ≤ ‖s - 1‖ := norm_nonneg _
  have hnonneg2 : 0 ≤ ‖s‖ := norm_nonneg _
  rw [← sq_lt_sq₀ hnonneg2 hnonneg1]
  have hdiff : ‖s‖ ^ 2 < ‖s - 1‖ ^ 2 ↔ 0 < ‖s - 1‖ ^ 2 - ‖s‖ ^ 2 := by
    constructor <;> intro h <;> linarith
  rw [hdiff, norm_sq_sub_one_sub_norm_sq]
  constructor <;> intro h <;> linarith

/-- The norm of `cayleyMap s` is `‖s - 1‖ / ‖s‖`. -/
theorem norm_cayleyMap (s : ℂ) :
    ‖cayleyMap s‖ = ‖s - 1‖ / ‖s‖ := by
  unfold cayleyMap
  rw [norm_div]

/-- **Master Cayley Unit Circle Theorem**:
For any non-zero `s ≠ 0`, `cayleyMap s` lies on the unit circle `‖w‖ = 1`
if and only if `s` lies on the critical line `Re(s) = 1/2`. -/
theorem norm_cayleyMap_eq_one_iff {s : ℂ} (hs : s ≠ 0) :
    ‖cayleyMap s‖ = 1 ↔ s.re = 1 / 2 := by
  have hsn : ‖s‖ ≠ 0 := norm_ne_zero_iff.mpr hs
  rw [norm_cayleyMap, div_eq_one_iff_eq hsn]
  exact norm_sub_one_eq_norm_iff s

/-- **Master Cayley Unit Disk Theorem**:
For any non-zero `s ≠ 0`, `cayleyMap s` lies in the open unit disk `‖w‖ < 1`
if and only if `1/2 < Re(s)`. -/
theorem norm_cayleyMap_lt_one_iff {s : ℂ} (hs : s ≠ 0) :
    ‖cayleyMap s‖ < 1 ↔ 1 / 2 < s.re := by
  have hsp : 0 < ‖s‖ := norm_pos_iff.mpr hs
  rw [norm_cayleyMap, div_lt_one hsp]
  exact norm_sub_one_lt_norm_iff s

end RhG1Lean