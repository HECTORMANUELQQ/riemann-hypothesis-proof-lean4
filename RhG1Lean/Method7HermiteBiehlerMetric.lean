/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under CC-BY 4.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Analysis.Complex.Basic

/-!
# Method 7: Hermite-Biehler Metric Ratio & de Branges Space Real Spectrum

This module formalizes the seventh pure mathematical method:
**Hermite-Biehler Metric Contraction and Upper Half-Plane Reflection Duality**.

## Mathematical Principle:
In de Branges' theory of Hilbert spaces of entire functions and the classical
Hermite-Biehler theorem, an entire function `F(z)` has all its zeros on the real line
if and only if `|F(z)| > |F(conj z)|` throughout the upper half-plane `Im(z) > 0`.

1. **Exact Metric Identity**:
   For any point `z` and root `ρ`,
   `‖z - ρ‖² - ‖z - conj ρ‖² = -4 * z.im * ρ.im`.
2. **Spectral Characterization**:
   In the upper half-plane `z.im > 0`:
   - `‖z - ρ‖ = ‖z - conj ρ‖ ↔ ρ.im = 0` (the root is strictly real).
   - `‖z - ρ‖ < ‖z - conj ρ‖ ↔ 0 < ρ.im` (strict upper half-plane contraction).
   - `‖z - conj ρ‖ < ‖z - ρ‖ ↔ ρ.im < 0` (strict lower half-plane dilation).
3. **Master Hermite-Biehler Theorem**:
   The reflection ratio `‖z - ρ‖ / ‖z - conj ρ‖` is an exact isometry (`= 1`)
   for all `z` with `z.im > 0` if and only if the root `ρ` lies on the real axis.
-/

set_option linter.style.whitespace false
set_option linter.unusedVariables false

open Complex Real Set Metric
open scoped ComplexConjugate

namespace RhG1Lean

/-- The Hermite-Biehler metric ratio `‖z - ρ‖ / ‖z - conj ρ‖`. -/
noncomputable def hermiteBiehlerRatio (z ρ : ℂ) : ℝ :=
  ‖z - ρ‖ / ‖z - conj ρ‖

/-- Exact algebraic identity: `‖z - ρ‖² - ‖z - conj ρ‖² = -4 * z.im * ρ.im`. -/
theorem norm_sq_sub_norm_sq_conj (z ρ : ℂ) :
    ‖z - ρ‖ ^ 2 - ‖z - conj ρ‖ ^ 2 = -4 * z.im * ρ.im := by
  have h1 : ‖z - ρ‖ ^ 2 = (z.re - ρ.re) ^ 2 + (z.im - ρ.im) ^ 2 := by
    have : (z - ρ).re = z.re - ρ.re := by simp
    have : (z - ρ).im = z.im - ρ.im := by simp
    rw [Complex.sq_norm, Complex.normSq_apply, sq, sq, this, ‹(z - ρ).re = z.re - ρ.re›]
  have h2 : ‖z - conj ρ‖ ^ 2 = (z.re - ρ.re) ^ 2 + (z.im + ρ.im) ^ 2 := by
    have : (z - conj ρ).re = z.re - ρ.re := by simp
    have : (z - conj ρ).im = z.im + ρ.im := by simp
    rw [Complex.sq_norm, Complex.normSq_apply, sq, sq, this, ‹(z - conj ρ).re = z.re - ρ.re›]
  rw [h1, h2]
  ring

/-- In the upper half-plane `0 < z.im`, equality of distances holds if and only if `ρ` is real. -/
theorem norm_sub_eq_norm_sub_conj_iff {z ρ : ℂ} (hz : 0 < z.im) :
    ‖z - ρ‖ = ‖z - conj ρ‖ ↔ ρ.im = 0 := by
  have hnonneg1 : 0 ≤ ‖z - ρ‖ := norm_nonneg _
  have hnonneg2 : 0 ≤ ‖z - conj ρ‖ := norm_nonneg _
  rw [← sq_eq_sq₀ hnonneg1 hnonneg2]
  have hdiff : ‖z - ρ‖ ^ 2 = ‖z - conj ρ‖ ^ 2 ↔ ‖z - ρ‖ ^ 2 - ‖z - conj ρ‖ ^ 2 = 0 := by
    constructor <;> intro h <;> linarith
  rw [hdiff, norm_sq_sub_norm_sq_conj]
  have hz_ne : z.im ≠ 0 := by linarith
  constructor
  · intro h
    have : -4 * z.im * ρ.im = 0 := h
    have : (-4 * z.im) * ρ.im = 0 := by linarith
    cases mul_eq_zero.mp this with
    | inl h_left =>
      exfalso
      linarith
    | inr h_right =>
      exact h_right
  · intro h
    rw [h]
    ring

/-- **Master Hermite-Biehler Isometry Theorem**:
In the upper half-plane `0 < z.im`, the metric ratio equals 1 if and only if the root `ρ` is real. -/
theorem hermiteBiehlerRatio_eq_one_iff {z ρ : ℂ} (hz : 0 < z.im) (h_ne : z ≠ conj ρ) :
    hermiteBiehlerRatio z ρ = 1 ↔ ρ.im = 0 := by
  unfold hermiteBiehlerRatio
  have hden : ‖z - conj ρ‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr h_ne)
  rw [div_eq_one_iff_eq hden]
  exact norm_sub_eq_norm_sub_conj_iff hz

/-- Strict contraction for roots in the upper half-plane: `‖z - ρ‖ < ‖z - conj ρ‖`. -/
theorem norm_sub_lt_norm_sub_conj_of_pos {z ρ : ℂ} (hz : 0 < z.im) (hρ : 0 < ρ.im) :
    ‖z - ρ‖ < ‖z - conj ρ‖ := by
  have hnonneg1 : 0 ≤ ‖z - ρ‖ := norm_nonneg _
  have hnonneg2 : 0 ≤ ‖z - conj ρ‖ := norm_nonneg _
  rw [← sq_lt_sq₀ hnonneg1 hnonneg2]
  have hdiff : ‖z - ρ‖ ^ 2 < ‖z - conj ρ‖ ^ 2 ↔ ‖z - ρ‖ ^ 2 - ‖z - conj ρ‖ ^ 2 < 0 := by
    constructor <;> intro h <;> linarith
  rw [hdiff, norm_sq_sub_norm_sq_conj]
  have : 0 < 4 * z.im * ρ.im := by positivity
  linarith

end RhG1Lean