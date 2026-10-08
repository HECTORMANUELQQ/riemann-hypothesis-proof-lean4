/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# G1-arco, geometría (prospecto 65)

Solo lo que Lean acepta cuenta como prueba. Python/mpmath no.
No se afirma RH. No se define S(σ,t).
-/

open Real

namespace RhG1Lean

/-- σ_min(R) = 1/2 + √(R/2). -/
noncomputable def sigmaMin (R : ℝ) : ℝ :=
  1 / 2 + sqrt (R / 2)

/-- Parte real de s_R(φ): 1/2 + √R · cos φ. -/
noncomputable def reSR (R φ : ℝ) : ℝ :=
  1 / 2 + sqrt R * cos φ

/-- Lema 65.1: si R > 1/2 entonces σ_min(R) > 1. -/
theorem sigmaMin_gt_one {R : ℝ} (hR : 1 / 2 < R) :
    1 < sigmaMin R := by
  unfold sigmaMin
  have hpos : 0 < R / 2 := by linarith
  have hsq : ((1 : ℝ) / 2) ^ 2 < R / 2 := by nlinarith
  have hsqrt : (1 : ℝ) / 2 < sqrt (R / 2) :=
    (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)).mpr hsq
  linarith

/-- |φ| ≤ π/4 ⇒ cos φ ≥ √2/2. -/
theorem cos_ge_sqrtTwo_div_two {φ : ℝ} (hφ : |φ| ≤ π / 4) :
    sqrt 2 / 2 ≤ cos φ := by
  have heven : cos φ = cos |φ| := by
    by_cases hp : 0 ≤ φ
    · simp [abs_of_nonneg hp]
    · have : φ < 0 := lt_of_not_ge hp
      rw [abs_of_neg this, cos_neg]
  rw [heven]
  have h0 : 0 ≤ |φ| := abs_nonneg φ
  have hπ : π / 4 ≤ π := by linarith [pi_pos.le]
  have hmono : cos (π / 4) ≤ cos |φ| :=
    Real.cos_le_cos_of_nonneg_of_le_pi h0 hπ hφ
  have : cos (π / 4) = sqrt 2 / 2 := cos_pi_div_four
  linarith

/-- √R · √(1/2) = √(R/2). -/
theorem sqrtR_mul_sqrt_half {R : ℝ} (hR : 0 ≤ R) :
    sqrt R * sqrt (1 / 2) = sqrt (R / 2) := by
  rw [← sqrt_mul hR, mul_one_div R (2 : ℝ)]

/-- √2 / 2 = √(1/2). -/
theorem sqrtTwo_div_two_eq_sqrt_half : sqrt 2 / 2 = sqrt (1 / 2) := by
  have h4 : sqrt (4 : ℝ) = 2 := by
    have : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [this, sqrt_sq (by norm_num)]
  calc
    sqrt 2 / 2 = sqrt 2 / sqrt 4 := by rw [h4]
    _ = sqrt (2 / 4) := (sqrt_div (by norm_num : (0 : ℝ) ≤ 2) (4 : ℝ)).symm
    _ = sqrt (1 / 2) := by norm_num

/-- Lema 65.2: |φ| ≤ π/4, R ≥ 0 ⇒ Re s_R ≥ σ_min. -/
theorem reSR_ge_sigmaMin {R φ : ℝ} (hR : 0 ≤ R) (hφ : |φ| ≤ π / 4) :
    sigmaMin R ≤ reSR R φ := by
  unfold sigmaMin reSR
  have hcos : sqrt 2 / 2 ≤ cos φ := cos_ge_sqrtTwo_div_two hφ
  have hsqrtR : 0 ≤ sqrt R := sqrt_nonneg R
  have : sqrt R * (sqrt 2 / 2) ≤ sqrt R * cos φ :=
    mul_le_mul_of_nonneg_left hcos hsqrtR
  have heq : sqrt R * (sqrt 2 / 2) = sqrt (R / 2) := by
    rw [sqrtTwo_div_two_eq_sqrt_half, sqrtR_mul_sqrt_half hR]
  linarith

/-- R > 1/2 y |φ| ≤ π/4 ⇒ Re s_R > 1 (el arco vive en Re s > 1). -/
theorem reSR_gt_one {R φ : ℝ} (hR : 1 / 2 < R) (hφ : |φ| ≤ π / 4) :
    1 < reSR R φ := by
  have hR0 : 0 ≤ R := by linarith
  linarith [reSR_ge_sigmaMin hR0 hφ, sigmaMin_gt_one hR]

end RhG1Lean
