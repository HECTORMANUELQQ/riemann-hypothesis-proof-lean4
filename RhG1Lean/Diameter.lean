/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Basic.Real.Sign
import RhG1Lean.Arc
import RhG1Lean.Majorant

/-!
# G2 · diámetro L_R del semi-disco Γ½

Mapa: L_R = { i y | |y| ≤ R } en el plano u, u = w², w = s − 1/2.

Rama Re w ≥ 0:

  s(y) = 1/2 + √(|y|/2) + i · sign(y) · √(|y|/2)

Re s = σ_min(|y|). Si |y| > 1/2, Re s > 1 y vale 65.5.

El compacto |y| ≤ 1/2 (Re s ≤ 1) no usa la serie de ζ; queda aparte.
-/

open Complex Real

namespace RhG1Lean

/-- s sobre el diámetro u = i y, rama Re w ≥ 0. -/
noncomputable def sOnDiameter (y : ℝ) : ℂ :=
  ⟨(1 : ℝ) / 2 + Real.sqrt (|y| / 2), y.sign * Real.sqrt (|y| / 2)⟩

theorem re_sOnDiameter (y : ℝ) : (sOnDiameter y).re = sigmaMin |y| := by
  simp [sOnDiameter, sigmaMin]

/-- G2 geometría: |y| > 1/2 ⇒ Re s > 1. -/
theorem one_lt_re_sOnDiameter {y : ℝ} (hy : 1 / 2 < |y|) :
    1 < (sOnDiameter y).re := by
  rw [re_sOnDiameter]
  exact sigmaMin_gt_one hy

/-- **G2 apply.** En el diámetro, si |y| > 1/2, vale el majorante 65.5. -/
theorem G2_norm_riemannXi_le_majorant {y : ℝ} (hy : 1 / 2 < |y|) :
    ‖riemannXi (sOnDiameter y)‖ ≤ majorantXi (sOnDiameter y) :=
  norm_riemannXi_le_majorant (one_lt_re_sOnDiameter hy)

lemma sigmaMin_mono {a b : ℝ} (_ha : 0 ≤ a) (hab : a ≤ b) :
    sigmaMin a ≤ sigmaMin b := by
  unfold sigmaMin
  gcongr

lemma sigmaMin_half : sigmaMin (1 / 2) = 1 := by
  unfold sigmaMin
  have : Real.sqrt ((1 / 2 : ℝ) / 2) = 1 / 2 := by
    have h : (1 / 2 : ℝ) / 2 = (1 / 2 : ℝ) ^ 2 := by ring
    rw [h, sqrt_sq (by norm_num)]
  rw [this]
  ring

/-- Compacto G2: |y| ≤ 1/2 ⇒ Re s ≤ 1. -/
theorem re_sOnDiameter_le_one {y : ℝ} (hy : |y| ≤ 1 / 2) :
    (sOnDiameter y).re ≤ 1 := by
  rw [re_sOnDiameter, ← sigmaMin_half]
  exact sigmaMin_mono (abs_nonneg y) hy

/-- En L_R no está el polo s=1 (ni y=0, que da s=1/2). -/
theorem sOnDiameter_ne_one (y : ℝ) : sOnDiameter y ≠ 1 := by
  intro h
  have hr : (1 : ℝ) / 2 + Real.sqrt (|y| / 2) = 1 := by
    have := congrArg Complex.re h
    simpa [sOnDiameter] using this
  have hi : y.sign * Real.sqrt (|y| / 2) = 0 := by
    have := congrArg Complex.im h
    simpa [sOnDiameter] using this
  have hsqrt : Real.sqrt (|y| / 2) = 1 / 2 := by linarith [hr]
  rw [hsqrt, mul_eq_zero] at hi
  rcases hi with hsign | hbot
  · have hy0 : y = 0 := sign_eq_zero_iff.mp hsign
    simp [hy0] at hsqrt
  · norm_num at hbot

theorem half_le_re_sOnDiameter (y : ℝ) : (1 : ℝ) / 2 ≤ (sOnDiameter y).re := by
  rw [re_sOnDiameter]
  unfold sigmaMin
  linarith [sqrt_nonneg (|y| / 2)]

theorem sOnDiameter_ne_zero (y : ℝ) : sOnDiameter y ≠ 0 := by
  intro h
  have hr : (sOnDiameter y).re = 0 := by rw [h]; simp
  linarith [half_le_re_sOnDiameter y, hr]

theorem re_half_pos_sOnDiameter (y : ℝ) : 0 < (sOnDiameter y / 2).re := by
  rw [re_div_two]
  linarith [half_le_re_sOnDiameter y]

end RhG1Lean
