/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

/-!
# Boca A · dónde vivirían los contraejemplos de altura grande

Mapa (prospecto 28): A = {Im u ≠ 0}, u = w², w = δ + i t.

  Re u = δ² − t²
  Im u = 2 δ t

Si |t| > |δ| (ceros altos, δ acotado por 1/2), Re u < 0:
**fuera del semi-disco G1**. G1–G5 no los muerden.

Rosas / Pick: miran δ=0 (recta). Este lema es el diccionario
“por qué la altura grande no está en O₁”.
-/

open Complex Real

namespace RhG1Lean

theorem re_w_sq (δ t : ℝ) : (((δ : ℂ) + I * t) ^ 2).re = δ * δ - t * t := by
  simp [pow_two, mul_re, mul_im]

theorem im_w_sq (δ t : ℝ) : (((δ : ℂ) + I * t) ^ 2).im = 2 * δ * t := by
  simp [pow_two, mul_re, mul_im]
  ring

/-- **Boca A (Re).** Si |t| > |δ| entonces Re u < 0. -/
theorem bocaA_re_neg {δ t : ℝ} (h : |δ| < |t|) :
    (((δ : ℂ) + I * t) ^ 2).re < 0 := by
  rw [re_w_sq, ← sq δ, ← sq t, ← sq_abs δ, ← sq_abs t]
  have hsq : |δ| ^ 2 < |t| ^ 2 :=
    pow_lt_pow_left₀ h (abs_nonneg δ) (by norm_num : (2 : ℕ) ≠ 0)
  linarith

/-- **Boca A (Im).** Si δ ≠ 0 y t ≠ 0 entonces Im u ≠ 0. -/
theorem bocaA_im_ne_zero {δ t : ℝ} (hδ : δ ≠ 0) (ht : t ≠ 0) :
    (((δ : ℂ) + I * t) ^ 2).im ≠ 0 := by
  rw [im_w_sq]
  simp [mul_eq_zero, hδ, ht]

/-- Un hipotético cero con |Im ρ| > |Re ρ − 1/2| no cae en O₁ = {Re u > 0}. -/
theorem offLine_not_in_O1 {δ t : ℝ} (h : |δ| < |t|) :
    ¬ (0 < (((δ : ℂ) + I * t) ^ 2).re) :=
  not_lt.mpr (le_of_lt (bocaA_re_neg h))

end RhG1Lean
