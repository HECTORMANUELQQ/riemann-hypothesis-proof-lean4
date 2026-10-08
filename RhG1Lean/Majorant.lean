/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under CC-BY 4.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import RhG1Lean.ZetaBound
import RhG1Lean.GammaBound

/-!
# 65.5 · majorante M de |ξ| en Re s > 1

ξ del mapa (AX-C4 + factor s(s-1)/2):

  ξ(s) = s(s-1)/2 · π^{-s/2} · Γ(s/2) · ζ(s)

Piezas ya verdes: |ζ| (65.3), |Γ| (65.4 Euler). Aquí se ensamblan.
No afirma RH. No usa Stirling Bernoulli.
-/

open Complex Real

namespace RhG1Lean

/-- ξ del prospecto 65 / AX-C4. -/
noncomputable def riemannXi (s : ℂ) : ℂ :=
  (s * (s - 1) / 2) * (π : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) * riemannZeta s

/-- Majorante operable: solo depende de σ = Re s. -/
noncomputable def majorantXi (s : ℂ) : ℝ :=
  ‖s * (s - 1) / 2‖ * π ^ (-s.re / 2) *
    Real.Gamma (s.re / 2) * ‖riemannZeta (s.re : ℂ)‖

lemma re_neg_div_two (s : ℂ) : (-s / 2).re = -s.re / 2 := by
  rw [neg_div, neg_re, re_div_two, neg_div]

lemma norm_pi_cpow_neg_half (s : ℂ) :
    ‖(π : ℂ) ^ (-s / 2)‖ = π ^ (-s.re / 2) := by
  rw [norm_cpow_eq_rpow_re_of_pos pi_pos, re_neg_div_two]

lemma re_half_pos_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : 0 < (s / 2).re := by
  rw [re_div_two]
  linarith

/-- **Lema 65.5.** Si `1 < Re s` entonces `‖ξ(s)‖ ≤ majorantXi s`. -/
theorem norm_riemannXi_le_majorant {s : ℂ} (hs : 1 < s.re) :
    ‖riemannXi s‖ ≤ majorantXi s := by
  unfold riemannXi majorantXi
  simp only [norm_mul]
  have hb : ‖(π : ℂ) ^ (-s / 2)‖ = π ^ (-s.re / 2) :=
    norm_pi_cpow_neg_half s
  have hc : ‖Complex.Gamma (s / 2)‖ ≤ Real.Gamma (s.re / 2) := by
    have := norm_Gamma_le_Gamma_re (re_half_pos_of_one_lt_re hs)
    rwa [re_div_two] at this
  have hd : ‖riemannZeta s‖ ≤ ‖riemannZeta (s.re : ℂ)‖ :=
    norm_riemannZeta_le_riemannZeta_re hs
  have hπ : 0 ≤ π ^ (-s.re / 2) :=
    (Real.rpow_pos_of_pos pi_pos _).le
  have hΓ : 0 ≤ Real.Gamma (s.re / 2) :=
    (Real.Gamma_pos_of_pos (by linarith : 0 < s.re / 2)).le
  have hζ : 0 ≤ ‖riemannZeta (s.re : ℂ)‖ := norm_nonneg _
  have ha : 0 ≤ ‖s * (s - 1) / 2‖ := norm_nonneg _
  have hbc := mul_le_mul_of_nonneg_left hc hπ
  -- ‖a‖ * ‖b‖ * ‖c‖ * ‖d‖ ≤ ‖a‖ * π^ * Γ * ‖ζσ‖
  calc
    ‖s * (s - 1) / 2‖ * ‖(π : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖ * ‖riemannZeta s‖
        = ‖s * (s - 1) / 2‖ * (π ^ (-s.re / 2)) * ‖Complex.Gamma (s / 2)‖ * ‖riemannZeta s‖ := by
          rw [hb]
    _ ≤ ‖s * (s - 1) / 2‖ * (π ^ (-s.re / 2)) * Real.Gamma (s.re / 2) * ‖riemannZeta s‖ := by
          gcongr
    _ ≤ ‖s * (s - 1) / 2‖ * (π ^ (-s.re / 2)) * Real.Gamma (s.re / 2) *
          ‖riemannZeta (s.re : ℂ)‖ := by
          gcongr

/-- En el arco R > 1/2, |φ| ≤ π/4, Re s = reSR ⇒ 65.5. -/
theorem norm_riemannXi_le_majorant_on_arc {R φ : ℝ} (hR : 1 / 2 < R) (hφ : |φ| ≤ π / 4)
    {s : ℂ} (hs : s.re = reSR R φ) :
    ‖riemannXi s‖ ≤ majorantXi s :=
  norm_riemannXi_le_majorant (hs ▸ reSR_gt_one hR hφ)

end RhG1Lean
