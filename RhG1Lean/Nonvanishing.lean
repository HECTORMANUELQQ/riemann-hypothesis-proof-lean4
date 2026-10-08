/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import RhG1Lean.Majorant
import RhG1Lean.Diameter
import RhG1Lean.Arc

/-!
# G3 · ξ ≠ 0 donde Re s > 1

En Re s > 1: ζ ≠ 0 (mathlib), Γ(s/2) ≠ 0 (Re(s/2)>0),
π^{-s/2} ≠ 0, y s(s-1)/2 ≠ 0 porque s≠0 y s≠1.

Aplica al arco G1 y al diámetro G2 con |y|>1/2.
No cubre el compacto |y|≤1/2 ni la boca A.
-/

open Complex Real

namespace RhG1Lean

theorem ne_one_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : s ≠ 1 := by
  intro h
  subst h
  simp at hs

theorem ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : s ≠ 0 := by
  intro h
  subst h
  simp at hs
  linarith

theorem pi_cpow_neg_half_ne_zero (s : ℂ) : (π : ℂ) ^ (-s / 2) ≠ 0 := by
  refine (cpow_eq_zero_iff _ _).not.mpr ?_
  simp [ofReal_eq_zero, pi_ne_zero]

/-- **G3.** Si `1 < Re s` entonces `ξ(s) ≠ 0`. -/
theorem riemannXi_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    riemannXi s ≠ 0 := by
  unfold riemannXi
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_
  · -- s(s-1)/2 ≠ 0
    intro h
    have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
    have hn : s * (s - 1) = 0 := (div_eq_zero_iff.mp h).resolve_right h2
    rcases mul_eq_zero.mp hn with h0 | h1
    · exact (ne_zero_of_one_lt_re hs) h0
    · exact (ne_one_of_one_lt_re hs) (sub_eq_zero.mp h1)
  · exact pi_cpow_neg_half_ne_zero s
  · exact Complex.Gamma_ne_zero_of_re_pos (re_half_pos_of_one_lt_re hs)
  · exact riemannZeta_ne_zero_of_one_lt_re hs

/-- G3 en el arco. -/
theorem G3_riemannXi_ne_zero_on_arc {R φ : ℝ} (hR : 1 / 2 < R) (hφ : |φ| ≤ π / 4)
    {s : ℂ} (hs : s.re = reSR R φ) : riemannXi s ≠ 0 :=
  riemannXi_ne_zero_of_one_lt_re (hs ▸ reSR_gt_one hR hφ)

/-- G3 en el diámetro |y| > 1/2. -/
theorem G3_riemannXi_ne_zero_on_diameter {y : ℝ} (hy : 1 / 2 < |y|) :
    riemannXi (sOnDiameter y) ≠ 0 :=
  riemannXi_ne_zero_of_one_lt_re (one_lt_re_sOnDiameter hy)

theorem re_half_pos_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : 0 < (s / 2).re := by
  rw [re_div_two]
  linarith

/-- G3 en Re s ≥ 1, s ≠ 0,1 (incluye extremos del compacto |y|=1/2). -/
theorem riemannXi_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) (h1 : s ≠ 1)
    (h0 : s ≠ 0) : riemannXi s ≠ 0 := by
  unfold riemannXi
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_
  · intro h
    have hn : s * (s - 1) = 0 := (div_eq_zero_iff.mp h).resolve_right two_ne_zero
    rcases mul_eq_zero.mp hn with hz | h1'
    · exact h0 hz
    · exact h1 (sub_eq_zero.mp h1')
  · exact pi_cpow_neg_half_ne_zero s
  · exact Complex.Gamma_ne_zero_of_re_pos (re_half_pos_of_one_le_re hs)
  · exact riemannZeta_ne_zero_of_one_le_re hs

/-- Extremos del compacto: |y| = 1/2 ⇒ Re s = 1, s ≠ 1, ξ ≠ 0. -/
theorem G3_riemannXi_ne_zero_on_diameter_endpoint {y : ℝ} (hy : |y| = 1 / 2) :
    riemannXi (sOnDiameter y) ≠ 0 := by
  have hre : (sOnDiameter y).re = 1 := by
    rw [re_sOnDiameter, hy, sigmaMin_half]
  refine riemannXi_ne_zero_of_one_le_re (le_of_eq hre.symm) (sOnDiameter_ne_one y) ?_
  intro h0
  have : (sOnDiameter y).re = 0 := by rw [h0]; simp
  rw [hre] at this
  norm_num at this

/-- En todo L_R, ξ=0 ↔ ζ=0 (prefactor, π^{-s/2} y Γ no se anulan). -/
theorem riemannXi_eq_zero_iff_zeta_sOnDiameter (y : ℝ) :
    riemannXi (sOnDiameter y) = 0 ↔ riemannZeta (sOnDiameter y) = 0 := by
  unfold riemannXi
  constructor
  · intro h
    have hπ := pi_cpow_neg_half_ne_zero (sOnDiameter y)
    have hG := Complex.Gamma_ne_zero_of_re_pos (re_half_pos_sOnDiameter y)
    have hp : sOnDiameter y * (sOnDiameter y - 1) / 2 ≠ 0 := by
      intro hp
      have hn : sOnDiameter y * (sOnDiameter y - 1) = 0 :=
        (div_eq_zero_iff.mp hp).resolve_right two_ne_zero
      rcases mul_eq_zero.mp hn with hz | h1
      · exact sOnDiameter_ne_zero y hz
      · exact sOnDiameter_ne_one y (sub_eq_zero.mp h1)
    have : sOnDiameter y * (sOnDiameter y - 1) / 2 *
        (π : ℂ) ^ (-sOnDiameter y / 2) * Complex.Gamma (sOnDiameter y / 2) *
        riemannZeta (sOnDiameter y) = 0 := h
    simp only [mul_eq_zero] at this
    tauto
  · intro h
    simp [h]

end RhG1Lean
