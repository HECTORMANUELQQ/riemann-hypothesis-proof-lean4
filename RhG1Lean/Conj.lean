/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import RhG1Lean.Majorant
import RhG1Lean.FunEq

/-!
# Conjugation symmetry of ξ (mapa L20 board)

Mathlib: 
iemannZeta_conj for all s (ZetaAsymp).
Lift to 
iemannXi; equal norms; fixed-t L20 with FE.
Does **not** claim N=0.
-/

open Complex
open scoped Real ComplexConjugate

namespace RhG1Lean

private lemma arg_pi_ne_pi : arg (π : ℂ) ≠ π := by
  have h0 : arg (π : ℂ) = 0 := arg_ofReal_of_nonneg Real.pi_pos.le
  rw [h0]
  exact (ne_of_gt Real.pi_pos).symm

/-- Same as Majorant def, written with -(s/2) for conj lemmas. -/
private lemma riemannXi_eq_neg_div (s : ℂ) :
    riemannXi s =
      (s * (s - 1) / 2) * (π : ℂ) ^ (-(s / 2)) * Complex.Gamma (s / 2) *
        riemannZeta s := by
  unfold riemannXi
  congr 3
  ring_nf

private lemma prefactor_xi_conj (s : ℂ) :
    conj (s * (s - 1) / 2) = conj s * (conj s - 1) / 2 := by
  simp [map_mul, map_div₀, map_sub, map_one, map_ofNat]

private lemma pi_cpow_neg_half_conj (s : ℂ) :
    (π : ℂ) ^ (-(conj s / 2)) = conj ((π : ℂ) ^ (-(s / 2))) := by
  have hn : conj (-(s / 2)) = -(conj s / 2) := by
    simp [map_neg, map_div₀, map_ofNat]
  have h := cpow_conj (π : ℂ) (-(s / 2)) arg_pi_ne_pi
  simp only [conj_ofReal] at h
  rw [← hn]
  exact h

/-- **C1.** ξ(conj s) = conj (ξ s) for all s. -/
theorem riemannXi_conj (s : ℂ) :
    riemannXi (conj s) = conj (riemannXi s) := by
  rw [riemannXi_eq_neg_div, riemannXi_eq_neg_div]
  rw [map_mul, map_mul, map_mul, prefactor_xi_conj, pi_cpow_neg_half_conj, riemannZeta_conj]
  have hdiv : conj s / 2 = conj (s / 2) := by
    simp [map_div₀, map_ofNat]
  rw [hdiv, Complex.Gamma_conj]

theorem norm_riemannXi_conj (s : ℂ) :
    ‖riemannXi (conj s)‖ = ‖riemannXi s‖ := by
  rw [riemannXi_conj, norm_conj]

/-- Fixed-t L20: ‖ξ(σ+it)‖ = ‖ξ((1-σ)+it)‖ under FE hyps at z = σ+it. -/
theorem norm_riemannXi_symm_re {σ t : ℝ} {z : ℂ}
    (hz : z = (σ : ℂ) + I * t)
    (hs0 : z ≠ 0) (hs1 : z ≠ 1)
    (hG : Gammaℝ z ≠ 0) (hG' : Gammaℝ (1 - z) ≠ 0) :
    ‖riemannXi ((σ : ℂ) + I * t)‖ =
      ‖riemannXi ((1 - σ : ℂ) + I * t)‖ := by
  have hFE := (norm_riemannXi_one_sub hs0 hs1 hG hG').symm
  have h1z : 1 - z = (1 - σ : ℂ) + I * (-t) := by
    simp [hz]; ring
  have hconjz : conj (1 - z) = (1 - σ : ℂ) + I * t := by
    rw [h1z]
    simp [map_add, map_mul, conj_ofReal, conj_I]
  calc
    ‖riemannXi ((σ : ℂ) + I * t)‖ = ‖riemannXi z‖ := by rw [hz]
    _ = ‖riemannXi (1 - z)‖ := hFE
    _ = ‖riemannXi (conj (1 - z))‖ := (norm_riemannXi_conj (1 - z)).symm
    _ = ‖riemannXi ((1 - σ : ℂ) + I * t)‖ := by rw [hconjz]

end RhG1Lean
