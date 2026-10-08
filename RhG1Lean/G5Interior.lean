/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under CC-BY 4.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Analysis.RCLike.Basic
import RhG1Lean.Nonvanishing
import RhG1Lean.MouthA

/-!
# G5 · N=0 donde sí se puede (sin listar ceros)

En {Re s > 1} ξ ≠ 0 (G3). Eso es N=0 ahí.

En O₁ (sector |Im w| ≤ Re w): si ‖w‖ > √2/2 entonces Re s > 1 y ξ ≠ 0.
Queda el disco |u| ≤ 1/2.

Rosas / monografía Pick-3: γ₁ ≈ 14.13. Esa muestra no vive en |t| < 1/2.
No es prueba Lean del disco chico; es el diccionario.

Ceros de ζ en un compacto: finitos (mathlib). Boca A: |t|>|δ| ⇒ Re u < 0.
-/

open Complex Real Set

namespace RhG1Lean

theorem xi_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : riemannXi s ≠ 0 :=
  riemannXi_ne_zero_of_one_lt_re hs

theorem xi_zeros_one_lt_re_empty :
    {s : ℂ | 1 < s.re ∧ riemannXi s = 0} = (∅ : Set ℂ) := by
  ext s
  constructor
  · intro h
    exact (riemannXi_ne_zero_of_one_lt_re h.1) h.2
  · intro h
    exact h.elim

lemma normSq_le_two_re_sq {w : ℂ} (h : |w.im| ≤ w.re) :
    ‖w‖ ^ 2 ≤ 2 * w.re ^ 2 := by
  have hre : 0 ≤ w.re := le_trans (abs_nonneg w.im) h
  have him : w.im ^ 2 ≤ w.re ^ 2 := by
    have : |w.im| ≤ |w.re| := by simpa [abs_of_nonneg hre] using h
    simpa [sq_abs] using (sq_le_sq.mpr this)
  have hsq : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    calc
      ‖w‖ ^ 2 = Complex.normSq w := (RCLike.normSq_eq_def' (K := ℂ) w).symm
      _ = w.re * w.re + w.im * w.im := Complex.normSq_apply w
      _ = w.re ^ 2 + w.im ^ 2 := by ring
  nlinarith

theorem one_lt_re_of_sector {w : ℂ} (hsec : |w.im| ≤ w.re)
    (hw : Real.sqrt 2 / 2 < ‖w‖) : 1 < ((1 : ℂ) / 2 + w).re := by
  have hre0 : 0 ≤ w.re := le_trans (abs_nonneg w.im) hsec
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hnorm_le : ‖w‖ ≤ Real.sqrt 2 * w.re := by
    have hn : 0 ≤ ‖w‖ := norm_nonneg w
    have hr : 0 ≤ Real.sqrt 2 * w.re := mul_nonneg (Real.sqrt_nonneg 2) hre0
    have hsq := normSq_le_two_re_sq hsec
    have : ‖w‖ ^ 2 ≤ (Real.sqrt 2 * w.re) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      simpa [mul_comm, two_mul] using hsq
    exact (sq_le_sq₀ hn hr).mp this
  have hge : ‖w‖ / Real.sqrt 2 ≤ w.re := (div_le_iff₀ hsqrt2).mpr (by linarith)
  have hhalf : (1 : ℝ) / 2 < ‖w‖ / Real.sqrt 2 := by
    have : (1 : ℝ) / 2 * Real.sqrt 2 = Real.sqrt 2 / 2 := by ring
    rw [lt_div_iff₀ hsqrt2, this]
    exact hw
  have : ((1 : ℂ) / 2 + w).re = 1 / 2 + w.re := by simp
  rw [this]
  linarith

theorem xi_ne_zero_of_sector_outer {w : ℂ} (hsec : |w.im| ≤ w.re)
    (hw : Real.sqrt 2 / 2 < ‖w‖) : riemannXi ((1 : ℂ) / 2 + w) ≠ 0 :=
  riemannXi_ne_zero_of_one_lt_re (one_lt_re_of_sector hsec hw)

theorem finite_zeta_zeros_of_compact {S : Set ℂ} (hS : IsCompact S) :
    (S ∩ riemannZetaZeros).Finite :=
  hS.inter_riemannZetaZeros_finite

end RhG1Lean
