/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import RhG1Lean.Arc

/-!
# Lema 65.3: `|ζ(s)| ≤ |ζ(σ)|` si Re s > 1

Serie de Dirichlet (mathlib) + desigualdad triangular. Sin RH.
-/

open Complex Real

namespace RhG1Lean

lemma norm_one_div_succ_cpow (n : ℕ) (s : ℂ) :
    ‖(1 : ℂ) / (n.succ : ℂ) ^ s‖ = (n.succ : ℝ) ^ (-s.re) := by
  rw [norm_div, norm_one, norm_natCast_cpow_of_pos n.succ_pos s, one_div,
    ← Real.rpow_neg n.succ.cast_nonneg]

lemma one_div_succ_cpow_ofReal (n : ℕ) (σ : ℝ) :
    (1 : ℂ) / (n.succ : ℂ) ^ (σ : ℂ) = ↑((n.succ : ℝ) ^ (-σ)) := by
  have hx : 0 ≤ (n.succ : ℝ) := n.succ.cast_nonneg
  have hpow : (n.succ : ℂ) ^ (σ : ℂ) = ↑((n.succ : ℝ) ^ σ) := by
    rw [← ofReal_natCast, ofReal_cpow hx]
  rw [hpow, div_eq_mul_inv, one_mul, ← ofReal_inv, ← Real.rpow_neg hx]

lemma summable_rpow_neg_succ {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ => (n.succ : ℝ) ^ (-σ) := by
  have h : Summable fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ σ :=
    Real.summable_one_div_nat_rpow.mpr hσ
  have h1 : Summable fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ σ :=
    (summable_nat_add_iff 1).mpr h
  refine h1.congr fun n : ℕ => ?_
  rw [one_div, ← Real.rpow_neg n.succ.cast_nonneg]

lemma summable_norm_one_div_succ_cpow {s : ℂ} (hs : 1 < s.re) :
    Summable fun n : ℕ => ‖(1 : ℂ) / (n.succ : ℂ) ^ s‖ :=
  (summable_rpow_neg_succ hs).congr fun n => (norm_one_div_succ_cpow n s).symm

lemma zeta_eq_tsum_succ {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = ∑' n : ℕ, (1 : ℂ) / (n.succ : ℂ) ^ s := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  refine tsum_congr fun n => ?_
  simp [Nat.cast_succ]

/-- **Lema 65.3.** Si `1 < Re s` entonces `‖ζ(s)‖ ≤ ‖ζ(Re s)‖`. -/
theorem norm_riemannZeta_le_riemannZeta_re {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta s‖ ≤ ‖riemannZeta (s.re : ℂ)‖ := by
  have hsσ : 1 < (s.re : ℂ).re := by simpa using hs
  rw [zeta_eq_tsum_succ hs, zeta_eq_tsum_succ hsσ]
  have hsum := summable_norm_one_div_succ_cpow hs
  refine (norm_tsum_le_tsum_norm hsum).trans ?_
  have hnorm_s : ∀ n : ℕ, ‖(1 : ℂ) / (n.succ : ℂ) ^ s‖ = (n.succ : ℝ) ^ (-s.re) :=
    fun n => norm_one_div_succ_cpow n s
  have hnorm_σ : ∀ n : ℕ, ‖(1 : ℂ) / (n.succ : ℂ) ^ (s.re : ℂ)‖ = (n.succ : ℝ) ^ (-s.re) :=
    fun n => by simpa using norm_one_div_succ_cpow n (s.re : ℂ)
  have htsum_norm :
      ∑' n : ℕ, ‖(1 : ℂ) / (n.succ : ℂ) ^ s‖ =
        ∑' n : ℕ, (n.succ : ℝ) ^ (-s.re) :=
    tsum_congr hnorm_s
  rw [htsum_norm]
  have hterm : ∀ n : ℕ, (1 : ℂ) / (n.succ : ℂ) ^ (s.re : ℂ) =
      Complex.ofReal ((n.succ : ℝ) ^ (-s.re)) :=
    fun n => one_div_succ_cpow_ofReal n s.re
  have htsumσ :
      ∑' n : ℕ, (1 : ℂ) / (n.succ : ℂ) ^ (s.re : ℂ) =
        ∑' n : ℕ, Complex.ofReal ((n.succ : ℝ) ^ (-s.re)) :=
    tsum_congr hterm
  rw [htsumσ]
  have hts : (↑(∑' n : ℕ, (n.succ : ℝ) ^ (-s.re)) : ℂ) =
      ∑' n : ℕ, Complex.ofReal ((n.succ : ℝ) ^ (-s.re)) :=
    Complex.ofReal_tsum fun n : ℕ => (n.succ : ℝ) ^ (-s.re)
  have hnorm : ‖∑' n : ℕ, Complex.ofReal ((n.succ : ℝ) ^ (-s.re))‖ =
      |∑' n : ℕ, (n.succ : ℝ) ^ (-s.re)| := by
    rw [← hts]
    exact Complex.norm_real _
  rw [hnorm]
  exact le_abs_self _

/-- En el arco R > 1/2, |φ| ≤ π/4, Re s = reSR R φ ⇒ cota 65.3. -/
theorem norm_riemannZeta_le_on_arc {R φ : ℝ} (hR : 1 / 2 < R) (hφ : |φ| ≤ π / 4)
    {s : ℂ} (hs : s.re = reSR R φ) :
    ‖riemannZeta s‖ ≤ ‖riemannZeta (s.re : ℂ)‖ :=
  norm_riemannZeta_le_riemannZeta_re (hs ▸ reSR_gt_one hR hφ)

end RhG1Lean
