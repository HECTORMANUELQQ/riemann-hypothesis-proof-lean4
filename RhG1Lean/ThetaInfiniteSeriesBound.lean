/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import RhG1Lean.LambdaZeroRealBound
import RhG1Lean.ThetaTailGeometric
import RhG1Lean.ThetaIntegralBound

/-!
# ThetaInfiniteSeriesBound: Rigorous Convergence and Bound for the Infinite Theta Series

This module formalizes the infinite summation of the Jacobi theta tail:

$$\sum_{n=1}^\infty (e^{-\pi})^{n^2} \le \sum_{n=1}^\infty (e^{-\pi})^n = \frac{e^{-\pi}}{1 - e^{-\pi}} < \frac{1}{7}.$$

Scaling by $2 / \pi$:
$$\frac{2}{\pi} \sum_{n=1}^\infty (e^{-\pi})^{n^2} \le \frac{2}{\pi} \frac{e^{-\pi}}{1 - e^{-\pi}} < \frac{2}{21} < 1.$$

This unconditionally establishes the infinite theta majorant for completedRiemannZeta₀
on the boundary of leftoverRect.
-/

set_option linter.style.longLine false

open Real

namespace RhG1Lean

/-- The n-th term of the Jacobi theta tail (0 for n = 0, q^(n^2) for n ≥ 1). -/
def thetaTailTerm (q : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else q ^ (n ^ 2)

/-- The n-th term of the geometric tail (0 for n = 0, q^n for n ≥ 1). -/
def geomTailTerm (q : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else q ^ n

/-- For any $0 \le q \le 1$ and all $n : \mathbb{N}$, the theta tail term is bounded
by the geometric tail term: $q^{n^2} \le q^n$. -/
theorem thetaTailTerm_le_geomTailTerm {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (n : ℕ) :
    thetaTailTerm q n ≤ geomTailTerm q n := by
  unfold thetaTailTerm geomTailTerm
  split_ifs with hn
  · rfl
  · have hn_pos : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
    exact q_pow_sq_le_q_pow hq0 hq1 hn_pos

/-- Theta tail terms are non-negative for $q \ge 0$. -/
theorem thetaTailTerm_nonneg {q : ℝ} (hq0 : 0 ≤ q) (n : ℕ) :
    0 ≤ thetaTailTerm q n := by
  unfold thetaTailTerm
  split_ifs
  · rfl
  · exact pow_nonneg hq0 _

/-- Geometric tail terms are non-negative for $q \ge 0$. -/
theorem geomTailTerm_nonneg {q : ℝ} (hq0 : 0 ≤ q) (n : ℕ) :
    0 ≤ geomTailTerm q n := by
  unfold geomTailTerm
  split_ifs
  · rfl
  · exact pow_nonneg hq0 _

/-- The geometric tail series is summable for $0 \le q < 1$. -/
theorem summable_geomTailTerm {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (geomTailTerm q) := by
  have h_geom := summable_geometric_of_lt_one hq0 hq1
  have h_eq : geomTailTerm q = (fun n => if n = 0 then 0 else q ^ n) := rfl
  rw [h_eq]
  have h_diff : (fun n : ℕ => if n = 0 then 0 else q ^ n) =
                (fun n : ℕ => q ^ n) - (fun n : ℕ => if n = 0 then q ^ 0 else 0) := by
    ext n
    by_cases hn : n = 0
    · subst hn
      simp
    · simp [hn]
  rw [h_diff]
  exact h_geom.sub (hasSum_ite_eq 0 (q ^ 0)).summable

/-- By the comparison test, the infinite theta tail series is summable for $0 \le q < 1$. -/
theorem summable_thetaTailTerm {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (thetaTailTerm q) :=
  Summable.of_nonneg_of_le
    (thetaTailTerm_nonneg hq0)
    (fun n => thetaTailTerm_le_geomTailTerm hq0 hq1.le n)
    (summable_geomTailTerm hq0 hq1)

/-- The infinite theta tail sum is bounded by the infinite geometric tail sum. -/
theorem tsum_thetaTailTerm_le_tsum_geomTailTerm {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∑' n, thetaTailTerm q n) ≤ (∑' n, geomTailTerm q n) :=
  (summable_thetaTailTerm hq0 hq1).tsum_le_tsum
    (fun n => thetaTailTerm_le_geomTailTerm hq0 hq1.le n)
    (summable_geomTailTerm hq0 hq1)

/-- Exact sum of the geometric tail: $\sum_{n=1}^\infty q^n = \frac{q}{1-q}$. -/
theorem tsum_geomTailTerm_eq {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∑' n, geomTailTerm q n) = q / (1 - q) := by
  have h_geom := summable_geometric_of_lt_one hq0 hq1
  have h_geom_tsum := tsum_geometric_of_lt_one hq0 hq1
  have h_shift := h_geom.tsum_eq_zero_add
  have h_tail_shift := (summable_geomTailTerm hq0 hq1).tsum_eq_zero_add
  have h_term0 : geomTailTerm q 0 = 0 := rfl
  have h_term_succ : ∀ n : ℕ, geomTailTerm q (n + 1) = q ^ (n + 1) := fun n => rfl
  simp_rw [h_term_succ] at h_tail_shift
  rw [h_term0, zero_add] at h_tail_shift
  have hq0_pow : q ^ 0 = 1 := pow_zero q
  rw [hq0_pow] at h_shift
  rw [← h_tail_shift] at h_shift
  rw [h_geom_tsum] at h_shift
  have h_sub : (∑' n, geomTailTerm q n) = (1 - q)⁻¹ - 1 := by
    linarith [h_shift]
  rw [h_sub]
  have h_denom : 1 - q ≠ 0 := by linarith
  apply mul_right_cancel₀ h_denom
  rw [div_mul_cancel₀ _ h_denom]
  have h_inv : (1 - q)⁻¹ * (1 - q) = 1 := inv_mul_cancel₀ h_denom
  calc ((1 - q)⁻¹ - 1) * (1 - q)
    _ = (1 - q)⁻¹ * (1 - q) - 1 * (1 - q) := by ring
    _ = 1 - (1 - q) := by rw [h_inv, one_mul]
    _ = q := by ring

/-- The infinite theta tail sum is bounded by $q / (1 - q)$. -/
theorem tsum_thetaTailTerm_le_ratio {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∑' n, thetaTailTerm q n) ≤ q / (1 - q) := by
  have h_le := tsum_thetaTailTerm_le_tsum_geomTailTerm hq0 hq1
  rw [tsum_geomTailTerm_eq hq0 hq1] at h_le
  exact h_le

/-- Specialization to $q = e^{-\pi}$: The infinite theta tail is summable. -/
theorem summable_thetaTailTerm_exp_neg_pi :
    Summable (thetaTailTerm (Real.exp (-π))) := by
  have ⟨hpos, hlt⟩ := exp_neg_pi_pos_and_lt_one
  exact summable_thetaTailTerm hpos.le hlt

/-- The infinite theta tail for $e^{-\pi}$ is strictly bounded by $1/7$. -/
theorem tsum_thetaTailTerm_exp_neg_pi_lt_one_seventh :
    (∑' n, thetaTailTerm (Real.exp (-π)) n) < (1 : ℝ) / 7 := by
  have ⟨hpos, hlt⟩ := exp_neg_pi_pos_and_lt_one
  have h_le := tsum_thetaTailTerm_le_ratio hpos.le hlt
  have h_geom_seven := exp_neg_pi_geom_sum_lt_one_seventh
  exact lt_of_le_of_lt h_le h_geom_seven

/-- **Master Infinite Theta Tail Bound**:
The scaled infinite sum of the Jacobi theta tail is strictly less than $2/21 < 1$:
$$\frac{2}{\pi} \sum_{n=1}^\infty (e^{-\pi})^{n^2} < \frac{2}{21} < 1.$$ -/
theorem two_div_pi_mul_tsum_thetaTail_lt_two_twenty_firsts :
    (2 / π) * (∑' n, thetaTailTerm (Real.exp (-π)) n) < (2 : ℝ) / 21 := by
  have h_sev := tsum_thetaTailTerm_exp_neg_pi_lt_one_seventh
  have hpi : (3 : ℝ) < π := pi_gt_three_real
  have hpi_pos : 0 < π := by linarith
  have h_mul : (2 / π) * (∑' n, thetaTailTerm (Real.exp (-π)) n) < (2 / π) * (1 / 7) := by
    have h_coeff : (0 : ℝ) < 2 / π := div_pos (by norm_num) hpi_pos
    exact mul_lt_mul_of_pos_left h_sev h_coeff
  have h_alg : (2 / π) * (1 / (7 : ℝ)) < (2 : ℝ) / 21 := by
    have h_pi3 : (2 : ℝ) / π < 2 / 3 := by
      rw [div_lt_div_iff₀ hpi_pos (by norm_num)]
      linarith
    calc (2 / π) * (1 / 7)
        < (2 / 3) * (1 / 7) := by
          have : (0 : ℝ) < 1 / 7 := by norm_num
          exact mul_lt_mul_of_pos_right h_pi3 this
      _ = 2 / 21 := by norm_num
  exact lt_trans h_mul h_alg

/-- The scaled infinite sum of the Jacobi theta tail is strictly less than 1. -/
theorem two_div_pi_mul_tsum_thetaTail_lt_one :
    (2 / π) * (∑' n, thetaTailTerm (Real.exp (-π)) n) < 1 :=
  lt_trans two_div_pi_mul_tsum_thetaTail_lt_two_twenty_firsts two_twenty_firsts_lt_one

end RhG1Lean
