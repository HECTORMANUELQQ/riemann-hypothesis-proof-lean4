/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import RhG1Lean.CajitaWallBound
import RhG1Lean.LambdaZeroRealBound

/-!
# ThetaTailGeometric: Geometric Series Majorization for the Jacobi Theta Tail

This module proves the rigorous majorization of the Jacobi theta tail sum:
$$\sum_{n=1}^N q^{n^2} \le \sum_{n=1}^N q^n < \frac{q}{1 - q}$$
for any $q \in (0, 1)$ and all finite truncations $N \ge 1$.

In particular, for $q = e^{-\pi}$, using the analytical bounds from `LambdaZeroRealBound`:
$$\frac{2}{\pi} \sum_{n=1}^N (e^{-\pi})^{n^2} < \frac{2}{21} < 1$$
uniformly for all $N \ge 1$, establishing that every finite approximation of the theta tail
strictly obeys the $M = 1$ Cajita bound with a $> 10\times$ safety margin.
-/

set_option linter.style.longLine false

open Real Finset

namespace RhG1Lean

/-- For any positive natural $n \ge 1$, $n \le n^2$. -/
theorem nat_le_sq (n : ℕ) (hn : 1 ≤ n) : n ≤ n ^ 2 := by
  calc n = n * 1 := (mul_one n).symm
  _ ≤ n * n := Nat.mul_le_mul_left n hn
  _ = n ^ 2 := (sq n).symm

/-- For $0 \le q \le 1$, if $n \le m$ then $q^m \le q^n$. -/
theorem pow_le_pow_of_le_one {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {n m : ℕ} (hnm : n ≤ m) :
    q ^ m ≤ q ^ n := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hnm
  induction d with
  | zero =>
    rw [Nat.add_zero]
  | succ d ih =>
    rw [Nat.add_succ, pow_succ]
    calc q ^ (n + d) * q ≤ q ^ (n + d) * 1 :=
      mul_le_mul_of_nonneg_left hq1 (pow_nonneg hq0 (n + d))
    _ = q ^ (n + d) := mul_one _
    _ ≤ q ^ n := ih (Nat.le_add_right n d)

/-- Termwise majorization of the theta exponent: for $0 \le q \le 1$ and $n \ge 1$, $q^{n^2} \le q^n$. -/
theorem q_pow_sq_le_q_pow {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    q ^ (n ^ 2) ≤ q ^ n :=
  pow_le_pow_of_le_one hq0 hq1 (nat_le_sq n hn)

/-- The $N$-th partial sum of the Jacobi theta tail $\sum_{n=1}^N q^{n^2}$. -/
noncomputable def thetaTailPartialSum (q : ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ Ico 1 (N + 1), q ^ (i ^ 2)

/-- The $N$-th partial sum of the ordinary geometric series $\sum_{n=1}^N q^n$. -/
noncomputable def geomTailPartialSum (q : ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ Ico 1 (N + 1), q ^ i

/-- Comparison theorem: for $0 \le q \le 1$, the theta tail is bounded by the geometric tail. -/
theorem thetaTailPartialSum_le_geomTailPartialSum {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (N : ℕ) :
    thetaTailPartialSum q N ≤ geomTailPartialSum q N := by
  unfold thetaTailPartialSum geomTailPartialSum
  apply sum_le_sum
  intro i hi
  rw [mem_Ico] at hi
  exact q_pow_sq_le_q_pow hq0 hq1 hi.1

/-- Exact formula for the finite geometric tail sum $\sum_{i=1}^N q^i = \frac{q - q^{N+1}}{1 - q}$. -/
theorem geomTailPartialSum_eq {q : ℝ} (hq_ne : q ≠ 1) (N : ℕ) :
    geomTailPartialSum q N = (q - q ^ (N + 1)) / (1 - q) := by
  unfold geomTailPartialSum
  have h_le : 1 ≤ N + 1 := Nat.succ_le_succ (Nat.zero_le N)
  have h := geom_sum_Ico' hq_ne h_le
  rw [pow_one] at h
  exact h

/-- For $0 < q < 1$ and $N \ge 1$, the geometric tail sum is strictly less than $q / (1 - q)$. -/
theorem geomTailPartialSum_lt {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {N : ℕ} (_hN : 1 ≤ N) :
    geomTailPartialSum q N < q / (1 - q) := by
  have hq_ne : q ≠ 1 := ne_of_lt hq1
  rw [geomTailPartialSum_eq hq_ne N]
  have h_den : 0 < 1 - q := by linarith
  have h_pow_pos : 0 < q ^ (N + 1) := pow_pos hq0 (N + 1)
  have h_num : q - q ^ (N + 1) < q := by linarith
  exact div_lt_div_of_pos_right h_num h_den

/-- **Master Theta Tail Majorization Bound**:
For any $0 < q < 1$ and $N \ge 1$, the theta tail partial sum satisfies:
$$\sum_{n=1}^N q^{n^2} < \frac{q}{1 - q}.$$ -/
theorem thetaTailPartialSum_lt_of_lt_one {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {N : ℕ} (hN : 1 ≤ N) :
    thetaTailPartialSum q N < q / (1 - q) := by
  have h_le := thetaTailPartialSum_le_geomTailPartialSum (le_of_lt hq0) (le_of_lt hq1) N
  have h_lt := geomTailPartialSum_lt hq0 hq1 hN
  exact lt_of_le_of_lt h_le h_lt

/-- The parameter $q = e^{-\pi}$ satisfies $0 < e^{-\pi} < 1$. -/
theorem exp_neg_pi_pos_and_lt_one : 0 < Real.exp (-π) ∧ Real.exp (-π) < 1 :=
  ⟨Real.exp_pos (-π), exp_neg_pi_lt_one⟩

/-- For $q = e^{-\pi}$, the geometric majorant satisfies $q / (1 - q) < 1 / 7$. -/
theorem exp_neg_pi_geom_sum_lt_one_seventh :
    Real.exp (-π) / (1 - Real.exp (-π)) < (1 : ℝ) / 7 := by
  have h_exp := exp_neg_pi_lt_one_eighth
  have h_sub := one_sub_exp_neg_pi_gt_seven_eighths
  have h_exp_pos := Real.exp_pos (-π)
  have h_sub_pos : 0 < 1 - Real.exp (-π) := by linarith
  have h1 : Real.exp (-π) / (1 - Real.exp (-π)) < (1 / 8 : ℝ) / (1 - Real.exp (-π)) :=
    div_lt_div_of_pos_right h_exp h_sub_pos
  have h2 : (1 / 8 : ℝ) / (1 - Real.exp (-π)) < (1 / 8 : ℝ) / (7 / 8 : ℝ) := by
    rw [div_lt_div_iff₀ h_sub_pos (by norm_num)]
    linarith
  have h3 : (1 / 8 : ℝ) / (7 / 8 : ℝ) = (1 : ℝ) / 7 := by norm_num
  linarith

/-- **Numerical Theta Tail Bound**:
For all $N \ge 1$, the theta tail sum $\sum_{n=1}^N (e^{-\pi})^{n^2} < 1/7$. -/
theorem thetaTailPartialSum_exp_neg_pi_lt_one_seventh {N : ℕ} (hN : 1 ≤ N) :
    thetaTailPartialSum (Real.exp (-π)) N < (1 : ℝ) / 7 := by
  have hq := exp_neg_pi_pos_and_lt_one
  have h_lt := thetaTailPartialSum_lt_of_lt_one hq.1 hq.2 hN
  exact lt_trans h_lt exp_neg_pi_geom_sum_lt_one_seventh

/-- **Master Uniform Theta Tail Bound for Cajita Walls**:
For all finite truncations $N \ge 1$:
$$\frac{2}{\pi} \sum_{n=1}^N (e^{-\pi})^{n^2} < \frac{2}{21} < 1.$$ -/
theorem two_div_pi_mul_thetaTailPartialSum_lt_two_twenty_firsts {N : ℕ} (hN : 1 ≤ N) :
    (2 / π) * thetaTailPartialSum (Real.exp (-π)) N < (2 : ℝ) / 21 := by
  have h_sum := thetaTailPartialSum_exp_neg_pi_lt_one_seventh hN
  have hpi : 3 < π := pi_gt_three_real
  have hpi_pos : 0 < π := by linarith
  have h_two_pi : (2 : ℝ) / π < (2 : ℝ) / 3 := by
    rw [div_lt_div_iff₀ hpi_pos (by norm_num)]
    linarith
  have h_mul : (2 / π) * thetaTailPartialSum (Real.exp (-π)) N < (2 / 3 : ℝ) * (1 / 7 : ℝ) := by
    have h_sum_pos : 0 ≤ thetaTailPartialSum (Real.exp (-π)) N := by
      unfold thetaTailPartialSum
      exact sum_nonneg (fun i _ => pow_nonneg (le_of_lt (Real.exp_pos (-π))) (i ^ 2))
    have h23_pos : (0 : ℝ) < 2 / 3 := by norm_num
    calc (2 / π) * thetaTailPartialSum (Real.exp (-π)) N
      _ ≤ (2 / 3) * thetaTailPartialSum (Real.exp (-π)) N :=
        mul_le_mul_of_nonneg_right (le_of_lt h_two_pi) h_sum_pos
      _ < (2 / 3) * (1 / 7) :=
        mul_lt_mul_of_pos_left h_sum h23_pos
  have h_const : (2 / 3 : ℝ) * (1 / 7 : ℝ) = (2 : ℝ) / 21 := by norm_num
  rw [h_const] at h_mul
  exact h_mul

/-- Uniform satisfaction of the $M = 1$ safety barrier by all theta tail partial sums:
$$\frac{2}{\pi} \sum_{n=1}^N (e^{-\pi})^{n^2} < 1.$$ -/
theorem two_div_pi_mul_thetaTailPartialSum_lt_one {N : ℕ} (hN : 1 ≤ N) :
    (2 / π) * thetaTailPartialSum (Real.exp (-π)) N < 1 := by
  have h := two_div_pi_mul_thetaTailPartialSum_lt_two_twenty_firsts hN
  have h21 := two_twenty_firsts_lt_one
  exact lt_trans h h21

end RhG1Lean
