/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import RhG1Lean.Leftover
import RhG1Lean.XiEntire
import RhG1Lean.FrontierMeasurement

/-!
# CajitaPrefactorObstruction: Direct Algebraic Exclusion of Zeros in Room 1

This module proves that the prefactor (1-s)$ in the completion formula
\operatorname{entireXi}(s) - \frac{1}{2} = -\frac{s(1-s)}{2} \operatorname{completedRiemannZeta₀}(s)
has strictly sub-unitary norm everywhere on leftoverRect:
\|s(1-s)\|^2 \le \frac{5}{8} < 1.

Therefore, whenever $\|\operatorname{completedRiemannZeta₀}(s)\| \le 1$,
$\operatorname{entireXi}(s)$ cannot vanish anywhere on leftoverRect.
-/

set_option linter.style.longLine false

open Complex Real Set

namespace RhG1Lean

/-- Lemma relating complex norm squared to the sum of real and imaginary squares. -/
lemma norm_sq_eq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

/-- For any  \in \text{leftoverRect}$, $\|s\|^2 \le 5/4$. -/
theorem norm_sq_s_le_five_fourths {s : ℂ} (hs : s ∈ leftoverRect) :
    ‖s‖ ^ 2 ≤ (5 : ℝ) / 4 := by
  have hre : s.re ≤ 1 := hs.2.1
  have hre_pos : (0 : ℝ) ≤ s.re := by
    have : (2 : ℝ)⁻¹ ≤ s.re := hs.1
    linarith
  have him : |s.im| ≤ (1 / 2 : ℝ) := by
    have : |s.im| ≤ (2 : ℝ)⁻¹ := hs.2.2
    linarith
  have h_im_sq : s.im ^ 2 ≤ (1 / 4 : ℝ) := by
    have hpos : 0 ≤ |s.im| := abs_nonneg s.im
    have h1 : |s.im| ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
      nlinarith
    rw [sq_abs] at h1
    linarith
  have h_re_sq : s.re ^ 2 ≤ 1 := by
    nlinarith
  rw [norm_sq_eq]
  calc s.re ^ 2 + s.im ^ 2
      ≤ 1 + 1 / 4 := add_le_add h_re_sq h_im_sq
    _ = 5 / 4 := by norm_num

/-- For any  \in \text{leftoverRect}$, $\|1 - s\|^2 \le 1/2$. -/
theorem norm_sq_one_sub_s_le_half {s : ℂ} (hs : s ∈ leftoverRect) :
    ‖1 - s‖ ^ 2 ≤ (1 : ℝ) / 2 := by
  have hre1 : (1 / 2 : ℝ) ≤ s.re := by
    have : (2 : ℝ)⁻¹ ≤ s.re := hs.1
    linarith
  have hre2 : s.re ≤ 1 := hs.2.1
  have him : |s.im| ≤ (1 / 2 : ℝ) := by
    have : |s.im| ≤ (2 : ℝ)⁻¹ := hs.2.2
    linarith
  have h_re_sq : (1 - s.re) ^ 2 ≤ (1 / 4 : ℝ) := by
    nlinarith
  have h_im_sq : s.im ^ 2 ≤ (1 / 4 : ℝ) := by
    have hpos : 0 ≤ |s.im| := abs_nonneg s.im
    have h1 : |s.im| ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
      nlinarith
    rw [sq_abs] at h1
    linarith
  have h_sub_re : (1 - s).re = 1 - s.re := by simp
  have h_sub_im : (1 - s).im = - s.im := by simp
  rw [norm_sq_eq, h_sub_re, h_sub_im, neg_sq]
  calc (1 - s.re) ^ 2 + s.im ^ 2
      ≤ 1 / 4 + 1 / 4 := add_le_add h_re_sq h_im_sq
    _ = 1 / 2 := by norm_num

/-- **Master Prefactor Squared Bound**:
For any  \in \text{leftoverRect}$, $\|s(1-s)\|^2 \le 5/8$. -/
theorem norm_sq_mul_one_sub_le_five_eighths {s : ℂ} (hs : s ∈ leftoverRect) :
    ‖s * (1 - s)‖ ^ 2 ≤ (5 : ℝ) / 8 := by
  rw [norm_mul, mul_pow]
  have h1 := norm_sq_s_le_five_fourths hs
  have h2 := norm_sq_one_sub_s_le_half hs
  have h2_nonneg : 0 ≤ ‖1 - s‖ ^ 2 := sq_nonneg _
  calc ‖s‖ ^ 2 * ‖1 - s‖ ^ 2
      ≤ (5 / 4) * (1 / 2) := mul_le_mul h1 h2 h2_nonneg (by norm_num)
    _ = 5 / 8 := by norm_num

/-- The prefactor norm $\|s(1-s)\|$ is strictly less than 1 on leftoverRect. -/
theorem norm_mul_one_sub_lt_one {s : ℂ} (hs : s ∈ leftoverRect) :
    ‖s * (1 - s)‖ < 1 := by
  have h_sq := norm_sq_mul_one_sub_le_five_eighths hs
  have h_five_eighths_lt_one : (5 : ℝ) / 8 < 1 := by norm_num
  have h_lt : ‖s * (1 - s)‖ ^ 2 < 1 ^ 2 := by
    calc ‖s * (1 - s)‖ ^ 2 ≤ 5 / 8 := h_sq
      _ < 1 := h_five_eighths_lt_one
      _ = 1 ^ 2 := by norm_num
  have h_abs : |‖s * (1 - s)‖| < |(1 : ℝ)| := sq_lt_sq.mp h_lt
  rw [abs_norm, abs_of_pos (by norm_num)] at h_abs
  exact h_abs

/-- Half prefactor norm is strictly less than 1/2 on leftoverRect. -/
theorem norm_half_mul_one_sub_lt_half {s : ℂ} (hs : s ∈ leftoverRect) :
    ‖s * (1 - s) / 2‖ < (1 : ℝ) / 2 := by
  rw [norm_div]
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2]
  have h := norm_mul_one_sub_lt_one hs
  linarith

/-- The completion prefactor $\|s(s-1)/2\|$ is strictly less than 1/2 on leftoverRect. -/
theorem norm_prefactor_xi_lt_half {s : ℂ} (hs : s ∈ leftoverRect) :
    ‖s * (s - 1) / 2‖ < (1 : ℝ) / 2 := by
  have h_eq : s * (s - 1) / 2 = - (s * (1 - s) / 2) := by ring
  rw [h_eq, norm_neg]
  exact norm_half_mul_one_sub_lt_half hs

/-- Under $\|\operatorname{completedRiemannZeta₀}(s)\| \le 1$, the deviation
$\|\operatorname{entireXi}(s) - 1/2\|$ is strictly less than 1/2 on leftoverRect. -/
theorem entireXi_sub_half_lt_half_of_zeta₀_le_one {s : ℂ} (hs : s ∈ leftoverRect)
    (hM : ‖completedRiemannZeta₀ s‖ ≤ 1) :
    ‖entireXi s - 1 / 2‖ < (1 : ℝ) / 2 := by
  have h_diff : entireXi s - 1 / 2 = (s * (s - 1) / 2) * completedRiemannZeta₀ s := by
    unfold entireXi
    ring
  rw [h_diff, norm_mul]
  have hpref := norm_prefactor_xi_lt_half hs
  by_cases hzeta : ‖completedRiemannZeta₀ s‖ = 0
  · rw [hzeta, mul_zero]
    norm_num
  · calc ‖s * (s - 1) / 2‖ * ‖completedRiemannZeta₀ s‖
        ≤ ‖s * (s - 1) / 2‖ * 1 := mul_le_mul_of_nonneg_left hM (norm_nonneg _)
      _ = ‖s * (s - 1) / 2‖ := mul_one _
      _ < 1 / 2 := hpref

/-- Master Obstruction Theorem: On leftoverRect, whenever
$\|\operatorname{completedRiemannZeta₀}(s)\| \le 1$, $\operatorname{entireXi}(s) \ne 0$. -/
theorem entireXi_ne_zero_of_zeta₀_le_one_mem_leftoverRect {s : ℂ} (hs : s ∈ leftoverRect)
    (hM : ‖completedRiemannZeta₀ s‖ ≤ 1) :
    entireXi s ≠ 0 := by
  have hlt := entireXi_sub_half_lt_half_of_zeta₀_le_one hs hM
  exact entireXi_ne_zero_of_sub_half_lt hlt


/-- Master Obstruction Theorem for Zeta: On leftoverInterior, whenever
$\|\operatorname{completedRiemannZeta₀}(s)\| \le 1$, $\zeta(s) \ne 0$. -/
theorem riemannZeta_ne_zero_of_zeta₀_le_one_mem_leftoverInterior {s : ℂ}
    (hs : s ∈ leftoverInterior)
    (hM : ‖completedRiemannZeta₀ s‖ ≤ 1) :
    riemannZeta s ≠ 0 := by
  have hs_rect : s ∈ leftoverRect := (mem_leftoverInterior.mp hs).1
  have hxi := entireXi_ne_zero_of_zeta₀_le_one_mem_leftoverRect hs_rect hM
  intro hz
  have hxi_zero : entireXi s = 0 := (entireXi_eq_zero_iff_zeta_leftoverInterior hs).mpr hz
  exact hxi hxi_zero

end RhG1Lean
