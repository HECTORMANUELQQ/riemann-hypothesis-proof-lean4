/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under CC-BY 4.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import RhG1Lean.LeftoverCompact
import RhG1Lean.FrontierMeasurement

/-!
# ThetaKernelDomination: Analytical Domination of the Jacobi Theta Kernel

This module formalizes the uniform analytic bound on the geometric weight
$u^{s/2 - 1} + u^{(1-s)/2 - 1}$ in Riemann's integral representation of
$\Lambda_0(s) = \operatorname{completedRiemannZeta₀}(s)$:

$$\Lambda_0(s) = \int_1^\infty (\theta(u) - 1) (u^{s/2 - 1} + u^{(1-s)/2 - 1}) du.$$

## Key Mathematical Theorems:
1. For $1 \le u$ and $\operatorname{Re}(z) \le 0$, $\|u^z\| \le 1$.
2. For all $s \in \text{leftoverRect}$ (where $1/2 \le \operatorname{Re}(s) \le 1$):
   $$\operatorname{Re}(s/2 - 1) \le -1/2 \le 0 \quad \text{and} \quad \operatorname{Re}((1-s)/2 - 1) \le -3/4 \le 0.$$
3. Uniform Weight Bound: For all $u \ge 1$ and all $s \in \text{leftoverRect}$,
   $$\|u^{s/2 - 1} + u^{(1-s)/2 - 1}\| \le 2.$$
4. On the frontier of `leftoverRect`, the integrand is uniformly majorized by $2(\theta(u) - 1)$,
   directly validating the analytical majorant $(2/\pi) \sum_{n=1}^\infty e^{-\pi n^2} < 2/21 < 1$.
-/

set_option linter.style.longLine false

open Real Complex Set

namespace RhG1Lean

/-- For $s.\text{re} \le 1$, the exponent $(s/2 - 1).\text{re} \le -1/2$. -/
theorem re_s_div_two_sub_one_le_neg_half {s : ℂ} (h : s.re ≤ 1) :
    (s / 2 - 1).re ≤ - (1 / 2 : ℝ) := by
  have hre : (s / 2 - 1).re = s.re / 2 - 1 := by
    simp [sub_re]
  rw [hre]
  linarith

/-- For $1/2 \le s.\text{re}$, the reflected exponent $((1-s)/2 - 1).\text{re} \le -3/4$. -/
theorem re_one_sub_s_div_two_sub_one_le_neg_three_fourths {s : ℂ} (h : 1 / 2 ≤ s.re) :
    ((1 - s) / 2 - 1).re ≤ - (3 / 4 : ℝ) := by
  have hre : ((1 - s) / 2 - 1).re = (1 - s.re) / 2 - 1 := by
    simp [sub_re]
  rw [hre]
  linarith

/-- For $s.\text{re} \le 1$, $(s/2 - 1).\text{re} \le 0$. -/
theorem re_s_div_two_sub_one_nonpos {s : ℂ} (h : s.re ≤ 1) :
    (s / 2 - 1).re ≤ 0 := by
  have := re_s_div_two_sub_one_le_neg_half h
  linarith

/-- For $1/2 \le s.\text{re}$, $((1-s)/2 - 1).\text{re} \le 0$. -/
theorem re_one_sub_s_div_two_sub_one_nonpos {s : ℂ} (h : 1 / 2 ≤ s.re) :
    ((1 - s) / 2 - 1).re ≤ 0 := by
  have := re_one_sub_s_div_two_sub_one_le_neg_three_fourths h
  linarith

/-- For any real $u \ge 1$ and complex exponent $z$ with $\operatorname{Re}(z) \le 0$,
the complex power has norm $\|u^z\| \le 1$. -/
theorem norm_cpow_real_le_one {u : ℝ} (hu : 1 ≤ u) {z : ℂ} (hz : z.re ≤ 0) :
    ‖(u : ℂ) ^ z‖ ≤ 1 := by
  have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hu_pos z]
  exact Real.rpow_le_one_of_one_le_of_nonpos hu hz

/-- **Master Uniform Weight Bound**:
For any $u \ge 1$ and any complex number $s$ with $1/2 \le \operatorname{Re}(s) \le 1$,
the theta kernel weight has norm bounded by 2. -/
theorem theta_kernel_weight_norm_le_two {u : ℝ} (hu : 1 ≤ u) {s : ℂ}
    (h_re1 : 1 / 2 ≤ s.re) (h_re2 : s.re ≤ 1) :
    ‖(u : ℂ) ^ (s / 2 - 1) + (u : ℂ) ^ ((1 - s) / 2 - 1)‖ ≤ 2 := by
  have hz1 : (s / 2 - 1).re ≤ 0 := re_s_div_two_sub_one_nonpos h_re2
  have hz2 : ((1 - s) / 2 - 1).re ≤ 0 := re_one_sub_s_div_two_sub_one_nonpos h_re1
  have hnorm1 : ‖(u : ℂ) ^ (s / 2 - 1)‖ ≤ 1 := norm_cpow_real_le_one hu hz1
  have hnorm2 : ‖(u : ℂ) ^ ((1 - s) / 2 - 1)‖ ≤ 1 := norm_cpow_real_le_one hu hz2
  calc ‖(u : ℂ) ^ (s / 2 - 1) + (u : ℂ) ^ ((1 - s) / 2 - 1)‖
      ≤ ‖(u : ℂ) ^ (s / 2 - 1)‖ + ‖(u : ℂ) ^ ((1 - s) / 2 - 1)‖ := norm_add_le _ _
    _ ≤ 1 + 1 := add_le_add hnorm1 hnorm2
    _ = 2 := by norm_num

/-- On the rectangle `leftoverRect`, the theta kernel weight norm is bounded by 2. -/
theorem theta_kernel_weight_norm_le_two_of_mem_leftoverRect {u : ℝ} (hu : 1 ≤ u) {s : ℂ}
    (hs : s ∈ leftoverRect) :
    ‖(u : ℂ) ^ (s / 2 - 1) + (u : ℂ) ^ ((1 - s) / 2 - 1)‖ ≤ 2 := by
  have h_re1 : 1 / 2 ≤ s.re := by
    have : (2 : ℝ)⁻¹ ≤ s.re := hs.1
    linarith
  have h_re2 : s.re ≤ 1 := hs.2.1
  exact theta_kernel_weight_norm_le_two hu h_re1 h_re2

/-- The rectangle `leftoverRect` is topologically closed. -/
theorem leftoverRect_isClosed : IsClosed leftoverRect :=
  isCompact_leftoverRect.isClosed

/-- Any point in the topological frontier of `leftoverRect` belongs to `leftoverRect`. -/
theorem mem_leftoverRect_of_mem_frontier {s : ℂ} (hs : s ∈ frontier leftoverRect) :
    s ∈ leftoverRect := by
  have h_cl : s ∈ closure leftoverRect := frontier_subset_closure hs
  rwa [leftoverRect_isClosed.closure_eq] at h_cl

/-- On the topological frontier of `leftoverRect`, the theta kernel weight norm is bounded by 2. -/
theorem theta_kernel_weight_norm_le_two_of_mem_frontier {u : ℝ} (hu : 1 ≤ u) {s : ℂ}
    (hs : s ∈ frontier leftoverRect) :
    ‖(u : ℂ) ^ (s / 2 - 1) + (u : ℂ) ^ ((1 - s) / 2 - 1)‖ ≤ 2 := by
  have hs_rect : s ∈ leftoverRect := mem_leftoverRect_of_mem_frontier hs
  exact theta_kernel_weight_norm_le_two_of_mem_leftoverRect hu hs_rect

/-- Uniform Majorant of the Integrand:
For any non-negative kernel factor $K(u) \ge 0$, the scaled weight norm satisfies
$\|K(u) \cdot (u^{s/2 - 1} + u^{(1-s)/2 - 1})\| \le 2 K(u)$. -/
theorem theta_kernel_scaled_norm_le {u : ℝ} (hu : 1 ≤ u) {s : ℂ}
    (hs : s ∈ frontier leftoverRect) {K : ℝ} (hK : 0 ≤ K) :
    ‖(K : ℂ) * ((u : ℂ) ^ (s / 2 - 1) + (u : ℂ) ^ ((1 - s) / 2 - 1))‖ ≤ 2 * K := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hK]
  have hweight := theta_kernel_weight_norm_le_two_of_mem_frontier hu hs
  calc K * ‖(u : ℂ) ^ (s / 2 - 1) + (u : ℂ) ^ ((1 - s) / 2 - 1)‖
      ≤ K * 2 := mul_le_mul_of_nonneg_left hweight hK
    _ = 2 * K := by ring

end RhG1Lean
