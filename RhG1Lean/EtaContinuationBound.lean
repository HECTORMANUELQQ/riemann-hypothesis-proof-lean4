/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import RhG1Lean.Eta
import RhG1Lean.LeftoverNonvanishing

/-!
# EtaContinuationBound: Universal Invertibility of the Dirichlet Eta Factor

This module formalizes the universal non-vanishing of the Dirichlet eta multiplier
 - 2^{1-s} \\ne 0$ for all complex numbers $ with $\\operatorname{Re}(s) < 1$.

## Key Result:
For all  \\in \\mathbb{C}$ with $\\operatorname{Re}(s) < 1$,
$\\zeta(s) = 0 \\iff \\eta(s) = 0$.
In particular, inside leftoverInterior, the non-vanishing of the Riemann zeta function
is identically equivalent to the non-vanishing of the Dirichlet eta function.
-/

open Real Complex Set

namespace RhG1Lean

/-- Norm of ^{1-s}$ is ^{1 - s.re}$. -/
theorem norm_two_cpow_one_sub (s : ℂ) :
    ‖(2 : ℂ) ^ (1 - s)‖ = (2 : ℝ) ^ (1 - s.re) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have h := Complex.norm_cpow_eq_rpow_re_of_pos h2 (1 - s)
  rw [sub_re, one_re] at h
  exact h

/-- For .re < 1$, the exponent  - s.re > 0$. -/
theorem one_sub_re_pos_of_re_lt_one {s : ℂ} (hs : s.re < 1) : 0 < 1 - s.re := by
  linarith

/-- For .re < 1$, ^{1 - s.re} > 1$. -/
theorem two_rpow_one_sub_re_gt_one {s : ℂ} (hs : s.re < 1) :
    1 < (2 : ℝ) ^ (1 - s.re) := by
  have h2 : (1 : ℝ) < 2 := by norm_num
  have hpos : 0 < 1 - s.re := one_sub_re_pos_of_re_lt_one hs
  exact Real.one_lt_rpow h2 hpos

/-- For .re < 1$, the norm $\|2^{1-s}\| > 1$. -/
theorem norm_two_cpow_one_sub_gt_one {s : ℂ} (hs : s.re < 1) :
    1 < ‖(2 : ℂ) ^ (1 - s)‖ := by
  rw [norm_two_cpow_one_sub]
  exact two_rpow_one_sub_re_gt_one hs

/-- Master Multiplier Theorem:
For any complex number $ with $\\operatorname{Re}(s) < 1$,  - 2^{1-s} \\ne 0$. -/
theorem dirichletEta_factor_ne_zero_of_re_lt_one {s : ℂ} (hs : s.re < 1) :
    1 - (2 : ℂ) ^ (1 - s) ≠ 0 := by
  intro hz
  have heq : (2 : ℂ) ^ (1 - s) = 1 := by
    linear_combination -hz
  have hnorm : ‖(2 : ℂ) ^ (1 - s)‖ = 1 := by rw [heq, norm_one]
  have hgt : 1 < ‖(2 : ℂ) ^ (1 - s)‖ := norm_two_cpow_one_sub_gt_one hs
  linarith

/-- For any complex number $ with $\\operatorname{Re}(s) < 1$,
$\\zeta(s) = 0 \\iff \\eta(s) = 0$. -/
theorem riemannZeta_eq_zero_iff_dirichletEta_eq_zero_of_re_lt_one {s : ℂ} (hs : s.re < 1) :
    riemannZeta s = 0 ↔ dirichletEta s = 0 := by
  unfold dirichletEta
  have hfac : 1 - (2 : ℂ) ^ (1 - s) ≠ 0 := dirichletEta_factor_ne_zero_of_re_lt_one hs
  simp [mul_eq_zero, hfac]

/-- Inside leftoverInterior,  - 2^{1-s} \\ne 0$. -/
theorem dirichletEta_factor_ne_zero_of_mem_leftoverInterior {s : ℂ} (hs : s ∈ leftoverInterior) :
    1 - (2 : ℂ) ^ (1 - s) ≠ 0 :=
  dirichletEta_factor_ne_zero_of_re_lt_one hs.2

/-- Inside leftoverInterior, $\\zeta(s) = 0 \\iff \\eta(s) = 0$. -/
theorem riemannZeta_eq_zero_iff_dirichletEta_eq_zero_of_mem_leftoverInterior
    {s : ℂ} (hs : s ∈ leftoverInterior) :
    riemannZeta s = 0 ↔ dirichletEta s = 0 :=
  riemannZeta_eq_zero_iff_dirichletEta_eq_zero_of_re_lt_one hs.2

end RhG1Lean
