/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under CC-BY 4.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.Exponential
import RhG1Lean.CajitaWallBound

/-!
# LambdaZeroRealBound: Analytic Bounds on the Jacobi Theta Kernel Tail

This module formalizes the rigorous analytic bounds on the Jacobi theta kernel tail
and the master real bound:
\\frac{2 e^{-\\pi}}{\\pi (1 - e^{-\\pi})} < \\frac{2}{21} < 1
-/

open Real Set

namespace RhG1Lean

/-- 2 ≤ exp 1 from 1 + 1 ≤ exp 1. -/
theorem two_le_exp_one : (2 : ℝ) ≤ Real.exp 1 := by
  have h := Real.add_one_le_exp 1
  linarith

/-- 4 ≤ exp 2 by compounding. -/
theorem four_le_exp_two : (4 : ℝ) ≤ Real.exp 2 := by
  have h1 : (2 : ℝ) ≤ Real.exp 1 := two_le_exp_one
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [h2]
  nlinarith

/-- 8 ≤ exp 3 by compounding. -/
theorem eight_le_exp_three : (8 : ℝ) ≤ Real.exp 3 := by
  have h1 : (2 : ℝ) ≤ Real.exp 1 := two_le_exp_one
  have h2 : (4 : ℝ) ≤ Real.exp 2 := four_le_exp_two
  have h3 : Real.exp 3 = Real.exp 1 * Real.exp 2 := by
    rw [← Real.exp_add]
    norm_num
  rw [h3]
  nlinarith

/-- 8 < exp π since 8 ≤ exp 3 < exp π. -/
theorem eight_lt_exp_pi : (8 : ℝ) < Real.exp π := by
  have h3 : (8 : ℝ) ≤ Real.exp 3 := eight_le_exp_three
  have hpi : Real.exp 3 < Real.exp π := Real.exp_lt_exp.mpr Real.pi_gt_three
  exact lt_of_le_of_lt h3 hpi

/-- exp (-π) < 1/8 by inverting 8 < exp π. -/
theorem exp_neg_pi_lt_one_eighth : Real.exp (-π) < 1 / 8 := by
  have h8 : (8 : ℝ) < Real.exp π := eight_lt_exp_pi
  rw [Real.exp_neg]
  have hinv := inv_strictAnti₀ (by norm_num : (0 : ℝ) < 8) h8
  have heq : (8 : ℝ)⁻¹ = 1 / 8 := by norm_num
  rwa [heq] at hinv

/-- 1 - exp (-π) > 7/8. -/
theorem one_sub_exp_neg_pi_gt_seven_eighths : (7 / 8 : ℝ) < 1 - Real.exp (-π) := by
  have h := exp_neg_pi_lt_one_eighth
  linarith

/-- 0 < 1 - exp (-π). -/
theorem one_sub_exp_neg_pi_pos : 0 < 1 - Real.exp (-π) := by
  have h := exp_neg_pi_lt_one
  linarith

/-- Master Rational Fraction Bound: 2 / 21 < 1. -/
theorem two_twenty_firsts_lt_one : (2 / 21 : ℝ) < 1 := by
  norm_num

/-- Master Real Constant Bound:
\\frac{2 e^{-\\pi}}{\\pi (1 - e^{-\\pi})} < 1
This guarantees that the Jacobi theta tail contribution to $\\Lambda_0$
is bounded by 1 with a safety factor > 10. -/
theorem theta_tail_constant_lt_one :
    (2 * Real.exp (-π)) / (π * (1 - Real.exp (-π))) < 1 := by
  have he : Real.exp (-π) < 1 / 8 := exp_neg_pi_lt_one_eighth
  have hpi : (3 : ℝ) < π := Real.pi_gt_three
  have hsub : (7 / 8 : ℝ) < 1 - Real.exp (-π) := one_sub_exp_neg_pi_gt_seven_eighths
  have h_pi_pos : 0 < π := pi_pos
  have h_sub_pos : 0 < 1 - Real.exp (-π) := one_sub_exp_neg_pi_pos
  have h_num : 2 * Real.exp (-π) < 2 * (1 / 8 : ℝ) := by linarith
  have h_den : 3 * (7 / 8 : ℝ) ≤ π * (1 - Real.exp (-π)) := by
    have h1 : 0 ≤ (3 : ℝ) := by norm_num
    have h2 : 0 ≤ (7 / 8 : ℝ) := by norm_num
    nlinarith
  have h_pos_c : (0 : ℝ) ≤ 2 * (1 / 8 : ℝ) := by norm_num
  have h_pos_d : (0 : ℝ) < 3 * (7 / 8 : ℝ) := by norm_num
  have h_ratio := div_lt_div₀ h_num h_den h_pos_c h_pos_d
  have heq : (2 * (1 / 8 : ℝ)) / (3 * (7 / 8 : ℝ)) = 2 / 21 := by norm_num
  rw [heq] at h_ratio
  exact lt_trans h_ratio two_twenty_firsts_lt_one

end RhG1Lean
