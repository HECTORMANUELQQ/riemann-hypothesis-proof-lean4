/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under CC-BY 4.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import RhG1Lean.CajitaMellinBridge
import RhG1Lean.ThetaInfiniteSeriesBound

/-!
# ThetaTailIntegralEvaluation: Explicit Integration of the Jacobi Theta Tail

This module proves the exact formula and bound for the improper integral of each
individual term in the Jacobi theta tail on [1, ∞):

$$\int_1^\infty e^{-\pi (n+1)^2 x} \, dx = \frac{e^{-\pi (n+1)^2}}{\pi (n+1)^2} \le \frac{1}{\pi} e^{-\pi (n+1)^2}.$$

Multiplying by 2 yields:
$$2 \int_1^\infty e^{-\pi (n+1)^2 x} \, dx \le \frac{2}{\pi} e^{-\pi (n+1)^2}.$$

Summed over n ≥ 0, this converges to:
$$\frac{2}{\pi} \sum_{n=1}^\infty (e^{-\pi})^{n^2} = \operatorname{canonicalThetaMajorant} < \frac{2}{21} < 1.$$
-/

set_option linter.style.longLine false

open Real Set

namespace RhG1Lean

/-- Exact Improper Integral of the n-th Theta Tail Term on (1, ∞):
$$\int_1^\infty e^{-\pi (n+1)^2 x} \, dx = \frac{e^{-\pi (n+1)^2}}{\pi (n+1)^2}.$$ -/
theorem integral_theta_term (n : ℕ) :
    ∫ (x : ℝ) in Ioi (1 : ℝ), exp (- (π * (n + 1 : ℝ)^2) * x) =
      exp (- (π * (n + 1 : ℝ)^2)) / (π * (n + 1 : ℝ)^2) := by
  have hpi : 0 < π := pi_pos
  have hn : 0 < (n + 1 : ℝ)^2 := sq_pos_of_pos (by positivity)
  have ha_pos : 0 < π * (n + 1 : ℝ)^2 := mul_pos hpi hn
  have ha : - (π * (n + 1 : ℝ)^2) < 0 := neg_lt_zero.mpr ha_pos
  have h := integral_exp_mul_Ioi ha 1
  rw [mul_one] at h
  rw [h]
  rw [neg_div_neg_eq]

/-- Uniform Upper Bound on the Integral of the n-th Theta Tail Term:
$$\int_1^\infty e^{-\pi (n+1)^2 x} \, dx \le \frac{1}{\pi} e^{-\pi (n+1)^2}.$$ -/
theorem integral_theta_term_le (n : ℕ) :
    ∫ (x : ℝ) in Ioi (1 : ℝ), exp (- (π * (n + 1 : ℝ)^2) * x) ≤
      (1 / π) * exp (- (π * (n + 1 : ℝ)^2)) := by
  rw [integral_theta_term n]
  have hpi : 0 < π := pi_pos
  have hn_ge : (1 : ℝ) ≤ (n + 1 : ℝ)^2 := by
    have : (1 : ℝ) ≤ (n + 1 : ℝ) := by
      have : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    nlinarith
  have h_denom : π ≤ π * (n + 1 : ℝ)^2 := by
    have := mul_le_mul_of_nonneg_left hn_ge hpi.le
    rwa [mul_one] at this
  have hexp_pos : 0 < exp (- (π * (n + 1 : ℝ)^2)) := exp_pos _
  rw [div_le_iff₀]
  · calc exp (- (π * (n + 1 : ℝ)^2))
        = (1 / π) * exp (- (π * (n + 1 : ℝ)^2)) * π := by
            have h_canc : π * (1 / π) = 1 := mul_one_div_cancel (ne_of_gt hpi)
            calc exp (- (π * (n + 1 : ℝ)^2))
                = 1 * exp (- (π * (n + 1 : ℝ)^2)) := by ring
              _ = (π * (1 / π)) * exp (- (π * (n + 1 : ℝ)^2)) := by rw [h_canc]
              _ = (1 / π) * exp (- (π * (n + 1 : ℝ)^2)) * π := by ring
      _ ≤ (1 / π) * exp (- (π * (n + 1 : ℝ)^2)) * (π * (n + 1 : ℝ)^2) := by
            refine mul_le_mul_of_nonneg_left h_denom ?_
            exact mul_nonneg (by positivity) hexp_pos.le
  · exact mul_pos hpi (sq_pos_of_pos (by positivity))

/-- Scaled Theta Tail Term Integral Bound:
$$2 \int_1^\infty e^{-\pi (n+1)^2 x} \, dx \le \frac{2}{\pi} e^{-\pi (n+1)^2}.$$ -/
theorem two_mul_integral_theta_term_le (n : ℕ) :
    2 * ∫ (x : ℝ) in Ioi (1 : ℝ), exp (- (π * (n + 1 : ℝ)^2) * x) ≤
      (2 / π) * exp (- (π * (n + 1 : ℝ)^2)) := by
  have h := integral_theta_term_le n
  calc 2 * ∫ (x : ℝ) in Ioi (1 : ℝ), exp (- (π * (n + 1 : ℝ)^2) * x)
      ≤ 2 * ((1 / π) * exp (- (π * (n + 1 : ℝ)^2))) := mul_le_mul_of_nonneg_left h (by norm_num)
    _ = (2 / π) * exp (- (π * (n + 1 : ℝ)^2)) := by ring

/-- Equality with the theta tail term evaluated at $e^{-\pi}$:
$$\frac{2}{\pi} e^{-\pi (n+1)^2} = \frac{2}{\pi} \operatorname{thetaTailTerm}(e^{-\pi})(n+1).$$ -/
theorem two_div_pi_mul_exp_eq_thetaTailTerm (n : ℕ) :
    (2 / π) * exp (- (π * (n + 1 : ℝ)^2)) =
      (2 / π) * thetaTailTerm (exp (-π)) (n + 1) := by
  unfold thetaTailTerm
  have hn1 : n + 1 ≠ 0 := Nat.succ_ne_zero n
  simp only [hn1, ↓reduceIte]
  have h := exp_nat_mul (-π) ((n + 1)^2)
  have h_comm : (((n + 1)^2 : ℕ) : ℝ) * (-π) = - (π * (n + 1 : ℝ)^2) := by
    push_cast
    ring
  rw [h_comm] at h
  rw [h]

/-- Universal strict bound by 2 / 21 on each integrated theta tail term:
$$2 \int_1^\infty e^{-\pi (n+1)^2 x} \, dx < \frac{2}{21} < 1.$$ -/
theorem two_mul_integral_theta_term_lt_two_twenty_firsts (n : ℕ) :
    2 * ∫ (x : ℝ) in Ioi (1 : ℝ), exp (- (π * (n + 1 : ℝ)^2) * x) < (2 : ℝ) / 21 := by
  have h_le := two_mul_integral_theta_term_le n
  have h_eq := two_div_pi_mul_exp_eq_thetaTailTerm n
  rw [h_eq] at h_le
  have h_pos : 0 ≤ exp (-π) := (exp_pos (-π)).le
  have h_term_le_tsum : thetaTailTerm (exp (-π)) (n + 1) ≤ ∑' k, thetaTailTerm (exp (-π)) k :=
    Summable.le_tsum summable_thetaTailTerm_exp_neg_pi (n + 1) (fun j _ => thetaTailTerm_nonneg h_pos j)
  have h2pi : 0 ≤ 2 / π := div_nonneg (by norm_num) pi_pos.le
  have h_maj : (2 / π) * thetaTailTerm (exp (-π)) (n + 1) ≤ canonicalThetaMajorant := by
    unfold canonicalThetaMajorant
    exact mul_le_mul_of_nonneg_left h_term_le_tsum h2pi
  have h_tot := lt_of_le_of_lt (le_trans h_le h_maj) canonicalThetaMajorant_lt_two_twenty_firsts
  exact h_tot

/-- Strict bound by 1 on each integrated theta tail term:
$$2 \int_1^\infty e^{-\pi (n+1)^2 x} \, dx < 1.$$ -/
theorem two_mul_integral_theta_term_lt_one (n : ℕ) :
    2 * ∫ (x : ℝ) in Ioi (1 : ℝ), exp (- (π * (n + 1 : ℝ)^2) * x) < 1 :=
  lt_trans (two_mul_integral_theta_term_lt_two_twenty_firsts n) two_twenty_firsts_lt_one

end RhG1Lean
