/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Group.Basic
import RhG1Lean.KroneckerMismatch
import RhG1Lean.BocaADualCancellation
import RhG1Lean.BocaANonvanishing
import RhG1Lean.PrimeRemainderBound

/-!
# Prime2LinearGap: Linear Quantitative Lower Bound for Prime-2 Dual Mismatch

This module establishes an explicit, quantitative lower bound on the prime-2 gain ratio gap
$|r_2(\delta) - 1|$ in terms of the displacement $|\delta|$ from the critical line:

$$|r_2(\delta) - 1| \ge |\delta| \log 2 \quad \text{for all } \delta \in [-1/2, 1/2] \setminus \{0\}.$$

## Mathematical Rationale:
1. When $\delta < 0$: $r_2(\delta) = e^{-2\delta \log 2} > 1$, and since $e^x - 1 \ge x$,
   $r_2(\delta) - 1 \ge -2\delta \log 2 = 2|\delta| \log 2 \ge |\delta| \log 2$.
2. When $0 < \delta \le 1/2$: $r_2(\delta) = e^{-2\delta \log 2} < 1$, and
   $1 - r_2(\delta) = \frac{e^{2\delta \log 2} - 1}{e^{2\delta \log 2}} \ge \frac{2\delta \log 2}{2} = |\delta| \log 2$.
3. As a corollary, inside the critical strip $0 < \operatorname{Re}(s) < 1$ with $\operatorname{Re}(s) \ne 1/2$,
   the prime-2 gap is strictly bounded below by $|\delta| \log 2 > 0$.
-/

set_option linter.style.longLine false

open Real Complex Set

namespace RhG1Lean

/-- Elementary convexity inequality for real exponential: $x \le e^x - 1$. -/
theorem exp_sub_one_ge (x : ℝ) : x ≤ Real.exp x - 1 := by
  have h := Real.add_one_le_exp x
  linarith

/-- For $\delta < 0$, the prime-2 gain ratio exceeds 1 by at least $2(-\delta)\log 2$. -/
theorem primeDualGainRatio_sub_one_ge_of_neg {δ : ℝ} (_hδ : δ < 0) :
    2 * (-δ) * Real.log 2 ≤ primeDualGainRatio δ - 1 := by
  unfold primeDualGainRatio
  have h := exp_sub_one_ge (-2 * δ * Real.log 2)
  have hy : -2 * δ * Real.log 2 = 2 * (-δ) * Real.log 2 := by ring
  linarith

/-- For $0 < \delta \le 1/2$, the exponent $y = 2\delta \log 2$ satisfies $e^y \le 2$. -/
theorem exp_two_mul_delta_log_two_le_two {δ : ℝ} (hδ_le : δ ≤ 1 / 2) :
    Real.exp (2 * δ * Real.log 2) ≤ 2 := by
  have hlog : 0 < Real.log 2 := log_two_pos
  have h_le : 2 * δ * Real.log 2 ≤ Real.log 2 := by
    calc 2 * δ * Real.log 2 = (2 * δ) * Real.log 2 := by ring
    _ ≤ 1 * Real.log 2 := by
      have : 2 * δ ≤ 1 := by linarith
      exact mul_le_mul_of_nonneg_right this (le_of_lt hlog)
    _ = Real.log 2 := by ring
  have hexp := Real.exp_le_exp.mpr h_le
  have h2 : (0 : ℝ) < 2 := by norm_num
  rw [Real.exp_log h2] at hexp
  exact hexp

/-- For $0 < \delta \le 1/2$, $1 - r_2(\delta) \ge \delta \log 2$. -/
theorem one_sub_primeDualGainRatio_ge_of_pos {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1 / 2) :
    δ * Real.log 2 ≤ 1 - primeDualGainRatio δ := by
  unfold primeDualGainRatio
  set y := 2 * δ * Real.log 2
  have hlog : 0 < Real.log 2 := log_two_pos
  have hy_pos : 0 < y := by
    have : 0 < 2 * δ := by linarith
    exact mul_pos this hlog
  set E := Real.exp y
  have hexp_le : E ≤ 2 := exp_two_mul_delta_log_two_le_two hδ_le
  have hexp_pos : 0 < E := Real.exp_pos y
  have h_sub : y ≤ E - 1 := exp_sub_one_ge y
  have h_exp_neg : Real.exp (-2 * δ * Real.log 2) = E⁻¹ := by
    have : -2 * δ * Real.log 2 = -y := by ring
    rw [this, Real.exp_neg]
  rw [h_exp_neg]
  have hE_ne : E ≠ 0 := ne_of_gt hexp_pos
  have h_div : 1 - E⁻¹ = (E - 1) / E := by
    field_simp [hE_ne]
  rw [h_div]
  have h_two_pos : (0 : ℝ) < 2 := by norm_num
  have h_mul_le : y * E ≤ 2 * (E - 1) := by
    have h1 : y * E ≤ (E - 1) * 2 :=
      mul_le_mul h_sub hexp_le (le_of_lt hexp_pos) (by linarith)
    linarith
  have h_frac : y / 2 ≤ (E - 1) / E := by
    rw [div_le_div_iff₀ h_two_pos hexp_pos]
    linarith
  have hy_half : y / 2 = δ * Real.log 2 := by
    calc y / 2 = (2 * δ * Real.log 2) / 2 := rfl
    _ = δ * Real.log 2 := by ring
  rw [hy_half] at h_frac
  exact h_frac

/-- For $\delta < 0$, $|r_2(\delta) - 1| \ge |\delta| \log 2$. -/
theorem abs_primeDualGainRatio_sub_one_ge_of_neg {δ : ℝ} (hδ : δ < 0) :
    |δ| * Real.log 2 ≤ |primeDualGainRatio δ - 1| := by
  have hgt : 1 < primeDualGainRatio δ := primeDualGainRatio_gt_one_of_neg hδ
  have habs : |primeDualGainRatio δ - 1| = primeDualGainRatio δ - 1 :=
    abs_of_pos (sub_pos_of_lt hgt)
  rw [habs]
  have h_ge := primeDualGainRatio_sub_one_ge_of_neg hδ
  have h_abs_delta : |δ| = -δ := abs_of_neg hδ
  rw [h_abs_delta]
  have hlog : 0 < Real.log 2 := log_two_pos
  have h1 : -δ * Real.log 2 ≤ 2 * (-δ) * Real.log 2 := by
    have hle : -δ ≤ 2 * (-δ) := by linarith
    exact mul_le_mul_of_nonneg_right hle (le_of_lt hlog)
  linarith

/-- For $0 < \delta \le 1/2$, $|r_2(\delta) - 1| \ge |\delta| \log 2$. -/
theorem abs_primeDualGainRatio_sub_one_ge_of_pos {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1 / 2) :
    |δ| * Real.log 2 ≤ |primeDualGainRatio δ - 1| := by
  have hlt : primeDualGainRatio δ < 1 := primeDualGainRatio_lt_one_of_pos hδ_pos
  have h_neg : primeDualGainRatio δ - 1 < 0 := sub_neg_of_lt hlt
  have habs : |primeDualGainRatio δ - 1| = -(primeDualGainRatio δ - 1) := abs_of_neg h_neg
  rw [habs]
  have h_ring : -(primeDualGainRatio δ - 1) = 1 - primeDualGainRatio δ := by ring
  rw [h_ring]
  have h_ge := one_sub_primeDualGainRatio_ge_of_pos hδ_pos hδ_le
  have h_abs_delta : |δ| = δ := abs_of_pos hδ_pos
  rw [h_abs_delta]
  exact h_ge

/-- **Master Linear Gap Theorem**:
For all $\delta \in [-1/2, 1/2] \setminus \{0\}$, the prime-2 gain ratio mismatch
satisfies $|r_2(\delta) - 1| \ge |\delta| \log 2$. -/
theorem primeDualGainRatio_gap_ge_linear {δ : ℝ}
    (hδ_mem : δ ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) (hδ_ne : δ ≠ 0) :
    |δ| * Real.log 2 ≤ |primeDualGainRatio δ - 1| := by
  rcases lt_or_gt_of_ne hδ_ne with hneg | hpos
  · exact abs_primeDualGainRatio_sub_one_ge_of_neg hneg
  · exact abs_primeDualGainRatio_sub_one_ge_of_pos hpos hδ_mem.2

/-- The linear lower bound $|\delta| \log 2$ is strictly positive for any $\delta \ne 0$. -/
theorem primeDualGainRatio_linear_bound_pos {δ : ℝ} (hδ_ne : δ ≠ 0) :
    0 < |δ| * Real.log 2 := by
  have habs : 0 < |δ| := abs_pos.mpr hδ_ne
  have hlog : 0 < Real.log 2 := log_two_pos
  exact mul_pos habs hlog

/-- **Critical Strip Linear Gap**:
For any point $s$ in the critical strip $0 < \operatorname{Re}(s) < 1$ with $\operatorname{Re}(s) \ne 1/2$,
the prime-2 gap satisfies $|r_2(\delta) - 1| \ge |\delta| \log 2$. -/
theorem primeDualGainRatio_gap_ge_linear_of_mem_strip {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (hne : s.re ≠ 1 / 2) :
    |s.re - 1 / 2| * Real.log 2 ≤ |primeDualGainRatio (s.re - 1 / 2) - 1| := by
  have hδ_mem : s.re - 1 / 2 ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) := ⟨by linarith, by linarith⟩
  have hδ_ne : s.re - 1 / 2 ≠ 0 := sub_ne_zero.mpr hne
  exact primeDualGainRatio_gap_ge_linear hδ_mem hδ_ne

/-- Sufficient condition for `HasPrime2DualDominance` via the linear quantitative gap:
if $\|R\| < (|\delta| \log 2) A_2$, then $w$ has prime-2 dual dominance. -/
theorem hasPrime2DualDominance_of_linear_bound {w : ℂ} {δ A₂ : ℝ}
    (hδ_mem : δ ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) (hδ_ne : δ ≠ 0) (hA₂ : 0 < A₂)
    (ψ θ : ℝ) (R : ℂ)
    (hR : ‖R‖ < (|δ| * Real.log 2) * A₂)
    (hw : w = ((primeDualGainRatio δ * A₂ : ℝ) : ℂ) * channelWave (-θ) +
              (A₂ : ℂ) * channelWave (-2 * ψ + θ) + R) :
    HasPrime2DualDominance w δ := by
  refine ⟨A₂, hA₂, ψ, θ, R, ?_, hw⟩
  have hgap := primeDualGainRatio_gap_ge_linear hδ_mem hδ_ne
  have hmul : (|δ| * Real.log 2) * A₂ ≤ |primeDualGainRatio δ - 1| * A₂ :=
    mul_le_mul_of_nonneg_right hgap (le_of_lt hA₂)
  exact lt_of_lt_of_le hR hmul

/-- Non-vanishing theorem under the linear quantitative bound:
if $\|R\| < (|\delta| \log 2) A_2$, the composite wave is strictly non-zero. -/
theorem ne_zero_of_linear_bound {w : ℂ} {δ A₂ : ℝ}
    (hδ_mem : δ ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) (hδ_ne : δ ≠ 0) (hA₂ : 0 < A₂)
    (ψ θ : ℝ) (R : ℂ)
    (hR : ‖R‖ < (|δ| * Real.log 2) * A₂)
    (hw : w = ((primeDualGainRatio δ * A₂ : ℝ) : ℂ) * channelWave (-θ) +
              (A₂ : ℂ) * channelWave (-2 * ψ + θ) + R) :
    w ≠ 0 := by
  have hdom := hasPrime2DualDominance_of_linear_bound hδ_mem hδ_ne hA₂ ψ θ R hR hw
  exact ne_zero_of_hasPrime2DualDominance hδ_ne hdom

end RhG1Lean
