/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Kronecker Gain Mismatch and Asymmetric Dual Cancellation

From `brief_cancelacion_dual.md` §3, §8:
Outside the critical line ($\delta \ne 0$), the ratio of West to East gains
$$r(\delta, \tau) = (\tau/\tau_*)^{\delta / \mu_\circ}$$
$$= \exp( (\delta / \mu_\circ) \log(\tau / \tau_*) )$$

Key theorems proved:
1. `two_vectors_sum_ne_zero_of_norm_ne`: Universal geometric barrier.
   Two vectors with strictly unequal norms can NEVER cancel each other:
   $\|v_1\| \ne \|v_2\| \implies v_1 + v_2 \ne 0$.
2. `channelGainRatio_eq_one_iff`: The gain ratio equals 1 if and only if
   $\delta = 0$ (on the critical line) or $\tau = \tau_*$.
3. `channelGainRatio_ne_one_of_delta_ne_zero`: For any $\tau \ne \tau_*$ and $\delta \ne 0$,
   $r(\delta, \tau) \ne 1$.
4. Strict dominance regimes:
   - $\delta > 0 \wedge \tau > \tau_* \implies r(\delta, \tau) > 1$ (West array dominates).
   - $\delta < 0 \wedge \tau > \tau_* \implies r(\delta, \tau) < 1$ (East array dominates).
-/

set_option linter.style.longLine false

open Real

namespace RhG1Lean

/-- **Universal Geometric Barrier**: Two vectors with unequal norms cannot sum to zero. -/
theorem two_vectors_sum_ne_zero_of_norm_ne {E : Type*} [SeminormedAddCommGroup E]
    {v₁ v₂ : E} (h : ‖v₁‖ ≠ ‖v₂‖) : v₁ + v₂ ≠ 0 := by
  intro hsum
  have heq : v₁ = -v₂ := eq_neg_of_add_eq_zero_left hsum
  have hnorm : ‖v₁‖ = ‖v₂‖ := by
    rw [heq, norm_neg]
  exact h hnorm

/-- The gain ratio between West and East arrays in the slowest channel $\omega_*$. -/
noncomputable def channelGainRatio (δ τ τ_star μ₀ : ℝ) : ℝ :=
  Real.exp ((δ / μ₀) * Real.log (τ / τ_star))

/-- The gain ratio is always strictly positive. -/
theorem channelGainRatio_pos (δ τ τ_star μ₀ : ℝ) :
    0 < channelGainRatio δ τ τ_star μ₀ :=
  Real.exp_pos _

/-- At the critical line $\delta = 0$, the gain ratio is identically 1 for all $\tau > 0$. -/
@[simp]
theorem channelGainRatio_zero (τ τ_star μ₀ : ℝ) :
    channelGainRatio 0 τ τ_star μ₀ = 1 := by
  simp [channelGainRatio]

/-- At the crossover time $\tau = \tau_*$, the gain ratio is 1 for all $\delta$. -/
theorem channelGainRatio_at_tau_star (δ τ_star μ₀ : ℝ) (h_star : 0 < τ_star) :
    channelGainRatio δ τ_star τ_star μ₀ = 1 := by
  unfold channelGainRatio
  have : τ_star / τ_star = 1 := div_self (ne_of_gt h_star)
  rw [this, Real.log_one, mul_zero, Real.exp_zero]

/-- **Kronecker Gain Mismatch Theorem**:
For $\mu_0 > 0$, $\tau > 0$, $\tau_* > 0$, the gain ratio equals 1 IF AND ONLY IF
$\delta = 0$ (the critical line) or $\tau = \tau_*$. -/
theorem channelGainRatio_eq_one_iff {δ τ τ_star μ₀ : ℝ}
    (hτ : 0 < τ) (h_star : 0 < τ_star) (hμ₀ : 0 < μ₀) :
    channelGainRatio δ τ τ_star μ₀ = 1 ↔ δ = 0 ∨ τ = τ_star := by
  unfold channelGainRatio
  rw [Real.exp_eq_one_iff]
  have hdiv_pos : 0 < τ / τ_star := div_pos hτ h_star
  constructor
  · intro hmul
    cases mul_eq_zero.mp hmul with
    | inl h1 =>
      have : δ = 0 := by
        have : δ / μ₀ * μ₀ = 0 * μ₀ := by rw [h1]
        rw [div_mul_cancel₀ δ (ne_of_gt hμ₀), zero_mul] at this
        exact this
      exact Or.inl this
    | inr h2 =>
      rw [Real.log_eq_zero] at h2
      rcases h2 with h2 | h2 | h2
      · linarith [hdiv_pos]
      · have : τ = τ_star := by
          have : (τ / τ_star) * τ_star = 1 * τ_star := by rw [h2]
          rw [div_mul_cancel₀ τ (ne_of_gt h_star), one_mul] at this
          exact this
        exact Or.inr this
      · linarith [hdiv_pos]
  · intro h
    cases h with
    | inl hδ =>
      simp [hδ]
    | inr hτ_eq =>
      have : τ / τ_star = 1 := by rw [hτ_eq, div_self (ne_of_gt h_star)]
      rw [this, Real.log_one, mul_zero]

/-- **Strict Asymmetry Off the Critical Line**:
For any off-line perturbation $\delta \ne 0$ and any time $\tau \ne \tau_*$,
the gain ratio is strictly different from 1. -/
theorem channelGainRatio_ne_one_of_delta_ne_zero {δ τ τ_star μ₀ : ℝ}
    (hτ : 0 < τ) (h_star : 0 < τ_star) (hμ₀ : 0 < μ₀)
    (hδ : δ ≠ 0) (h_tau_ne : τ ≠ τ_star) :
    channelGainRatio δ τ τ_star μ₀ ≠ 1 := by
  intro heq
  rw [channelGainRatio_eq_one_iff hτ h_star hμ₀] at heq
  cases heq with
  | inl h1 => exact hδ h1
  | inr h2 => exact h_tau_ne h2

/-- **West Array Dominance**: If $\delta > 0$ and $\tau > \tau_*$, the ratio $r > 1$. -/
theorem channelGainRatio_gt_one_of_pos {δ τ τ_star μ₀ : ℝ}
    (h_star : 0 < τ_star) (hμ₀ : 0 < μ₀)
    (hδ : 0 < δ) (hτ : τ_star < τ) :
    1 < channelGainRatio δ τ τ_star μ₀ := by
  unfold channelGainRatio
  rw [Real.one_lt_exp_iff]
  have h1 : 0 < δ / μ₀ := div_pos hδ hμ₀
  have hdiv_gt : 1 < τ / τ_star := (one_lt_div h_star).mpr hτ
  have h2 : 0 < Real.log (τ / τ_star) := Real.log_pos hdiv_gt
  exact mul_pos h1 h2

/-- **East Array Dominance**: If $\delta < 0$ and $\tau > \tau_*$, the ratio $r < 1$. -/
theorem channelGainRatio_lt_one_of_neg {δ τ τ_star μ₀ : ℝ}
    (h_star : 0 < τ_star) (hμ₀ : 0 < μ₀)
    (hδ : δ < 0) (hτ : τ_star < τ) :
    channelGainRatio δ τ τ_star μ₀ < 1 := by
  unfold channelGainRatio
  rw [Real.exp_lt_one_iff]
  have h1 : δ / μ₀ < 0 := div_neg_of_neg_of_pos hδ hμ₀
  have hdiv_gt : 1 < τ / τ_star := (one_lt_div h_star).mpr hτ
  have h2 : 0 < Real.log (τ / τ_star) := Real.log_pos hdiv_gt
  exact mul_neg_of_neg_of_pos h1 h2

/-- **Universal Dominance Barrier**: If the remainder $\|R\| < \|v\|$, then $v + R \ne 0$.
The leading mode cannot be cancelled by a strictly smaller remainder. -/
theorem vector_add_remainder_ne_zero_of_norm_lt {E : Type*} [SeminormedAddCommGroup E]
    {v R : E} (h : ‖R‖ < ‖v‖) : v + R ≠ 0 := by
  intro hsum
  have heq : v = -R := eq_neg_of_add_eq_zero_left hsum
  have hnorm : ‖v‖ = ‖R‖ := by rw [heq, norm_neg]
  linarith

/-- **Triangle Inequality Lower Bound**: $\|v + R\| \ge \|v\| - \|R\|$. -/
theorem norm_add_lower_bound {E : Type*} [SeminormedAddCommGroup E] (v R : E) :
    ‖v‖ - ‖R‖ ≤ ‖v + R‖ := by
  have h := norm_sub_norm_le v (-R)
  rw [norm_neg] at h
  have heq : v - (-R) = v + R := sub_neg_eq_add v R
  rwa [heq] at h

/-- **Monotonic Gain Amplification**: For $\delta > 0$, the West/East gain ratio is
strictly increasing with height $\tau > 0$. The mismatch amplifies as $\tau$ grows. -/
theorem channelGainRatio_lt_channelGainRatio_of_lt {δ τ₁ τ₂ τ_star μ₀ : ℝ}
    (h_star : 0 < τ_star) (hμ₀ : 0 < μ₀) (hδ : 0 < δ)
    (hτ₁ : 0 < τ₁) (hlt : τ₁ < τ₂) :
    channelGainRatio δ τ₁ τ_star μ₀ < channelGainRatio δ τ₂ τ_star μ₀ := by
  unfold channelGainRatio
  rw [Real.exp_lt_exp]
  have h1 : 0 < δ / μ₀ := div_pos hδ hμ₀
  have hdiv_lt : τ₁ / τ_star < τ₂ / τ_star := div_lt_div_of_pos_right hlt h_star
  have hdiv₁_pos : 0 < τ₁ / τ_star := div_pos hτ₁ h_star
  have h2 : Real.log (τ₁ / τ_star) < Real.log (τ₂ / τ_star) :=
    Real.log_lt_log hdiv₁_pos hdiv_lt
  exact mul_lt_mul_of_pos_left h2 h1

/-- **Monotonic Gain Decay**: For $\delta < 0$, the West/East gain ratio is
strictly decreasing with height $\tau > 0$. The East array dominates more and more. -/
theorem channelGainRatio_lt_channelGainRatio_of_lt_neg {δ τ₁ τ₂ τ_star μ₀ : ℝ}
    (h_star : 0 < τ_star) (hμ₀ : 0 < μ₀) (hδ : δ < 0)
    (hτ₁ : 0 < τ₁) (hlt : τ₁ < τ₂) :
    channelGainRatio δ τ₂ τ_star μ₀ < channelGainRatio δ τ₁ τ_star μ₀ := by
  unfold channelGainRatio
  rw [Real.exp_lt_exp]
  have h1 : δ / μ₀ < 0 := div_neg_of_neg_of_pos hδ hμ₀
  have hdiv_lt : τ₁ / τ_star < τ₂ / τ_star := div_lt_div_of_pos_right hlt h_star
  have hdiv₁_pos : 0 < τ₁ / τ_star := div_pos hτ₁ h_star
  have h2 : Real.log (τ₁ / τ_star) < Real.log (τ₂ / τ_star) :=
    Real.log_lt_log hdiv₁_pos hdiv_lt
  exact mul_lt_mul_of_neg_left h2 h1

/-- **Three-Vector Lower Bound (Dual Pair with Remainder)**:
For any dual pair $v_1, v_2$ and remainder $R$,
$\|v_1 + v_2 + R\| \ge |\|v_1\| - \|v_2\|| - \|R\|$. -/
theorem norm_add_add_lower_bound {E : Type*} [SeminormedAddCommGroup E]
    (v₁ v₂ R : E) :
    |‖v₁‖ - ‖v₂‖| - ‖R‖ ≤ ‖v₁ + v₂ + R‖ := by
  have h1 : ‖v₁‖ - ‖v₂‖ - ‖R‖ ≤ ‖v₁ + v₂ + R‖ := by
    have h := norm_sub_le (v₁ + v₂ + R) (v₂ + R)
    have heq : (v₁ + v₂ + R) - (v₂ + R) = v₁ := by abel
    rw [heq] at h
    have hsum : ‖v₂ + R‖ ≤ ‖v₂‖ + ‖R‖ := norm_add_le v₂ R
    linarith
  have h2 : ‖v₂‖ - ‖v₁‖ - ‖R‖ ≤ ‖v₁ + v₂ + R‖ := by
    have h := norm_sub_le (v₁ + v₂ + R) (v₁ + R)
    have heq : (v₁ + v₂ + R) - (v₁ + R) = v₂ := by abel
    rw [heq] at h
    have hsum : ‖v₁ + R‖ ≤ ‖v₁‖ + ‖R‖ := norm_add_le v₁ R
    linarith
  have hle : |‖v₁‖ - ‖v₂‖| ≤ ‖v₁ + v₂ + R‖ + ‖R‖ := by
    rw [abs_le]
    constructor <;> linarith
  linarith

/-- **Dual Cancellation Obstruction**: If the amplitude mismatch between West and East
arrays $|\|v_1\| - \|v_2\||$ exceeds the remainder norm $\|R\|$, the total field CANNOT vanish:
$v_1 + v_2 + R \ne 0$. -/
theorem sum_three_ne_zero_of_mismatch_gt_remainder {E : Type*} [SeminormedAddCommGroup E]
    {v₁ v₂ R : E} (h : ‖R‖ < |‖v₁‖ - ‖v₂‖|) :
    v₁ + v₂ + R ≠ 0 := by
  intro hsum
  have hle := norm_add_add_lower_bound v₁ v₂ R
  rw [hsum, norm_zero] at hle
  linarith

/-- **Relative Gain Mismatch Representation**:
If $v_2 \ne 0$ and $r = \|v_1\| / \|v_2\|$, then
$|\|v_1\| - \|v_2\|| = \|v_2\| \cdot |r - 1|$. -/
theorem norm_sub_norm_eq_mul_abs_sub_one {E : Type*} [SeminormedAddCommGroup E]
    (v₁ v₂ : E) (hv₂ : ‖v₂‖ ≠ 0) :
    |‖v₁‖ - ‖v₂‖| = ‖v₂‖ * |(‖v₁‖ / ‖v₂‖) - 1| := by
  have : ‖v₁‖ - ‖v₂‖ = ‖v₂‖ * ((‖v₁‖ / ‖v₂‖) - 1) := by
    calc ‖v₁‖ - ‖v₂‖ = (‖v₁‖ / ‖v₂‖) * ‖v₂‖ - ‖v₂‖ := by
          rw [div_mul_cancel₀ ‖v₁‖ hv₂]
      _ = ‖v₂‖ * ((‖v₁‖ / ‖v₂‖) - 1) := by ring
  have hpos : 0 ≤ ‖v₂‖ := norm_nonneg v₂
  rw [this, abs_mul, abs_of_nonneg hpos]

/-- **Macro-Scale Dual Cancellation Obstruction**:
If the relative gain mismatch $|r - 1|$ exceeds the normalized remainder $\|R\| / \|v_2\|$,
then the total field $v_1 + v_2 + R \ne 0$. -/
theorem sum_three_ne_zero_of_relative_mismatch {E : Type*} [SeminormedAddCommGroup E]
    {v₁ v₂ R : E} (hv₂ : 0 < ‖v₂‖)
    (hmismatch : ‖R‖ / ‖v₂‖ < |(‖v₁‖ / ‖v₂‖) - 1|) :
    v₁ + v₂ + R ≠ 0 := by
  apply sum_three_ne_zero_of_mismatch_gt_remainder
  have heq := norm_sub_norm_eq_mul_abs_sub_one v₁ v₂ (ne_of_gt hv₂)
  rw [heq]
  have hmul := mul_lt_mul_of_pos_right hmismatch hv₂
  rw [div_mul_cancel₀ ‖R‖ (ne_of_gt hv₂)] at hmul
  rw [mul_comm] at hmul
  exact hmul

end RhG1Lean
