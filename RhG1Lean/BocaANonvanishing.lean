/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under CC-BY 4.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Group.Basic
import RhG1Lean.KroneckerMismatch
import RhG1Lean.BocaADualCancellation
import RhG1Lean.StripReduction

/-!
# Boca A Non-vanishing via Kronecker Asymmetric Dominance

This module formalizes Phase N: the asymmetric dual cancellation obstruction
in the Boca A regime ($|\delta| < |t|$ with $|t| > 1/2$).

1. `bocaA_delta_ne_zero`:
   Any off-line point in Boca A has $\delta = \operatorname{Re} s - 1/2 \ne 0$.
2. `asymmetric_dual_sum_remainder_lower_bound`:
   $\|A_1 e^{-i\theta} + A_2 e^{-i(2\psi - \theta)} + R\| \ge |A_1 - A_2| - \|R\|$.
3. `asymmetric_dual_sum_ne_zero_of_remainder_lt`:
   If $\|R\| < |A_1 - A_2|$, then $A_1 e^{-i\theta} + A_2 e^{-i(2\psi - \theta)} + R \ne 0$.
4. `bocaA_mismatch_amplitude_eq`:
   $|r \cdot A_2 - A_2| = |r - 1| \cdot A_2$ for $A_2 \ge 0$.
5. `bocaA_relative_mismatch_ne_zero`:
   If $A_2 > 0$, $r \ne 1$, and $\|R\| < |r - 1| \cdot A_2$, then
   $(r \cdot A_2) e^{-i\theta} + A_2 e^{-i(2\psi - \theta)} + R \ne 0$.
6. `bocaA_gain_ratio_mismatch`:
   For $\delta \ne 0$ and $\tau \ne \tau_*$, the gain ratio $r(\delta, \tau) \ne 1$.
-/

set_option linter.style.longLine false

open Real Complex

namespace RhG1Lean

/-- In Boca A, if $\operatorname{Re} s \ne 1/2$, the displacement $\delta$ is non-zero. -/
theorem bocaA_delta_ne_zero {s : ℂ} (hne : s.re ≠ 1 / 2) : s.re - 1 / 2 ≠ 0 :=
  sub_ne_zero.mpr hne

/-- **Lower Bound for Asymmetric Dual Pair with Remainder**:
The norm of the total wave is bounded below by the amplitude mismatch minus the remainder. -/
theorem asymmetric_dual_sum_remainder_lower_bound (A₁ A₂ : ℝ) (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (ψ θ : ℝ) (R : ℂ) :
    |A₁ - A₂| - ‖R‖ ≤ ‖(A₁ : ℂ) * channelWave (-θ) + (A₂ : ℂ) * channelWave (-2 * ψ + θ) + R‖ := by
  set v := (A₁ : ℂ) * channelWave (-θ) + (A₂ : ℂ) * channelWave (-2 * ψ + θ)
  have htri := norm_sub_norm_le v (-R)
  rw [norm_neg, sub_neg_eq_add] at htri
  have hpair := asymmetric_dual_pair_norm_lower_bound A₁ A₂ hA₁ hA₂ ψ θ
  linarith

/-- **Asymmetric Dual Sum Non-vanishing**:
If the remainder norm is strictly smaller than the amplitude mismatch,
the composite wave cannot vanish. -/
theorem asymmetric_dual_sum_ne_zero_of_remainder_lt {A₁ A₂ : ℝ} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (ψ θ : ℝ) {R : ℂ} (hR : ‖R‖ < |A₁ - A₂|) :
    (A₁ : ℂ) * channelWave (-θ) + (A₂ : ℂ) * channelWave (-2 * ψ + θ) + R ≠ 0 := by
  intro hz
  have hlb := asymmetric_dual_sum_remainder_lower_bound A₁ A₂ hA₁ hA₂ ψ θ R
  rw [hz, norm_zero] at hlb
  linarith

/-- Factoring the amplitude mismatch in terms of the gain ratio $r = A_1 / A_2$. -/
theorem bocaA_mismatch_amplitude_eq (r A₂ : ℝ) (hA₂ : 0 ≤ A₂) :
    |r * A₂ - A₂| = |r - 1| * A₂ := by
  have : r * A₂ - A₂ = (r - 1) * A₂ := by ring
  rw [this, abs_mul, abs_of_nonneg hA₂]

/-- **Relative Mismatch Non-vanishing Theorem**:
If the gain ratio $r \ne 1$, $A_2 > 0$, and the remainder is bounded by the
relative mismatch $|r - 1| \cdot A_2$, then the total field is non-zero. -/
theorem bocaA_relative_mismatch_ne_zero {r A₂ : ℝ} (hr : 0 ≤ r) (hA₂ : 0 < A₂)
    (_hne : r ≠ 1) (ψ θ : ℝ) {R : ℂ}
    (hR : ‖R‖ < |r - 1| * A₂) :
    ((r * A₂ : ℝ) : ℂ) * channelWave (-θ) + (A₂ : ℂ) * channelWave (-2 * ψ + θ) + R ≠ 0 := by
  have hrA₂ : 0 ≤ r * A₂ := mul_nonneg hr (le_of_lt hA₂)
  have hA₂_le : 0 ≤ A₂ := le_of_lt hA₂
  have heq : |r * A₂ - A₂| = |r - 1| * A₂ := bocaA_mismatch_amplitude_eq r A₂ hA₂_le
  have hdiff : ‖R‖ < |r * A₂ - A₂| := by rwa [heq]
  exact asymmetric_dual_sum_ne_zero_of_remainder_lt hrA₂ hA₂_le ψ θ hdiff

/-- In Boca A, off the critical line, the gain ratio strictly departs from 1. -/
theorem bocaA_gain_ratio_mismatch {δ τ τ_star μ₀ : ℝ}
    (hτ : 0 < τ) (h_star : 0 < τ_star) (hμ₀ : 0 < μ₀)
    (hδ : δ ≠ 0) (h_tau_ne : τ ≠ τ_star) :
    channelGainRatio δ τ τ_star μ₀ ≠ 1 :=
  channelGainRatio_ne_one_of_delta_ne_zero hτ h_star hμ₀ hδ h_tau_ne

/-- **Boca A Dominance in the West Sub-regime** ($\delta > 0$):
When $\delta > 0$ and $\tau > \tau_*$, the gain ratio satisfies $r > 1$
and the amplitude difference is $(r - 1) \cdot A_2 > 0$. -/
theorem bocaA_west_mismatch_pos {δ τ τ_star μ₀ A₂ : ℝ}
    (h_star : 0 < τ_star) (hμ₀ : 0 < μ₀)
    (hδ : 0 < δ) (hτ : τ_star < τ) (hA₂ : 0 < A₂) :
    0 < (channelGainRatio δ τ τ_star μ₀ - 1) * A₂ := by
  have hr := channelGainRatio_gt_one_of_pos h_star hμ₀ hδ hτ
  have hsub : 0 < channelGainRatio δ τ τ_star μ₀ - 1 := sub_pos.mpr hr
  exact mul_pos hsub hA₂

/-- **Boca A Dominance in the East Sub-regime** ($\delta < 0$):
When $\delta < 0$ and $\tau > \tau_*$, the gain ratio satisfies $r < 1$
and the amplitude difference is $(1 - r) \cdot A_2 > 0$. -/
theorem bocaA_east_mismatch_pos {δ τ τ_star μ₀ A₂ : ℝ}
    (h_star : 0 < τ_star) (hμ₀ : 0 < μ₀)
    (hδ : δ < 0) (hτ : τ_star < τ) (hA₂ : 0 < A₂) :
    0 < (1 - channelGainRatio δ τ τ_star μ₀) * A₂ := by
  have hr := channelGainRatio_lt_one_of_neg h_star hμ₀ hδ hτ
  have hsub : 0 < 1 - channelGainRatio δ τ τ_star μ₀ := sub_pos.mpr hr
  exact mul_pos hsub hA₂

/-- **Boca A Master Non-vanishing Criterion**:
For any point off the critical line in Boca A, if the ratio $r = channelGainRatio$
and remainder $R$ satisfy the dominance condition $\|R\| < |r - 1| \cdot A_2$,
then the composite wave is strictly non-zero. -/
theorem bocaA_master_nonvanishing {δ τ τ_star μ₀ A₂ : ℝ}
    (hτ : 0 < τ) (h_star : 0 < τ_star) (hμ₀ : 0 < μ₀)
    (hδ : δ ≠ 0) (h_tau_ne : τ ≠ τ_star) (hA₂ : 0 < A₂)
    (ψ θ : ℝ) {R : ℂ}
    (hR : ‖R‖ < |channelGainRatio δ τ τ_star μ₀ - 1| * A₂) :
    let r := channelGainRatio δ τ τ_star μ₀
    ((r * A₂ : ℝ) : ℂ) * channelWave (-θ) + (A₂ : ℂ) * channelWave (-2 * ψ + θ) + R ≠ 0 := by
  intro r
  have hr_pos : 0 ≤ r := le_of_lt (channelGainRatio_pos δ τ τ_star μ₀)
  have hne : r ≠ 1 := bocaA_gain_ratio_mismatch hτ h_star hμ₀ hδ h_tau_ne
  exact bocaA_relative_mismatch_ne_zero hr_pos hA₂ hne ψ θ hR

/-! ### Prime-2 Slowest Channel Dual Gain Mismatch -/

/-- Gain ratio of the slowest prime channel (prime 2) under transverse displacement $\delta$:
$r_2(\delta) = 2^{-2\delta} = \exp(-2\delta \ln 2)$. -/
noncomputable def primeDualGainRatio (δ : ℝ) : ℝ :=
  Real.exp (-2 * δ * Real.log 2)

@[simp] theorem primeDualGainRatio_zero : primeDualGainRatio 0 = 1 := by
  unfold primeDualGainRatio
  simp

theorem primeDualGainRatio_pos (δ : ℝ) : 0 < primeDualGainRatio δ :=
  Real.exp_pos _

theorem log_two_pos : 0 < Real.log 2 := by
  have : (1 : ℝ) < 2 := by norm_num
  exact Real.log_pos this

theorem primeDualGainRatio_ne_one_of_delta_ne_zero {δ : ℝ} (hδ : δ ≠ 0) :
    primeDualGainRatio δ ≠ 1 := by
  unfold primeDualGainRatio
  intro h
  rw [Real.exp_eq_one_iff] at h
  have hlog : Real.log 2 ≠ 0 := ne_of_gt log_two_pos
  have h2 : (-2 : ℝ) ≠ 0 := by norm_num
  have hmul : (-2 * δ) * Real.log 2 = 0 := h
  cases mul_eq_zero.mp hmul with
  | inl h_neg2_delta =>
    cases mul_eq_zero.mp h_neg2_delta with
    | inl h_neg2 => exact (h2 h_neg2).elim
    | inr h_delta => exact hδ h_delta
  | inr h_l2 => exact (hlog h_l2).elim

theorem primeDualGainRatio_lt_one_of_pos {δ : ℝ} (hδ : 0 < δ) :
    primeDualGainRatio δ < 1 := by
  unfold primeDualGainRatio
  rw [Real.exp_lt_one_iff]
  have hlog : 0 < Real.log 2 := log_two_pos
  have : -2 * δ < 0 := by linarith
  exact mul_neg_of_neg_of_pos this hlog

theorem primeDualGainRatio_gt_one_of_neg {δ : ℝ} (hδ : δ < 0) :
    1 < primeDualGainRatio δ := by
  unfold primeDualGainRatio
  rw [Real.one_lt_exp_iff]
  have hlog : 0 < Real.log 2 := log_two_pos
  have : 0 < -2 * δ := by linarith
  exact mul_pos this hlog

theorem primeDualGainRatio_mismatch_pos {δ : ℝ} (hδ : δ ≠ 0) :
    0 < |primeDualGainRatio δ - 1| :=
  abs_pos.mpr (sub_ne_zero.mpr (primeDualGainRatio_ne_one_of_delta_ne_zero hδ))

/-- **Master Prime-2 Dual Non-vanishing Theorem**:
For any off-line perturbation $\delta \ne 0$, the prime-2 counter-rotating pair
with remainder $R$ cannot vanish if $\|R\| < |r_2(\delta) - 1| \cdot A_2$. -/
theorem prime2_dual_nonvanishing {δ A₂ : ℝ} (hδ : δ ≠ 0) (hA₂ : 0 < A₂)
    (ψ θ : ℝ) {R : ℂ}
    (hR : ‖R‖ < |primeDualGainRatio δ - 1| * A₂) :
    let r := primeDualGainRatio δ
    ((r * A₂ : ℝ) : ℂ) * channelWave (-θ) + (A₂ : ℂ) * channelWave (-2 * ψ + θ) + R ≠ 0 := by
  intro r
  have hr_nonneg : 0 ≤ r := le_of_lt (primeDualGainRatio_pos δ)
  have hne : r ≠ 1 := primeDualGainRatio_ne_one_of_delta_ne_zero hδ
  exact bocaA_relative_mismatch_ne_zero hr_nonneg hA₂ hne ψ θ hR

/-- Predicate stating that a complex value `w` admits a prime-2 asymmetric dual representation
with dominant gap over the remainder. -/
def HasPrime2DualDominance (w : ℂ) (δ : ℝ) : Prop :=
  ∃ (A₂ : ℝ) (_hA₂ : 0 < A₂) (ψ θ : ℝ) (R : ℂ),
    ‖R‖ < |primeDualGainRatio δ - 1| * A₂ ∧
    w = ((primeDualGainRatio δ * A₂ : ℝ) : ℂ) * channelWave (-θ) +
        (A₂ : ℂ) * channelWave (-2 * ψ + θ) + R

/-- If `w` has prime-2 dual dominance with $\delta \ne 0$, then $w \ne 0$. -/
theorem ne_zero_of_hasPrime2DualDominance {w : ℂ} {δ : ℝ} (hδ : δ ≠ 0)
    (hdom : HasPrime2DualDominance w δ) : w ≠ 0 := by
  rcases hdom with ⟨A₂, hA₂, ψ, θ, R, hR, rfl⟩
  exact prime2_dual_nonvanishing hδ hA₂ ψ θ hR

/-- If `riemannZeta s` satisfies prime-2 dual dominance for all off-line points in Boca A,
then `riemannZeta s ≠ 0` everywhere off-line in Boca A. -/
theorem bocaA_zeta_ne_zero_of_prime2_dominance
    (h_dom : ∀ s : ℂ, 0 < s.re → s.re < 1 → inBocaA s → s.re ≠ 1 / 2 →
      HasPrime2DualDominance (riemannZeta s) (s.re - 1 / 2)) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → inBocaA s → s.re ≠ 1 / 2 → riemannZeta s ≠ 0 := by
  intro s h0 h1 hB h_off
  have hδ : s.re - 1 / 2 ≠ 0 := sub_ne_zero.mpr h_off
  exact ne_zero_of_hasPrime2DualDominance hδ (h_dom s h0 h1 hB h_off)

end RhG1Lean

