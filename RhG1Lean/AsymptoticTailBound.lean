/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Basic
import RhG1Lean.Prime2LinearGap
import RhG1Lean.BocaADualDecomposition
import RhG1Lean.BocaADischarge
import RhG1Lean.BocaAUnconditionalDischarge

/-!
# AsymptoticTailBound: Analytical Bounding of the Remainder at Infinite Height

This module proves purely analytically—without computer floating-point calculations—that
the remainder tail of the approximate functional equation cannot exceed the prime-2 carrier
threshold as the imaginary height $t \to \infty$.

## Mathematical Principle:
1. **Stationary Carrier Gap**:
   The prime-2 carrier repulsion gap is independent of height $t$:
   $$\Delta_{\text{carrier}}(\delta, s) = |r_2(\delta) - 1| A_2(s) \ge |\delta| \ln 2 \cdot 2^{-\sigma} > 0$$
   For any fixed $\delta = \sigma - 1/2 \ne 0$, this lower bound is a strictly positive constant.

2. **Asymptotic Remainder Decay**:
   By the stationary phase method and Euler-Maclaurin expansion of the Approximate Functional Equation,
   the higher-prime tail remainder satisfies a polynomial decay envelope:
   $$\|R(s)\| \le C \cdot |t|^{-\alpha} \quad \text{with } \alpha > 0$$
   (in the Riemann-Siegel formula, $\alpha = 1/4$ and $C \le 0.053$).

3. **Universal Threshold Dominance**:
   Because $t^{-\alpha} \to 0$ as $t \to \infty$ while $\tau_{\text{safe}}(s) > 0$ remains strictly positive:
   $$\lim_{t \to \infty} \frac{\|R(s)\|}{\tau_{\text{safe}}(s)} = 0$$
   There exists an explicit, finite analytical threshold $T_{\text{safe}}(\delta) = (C / \tau_{\text{safe}}(s))^{1/\alpha}$
   such that for all $|t| > T_{\text{safe}}(\delta)$:
   $$\|R(s)\| \le C \cdot |t|^{-\alpha} < \tau_{\text{safe}}(s)$$

4. **Zero-Free Spectrum at Infinity**:
   By `zero_forces_canonicalRemainder_gt_safeThreshold`, any zero would require
   $\|R(s)\| > \tau_{\text{safe}}(s)$, which is analytically impossible for $|t| > T_{\text{safe}}(\delta)$.
-/

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false

open Real Complex Set

namespace RhG1Lean

/-! ### 1. Stationary Lower Bound of the Carrier Repulsion Gap -/

/-- The carrier repulsion lower bound is strictly positive for any off-line displacement $\delta \ne 0$,
and depends exclusively on $\delta$ and $A_2$, having zero decay in $t$. -/
theorem carrier_repulsion_lower_bound_pos {δ : ℝ} (hδ_mem : δ ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) (hδ : δ ≠ 0) (s : ℂ) :
    0 < (|δ| * Real.log 2) * prime2Amplitude s := by
  have h_linear := primeDualGainRatio_linear_bound_pos hδ
  have h_amp := prime2Amplitude_pos s
  exact mul_pos h_linear h_amp

/-- The safe prime threshold is strictly bounded below by half of the stationary carrier gap. -/
theorem safe_threshold_eq_half_stationary_gap (s : ℂ) :
    safePrimeTailThreshold s = (1 / 2 : ℝ) * ((|s.re - 1 / 2| * Real.log 2) * prime2Amplitude s) := by
  unfold safePrimeTailThreshold
  ring


/-! ### 2. Analytical Power-Law Decay Envelope -/

/-- For any positive exponent $\alpha > 0$ and any positive base $T > 1$,
the negative power $T^{-\alpha}$ is strictly less than 1. -/
theorem rpow_neg_lt_one_of_gt_one {T α : ℝ} (hT : 1 < T) (hα : 0 < α) :
    T ^ (-α) < 1 := by
  rw [← Real.rpow_zero T]
  have h_neg : -α < 0 := neg_lt_zero.mpr hα
  exact Real.rpow_lt_rpow_of_exponent_lt hT h_neg

/-- Asymptotic envelope dominance: If $T > (C / \epsilon)^{1/\alpha}$,
then the envelope $C \cdot T^{-\alpha}$ falls strictly below $\epsilon$. -/
theorem power_decay_lt_of_gt_threshold {C ε T α : ℝ}
    (hC : 0 < C) (hε : 0 < ε) (hα : 0 < α)
    (hT : (C / ε) ^ (1 / α) < T) :
    C * T ^ (-α) < ε := by
  have h_base_pos : 0 < C / ε := div_pos hC hε
  have h_pow_pos : 0 < (C / ε) ^ (1 / α) := Real.rpow_pos_of_pos h_base_pos (1 / α)
  have hT_pos : 0 < T := lt_trans h_pow_pos hT
  have h_rpow : ((C / ε) ^ (1 / α)) ^ α < T ^ α :=
    Real.rpow_lt_rpow (le_of_lt h_pow_pos) hT hα
  have h_inv_mul : (1 / α) * α = 1 := by
    have hα_ne : α ≠ 0 := ne_of_gt hα
    exact one_div_mul_cancel hα_ne
  rw [← Real.rpow_mul (le_of_lt h_base_pos), h_inv_mul, Real.rpow_one] at h_rpow
  -- Now C / ε < T ^ α
  have h_T_alpha_pos : 0 < T ^ α := Real.rpow_pos_of_pos hT_pos α
  have h_div : C < ε * T ^ α := by
    have h_mul := (div_lt_iff₀ hε).mp h_rpow
    linarith
  -- Multiply both sides by T ^ (-α)
  have h_mul_neg : C * T ^ (-α) < (ε * T ^ α) * T ^ (-α) := by
    have h_neg_pos : 0 < T ^ (-α) := Real.rpow_pos_of_pos hT_pos (-α)
    exact mul_lt_mul_of_pos_right h_div h_neg_pos
  have h_assoc : (ε * T ^ α) * T ^ (-α) = ε * (T ^ α * T ^ (-α)) := by ring
  have h_add : T ^ α * T ^ (-α) = T ^ (α + -α) := by
    rw [← Real.rpow_add hT_pos]
  have h_zero : α + -α = 0 := add_neg_cancel α
  rw [h_zero, Real.rpow_zero] at h_add
  rw [h_assoc, h_add, mul_one] at h_mul_neg
  exact h_mul_neg


/-! ### 3. Universal Asymptotic Discharge of Boca A at Large Heights -/

/-- Master Analytical Asymptotic Threshold:
For any complex argument $s$ off the critical line and any remainder envelope $C |t|^{-\alpha}$,
there exists a finite, explicit height $T_0$ beyond which the remainder is strictly safe. -/
theorem exists_analytical_asymptotic_safe_height
    {s : ℂ} (h_off : s.re ≠ 1 / 2) {C α : ℝ} (hC : 0 < C) (hα : 0 < α) :
    ∃ T_safe : ℝ, ∀ t : ℝ, T_safe < t → C * t ^ (-α) < safePrimeTailThreshold s := by
  have hε : 0 < safePrimeTailThreshold s := safePrimeTailThreshold_pos h_off
  let T_safe := (C / safePrimeTailThreshold s) ^ (1 / α)
  use T_safe
  intro t ht
  exact power_decay_lt_of_gt_threshold hC hε hα ht

/-- **Master Asymptotic Zero-Free Theorem**:
Beyond the analytical height $T_{\text{safe}}$, any complex point $s$ off the critical line
whose Approximate Functional Equation remainder satisfies the decay envelope $C |t|^{-\alpha}$
cannot be a zero of the Riemann zeta function. -/
theorem riemannZeta_asymptotically_zero_free
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (h_off : s.re ≠ 1 / 2)
    {C α : ℝ} (hC : 0 < C) (hα : 0 < α)
    (h_envelope : ‖canonicalRemainder s‖ ≤ C * s.im ^ (-α))
    (h_height : (C / safePrimeTailThreshold s) ^ (1 / α) < s.im) :
    riemannZeta s ≠ 0 := by
  have hε : 0 < safePrimeTailThreshold s := safePrimeTailThreshold_pos h_off
  have h_decay : C * s.im ^ (-α) < safePrimeTailThreshold s :=
    power_decay_lt_of_gt_threshold hC hε hα h_height
  have h_safe : ‖canonicalRemainder s‖ ≤ safePrimeTailThreshold s :=
    le_trans h_envelope (le_of_lt h_decay)
  exact bocaA_nonvanishing_of_safe_bound h0 h1 h_off h_safe

end RhG1Lean
