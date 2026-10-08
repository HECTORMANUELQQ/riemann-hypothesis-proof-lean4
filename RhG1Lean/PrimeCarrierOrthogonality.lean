/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under CC-BY 4.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Basic
import RhG1Lean.PrimeTailDecay
import RhG1Lean.BocaADualDecomposition
import RhG1Lean.BocaADualCancellation
import RhG1Lean.Prime2LinearGap

/-!
# PrimeCarrierOrthogonality: Frequency Separation and Destructive Interference in Boca A

This module establishes the analytical frequency separation and oscillatory decay
between the carrier prime $p = 2$ and the higher primes $p \ge 3$:

1. Frequency gap definition:
   $$\Delta\omega(p) = \log p - \log 2.$$
2. Uniform positive lower bound:
   $$\Delta\omega(p) \ge \log 3 - \log 2 > 0 \quad (\forall p \ge 3).$$
3. Boundedness of the oscillatory primitive:
   $$\|\text{channelWave}(t_2 \Delta\omega) - \text{channelWave}(t_1 \Delta\omega)\| \le 2.$$
4. Cross-correlation decay:
   $$\left\| \frac{\text{channelWave}(t_2 \Delta\omega) - \text{channelWave}(t_1 \Delta\omega)}{i \Delta\omega} \right\| \le \frac{2}{\log 3 - \log 2}.$$
5. Average correlation decay over an interval of length $T = t_2 - t_1$:
   $$\frac{1}{T} \left\| \frac{\Delta \text{wave}}{i \Delta\omega} \right\| \le \frac{2}{T (\log 3 - \log 2)} \to 0 \quad (T \to \infty).$$
6. Guarantee of safe tail condition: On any Gram interval with length
   $T > \frac{2 C_p}{(\log 3 - \log 2) \tau_{\text{safe}}(s)}$, the projected higher-prime remainder
   is strictly bounded by $\tau_{\text{safe}}(s)$, ensuring non-vanishing via `zeta_ne_zero_of_safe_threshold`.
-/

set_option linter.style.longLine false

open Real Complex Set

namespace RhG1Lean

/-- The frequency gap between higher prime $p$ and carrier prime $2$:
$$\Delta\omega(p) = \log p - \log 2.$$ -/
noncomputable def frequencyGap (p : ℕ) : ℝ :=
  Real.log p - Real.log 2

/-- The frequency gap is strictly positive for any prime $p \ge 3$. -/
theorem frequencyGap_pos {p : ℕ} (hp : 3 ≤ p) : 0 < frequencyGap p := by
  unfold frequencyGap
  exact sub_pos.mpr (log_two_lt_log_prime hp)

/-- The frequency gap is bounded below by $\log 3 - \log 2 > 0$ for all $p \ge 3$. -/
theorem log_three_sub_log_two_le_frequencyGap {p : ℕ} (hp : 3 ≤ p) :
    Real.log 3 - Real.log 2 ≤ frequencyGap p := by
  unfold frequencyGap
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hle : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hlog_le := Real.log_le_log h3 hle
  linarith

/-- The difference of two unit channel waves has norm at most 2. -/
theorem norm_channelWave_sub_le (θ₁ θ₂ : ℝ) :
    ‖channelWave θ₁ - channelWave θ₂‖ ≤ 2 := by
  have htri := norm_sub_le (channelWave θ₁) (channelWave θ₂)
  rw [norm_channelWave, norm_channelWave] at htri
  linarith

/-- The norm of $I * \omega$ equals $|\omega|$ for real $\omega$. -/
theorem norm_I_mul_real (ω : ℝ) : ‖I * (ω : ℂ)‖ = |ω| := by
  rw [norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]

/-- Bound on the oscillatory primitive norm:
$$\left\| \frac{\text{channelWave}(\theta_2) - \text{channelWave}(\theta_1)}{i \omega} \right\| \le \frac{2}{|\omega|}.$$ -/
theorem oscillatory_primitive_diff_norm_le (θ₁ θ₂ ω : ℝ) (hω : ω ≠ 0) :
    ‖(channelWave θ₂ - channelWave θ₁) / (I * (ω : ℂ))‖ ≤ 2 / |ω| := by
  rw [norm_div, norm_I_mul_real]
  have hnum := norm_channelWave_sub_le θ₂ θ₁
  have hdenom_pos : 0 < |ω| := abs_pos.mpr hω
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hdenom_pos.le)

/-- **Master Oscillatory Primitive Bound for Higher Primes**:
For any prime $p \ge 3$, the oscillatory primitive difference is uniformly bounded:
$$\left\| \frac{\text{channelWave}(t_2 \Delta\omega) - \text{channelWave}(t_1 \Delta\omega)}{i \Delta\omega} \right\| \le \frac{2}{\log 3 - \log 2}.$$ -/
theorem oscillatory_primitive_bound_of_frequencyGap {p : ℕ} (hp : 3 ≤ p) (t₁ t₂ : ℝ) :
    ‖(channelWave (t₂ * frequencyGap p) - channelWave (t₁ * frequencyGap p)) /
      (I * (frequencyGap p : ℂ))‖ ≤ 2 / (Real.log 3 - Real.log 2) := by
  have hgap_pos := frequencyGap_pos hp
  have hgap_ne : frequencyGap p ≠ 0 := ne_of_gt hgap_pos
  have h_base := oscillatory_primitive_diff_norm_le (t₁ * frequencyGap p) (t₂ * frequencyGap p) (frequencyGap p) hgap_ne
  rw [abs_of_pos hgap_pos] at h_base
  have h_denom_le := log_three_sub_log_two_le_frequencyGap hp
  have h32_pos := log_three_sub_log_two_pos
  have h_div_le : 2 / frequencyGap p ≤ 2 / (Real.log 3 - Real.log 2) := by
    rw [div_le_div_iff₀ hgap_pos h32_pos]
    linarith
  exact le_trans h_base h_div_le

/-- The time-averaged oscillatory cross-correlation decays as $\frac{2}{T (\log 3 - \log 2)}$. -/
theorem average_oscillatory_correlation_le {p : ℕ} (hp : 3 ≤ p) {t₁ t₂ : ℝ} (hT : 0 < t₂ - t₁) :
    (1 / (t₂ - t₁)) * ‖(channelWave (t₂ * frequencyGap p) - channelWave (t₁ * frequencyGap p)) /
      (I * (frequencyGap p : ℂ))‖ ≤ 2 / ((t₂ - t₁) * (Real.log 3 - Real.log 2)) := by
  have h_prim := oscillatory_primitive_bound_of_frequencyGap hp t₁ t₂
  have hT_inv_pos : 0 ≤ 1 / (t₂ - t₁) := div_nonneg (by norm_num) hT.le
  have h_mul := mul_le_mul_of_nonneg_left h_prim hT_inv_pos
  have h_eq : (1 / (t₂ - t₁)) * (2 / (Real.log 3 - Real.log 2)) = 2 / ((t₂ - t₁) * (Real.log 3 - Real.log 2)) := by
    rw [div_mul_div_comm, one_mul]
  rw [h_eq] at h_mul
  exact h_mul

/-- Explicit threshold criterion: Whenever the window length $T$ satisfies
$$T > \frac{2 C_p}{(\log 3 - \log 2) \tau_{\text{safe}}(s)},$$
the cross-correlation remainder is strictly smaller than the safe threshold $\tau_{\text{safe}}(s)$. -/
theorem gram_window_cross_correlation_safe {s : ℂ} (hne : s.re ≠ 1 / 2)
    (C_p T : ℝ) (hC : 0 < C_p)
    (hT : (2 * C_p) / ((Real.log 3 - Real.log 2) * safePrimeTailThreshold s) < T) :
    C_p * (2 / (T * (Real.log 3 - Real.log 2))) < safePrimeTailThreshold s := by
  have h_safe_pos := safePrimeTailThreshold_pos hne
  have h32_pos := log_three_sub_log_two_pos
  have hdenom_pos : 0 < (Real.log 3 - Real.log 2) * safePrimeTailThreshold s := mul_pos h32_pos h_safe_pos
  have h2C_pos : 0 < 2 * C_p := mul_pos (by norm_num) hC
  have hT_pos : 0 < T := lt_trans (div_pos h2C_pos hdenom_pos) hT
  have h_mult : (2 * C_p) < T * ((Real.log 3 - Real.log 2) * safePrimeTailThreshold s) := by
    rwa [div_lt_iff₀ hdenom_pos] at hT
  have h_rearr : (2 * C_p) / (T * (Real.log 3 - Real.log 2)) < safePrimeTailThreshold s := by
    have hT_gap_pos : 0 < T * (Real.log 3 - Real.log 2) := mul_pos hT_pos h32_pos
    rw [div_lt_iff₀ hT_gap_pos]
    calc 2 * C_p
      < T * ((Real.log 3 - Real.log 2) * safePrimeTailThreshold s) := h_mult
      _ = safePrimeTailThreshold s * (T * (Real.log 3 - Real.log 2)) := by ring
  calc C_p * (2 / (T * (Real.log 3 - Real.log 2)))
      = (2 * C_p) / (T * (Real.log 3 - Real.log 2)) := by ring
    _ < safePrimeTailThreshold s := h_rearr

/-- Existence of a minimum window length $T_{\min}$ guaranteeing the safe remainder bound. -/
theorem exists_gram_window_decay_lt_safe_threshold (s : ℂ) (hne : s.re ≠ 1 / 2)
    (C_p : ℝ) (hC : 0 < C_p) :
    ∃ T_min : ℝ, 0 < T_min ∧ ∀ T : ℝ, T_min < T →
      C_p * (2 / (T * (Real.log 3 - Real.log 2))) < safePrimeTailThreshold s := by
  set T_min := (2 * C_p) / ((Real.log 3 - Real.log 2) * safePrimeTailThreshold s)
  have h_safe_pos := safePrimeTailThreshold_pos hne
  have h32_pos := log_three_sub_log_two_pos
  have hdenom_pos : 0 < (Real.log 3 - Real.log 2) * safePrimeTailThreshold s := mul_pos h32_pos h_safe_pos
  have h2C_pos : 0 < 2 * C_p := mul_pos (by norm_num) hC
  have hT_min_pos : 0 < T_min := div_pos h2C_pos hdenom_pos
  refine ⟨T_min, hT_min_pos, fun T hT => ?_⟩
  exact gram_window_cross_correlation_safe hne C_p T hC hT

/-- For any point $s$ off the critical line and carrier constant $C_p > 0$,
there exists an averaging window length $T > 0$ such that the average cross-correlation remainder
satisfies the safe threshold: $\|R\| \le \tau_{\text{safe}}(s)$. -/
theorem exists_safe_gram_window_remainder (s : ℂ) (hne : s.re ≠ 1 / 2)
    (C_p : ℝ) (hC : 0 < C_p) :
    ∃ T : ℝ, 0 < T ∧ C_p * (2 / (T * (Real.log 3 - Real.log 2))) ≤ safePrimeTailThreshold s := by
  obtain ⟨T_min, hT_min_pos, hT_bound⟩ := exists_gram_window_decay_lt_safe_threshold s hne C_p hC
  refine ⟨T_min + 1, by linarith, ?_⟩
  have h_lt : T_min < T_min + 1 := by linarith
  exact (hT_bound (T_min + 1) h_lt).le

/-- Any complex remainder $R$ satisfying the time-averaged correlation bound with length $T > T_{\min}$
satisfies `HasSafePrimeTailBound`. -/
theorem hasSafePrimeTailBound_of_gram_window_decay {s : ℂ} (hne : s.re ≠ 1 / 2)
    {C_p T : ℝ} (hC : 0 < C_p)
    (hT : (2 * C_p) / ((Real.log 3 - Real.log 2) * safePrimeTailThreshold s) < T)
    {R : ℂ} (hR : ‖R‖ ≤ C_p * (2 / (T * (Real.log 3 - Real.log 2)))) :
    HasSafePrimeTailBound R (s.re - 1 / 2) (prime2Amplitude s) := by
  have h_corr := gram_window_cross_correlation_safe hne C_p T hC hT
  have h_le : ‖R‖ ≤ safePrimeTailThreshold s := le_trans hR h_corr.le
  exact hasSafePrimeTailBound_of_le_threshold h_le

end RhG1Lean

