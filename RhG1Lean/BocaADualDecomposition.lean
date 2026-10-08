/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import RhG1Lean.Prime2LinearGap
import RhG1Lean.PrimeTailAnalytic
import RhG1Lean.PrimeTailDecay
import RhG1Lean.BocaADualCancellation

/-!
# BocaADualDecomposition: Canonical Dual Channel Realization in Boca A

This module establishes the exact bridge between the analytical Riemann-Siegel
carrier terms at $n = 2$ and the abstract dual channel framework of Boca A:

1. The natural prime-2 amplitude scale is:
   $$A_2(s) = 2^{-(1 - \operatorname{Re}(s))} = 2^{-(1/2 - \delta)} > 0.$$
2. Scaled by $r_2(\delta) = 2^{-2\delta}$, the West channel amplitude is:
   $$r_2(\delta) A_2(s) = 2^{-2\delta} \cdot 2^{-(1/2 - \delta)} = 2^{-(1/2 + \delta)} = 2^{-\operatorname{Re}(s)} = \|2^{-s}\|.$$
3. The East channel amplitude is:
   $$A_2(s) = 2^{-(1 - \operatorname{Re}(s))} = \|2^{-(1-s)}\|.$$
4. The safe tail tolerance threshold:
   $$\tau_{\text{safe}}(s) = \frac{1}{2} (|\operatorname{Re}(s) - 1/2| \log 2) A_2(s) > 0$$
   is strictly positive everywhere off the critical line in the critical strip.
5. Consequently, any remainder with \|R(s)\| \le \tau_{\text{safe}}(s) unconditionally
   guarantees \zeta(s) \ne 0.
-/

set_option linter.style.longLine false

open Real Complex Set

namespace RhG1Lean

/-- The canonical carrier amplitude for the prime $p = 2$ at complex argument $s$:
$$A_2(s) = 2^{-(1 - \operatorname{Re}(s))}.$$ -/
noncomputable def prime2Amplitude (s : ℂ) : ℝ :=
  (2 : ℝ) ^ (-(1 - s.re))

/-- The prime-2 amplitude is strictly positive everywhere. -/
theorem prime2Amplitude_pos (s : ℂ) : 0 < prime2Amplitude s := by
  unfold prime2Amplitude
  exact Real.rpow_pos_of_pos (by norm_num) _

/-- The prime-2 amplitude is non-negative everywhere. -/
theorem prime2Amplitude_nonneg (s : ℂ) : 0 ≤ prime2Amplitude s :=
  (prime2Amplitude_pos s).le

/-- The product of the prime-2 gain ratio and $A_2(s)$ exactly equals $2^{-\operatorname{Re}(s)}$. -/
theorem primeDualGainRatio_mul_prime2Amplitude (s : ℂ) :
    primeDualGainRatio (s.re - 1 / 2) * prime2Amplitude s = (2 : ℝ) ^ (-s.re) := by
  unfold primeDualGainRatio prime2Amplitude
  have h2 : (0 : ℝ) < 2 := by norm_num
  have h_comm : -2 * (s.re - 1 / 2) * Real.log 2 = Real.log 2 * (-2 * (s.re - 1 / 2)) := by ring
  rw [h_comm, ← Real.rpow_def_of_pos h2]
  rw [← Real.rpow_add h2]
  congr 1
  ring

/-- The norm of the West carrier wave $(2 : \mathbb{C})^{-s}$ exactly equals $2^{-\operatorname{Re}(s)}$. -/
theorem norm_two_cpow_neg_s (s : ℂ) :
    ‖(2 : ℂ) ^ (-s)‖ = (2 : ℝ) ^ (-s.re) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have h := Complex.norm_cpow_eq_rpow_re_of_pos h2 (-s)
  rw [neg_re] at h
  exact h

/-- The norm of the East carrier wave $(2 : \mathbb{C})^{-(1-s)}$ exactly equals $A_2(s)$. -/
theorem norm_two_cpow_neg_one_sub_s (s : ℂ) :
    ‖(2 : ℂ) ^ (-(1 - s))‖ = prime2Amplitude s := by
  unfold prime2Amplitude
  have h2 : (0 : ℝ) < 2 := by norm_num
  have h := Complex.norm_cpow_eq_rpow_re_of_pos h2 (-(1 - s))
  rw [neg_re, sub_re, one_re] at h
  exact h

/-- The quotient of the West and East carrier wave norms equals the gain ratio $r_2(\delta) = 2^{-2\delta}$. -/
theorem norm_two_cpow_ratio_eq_primeDualGainRatio (s : ℂ) :
    ‖(2 : ℂ) ^ (-s)‖ / ‖(2 : ℂ) ^ (-(1 - s))‖ = primeDualGainRatio (s.re - 1 / 2) := by
  rw [norm_two_cpow_neg_s, norm_two_cpow_neg_one_sub_s]
  have hA2_pos := prime2Amplitude_pos s
  have h_prod := primeDualGainRatio_mul_prime2Amplitude s
  rw [← h_prod, mul_div_cancel_right₀ _ (ne_of_gt hA2_pos)]

/-- Off the critical line, the West and East carrier wave norms are strictly unequal. -/
theorem norm_two_cpow_west_ne_east_of_off_line {s : ℂ} (hne : s.re ≠ 1 / 2) :
    ‖(2 : ℂ) ^ (-s)‖ ≠ ‖(2 : ℂ) ^ (-(1 - s))‖ := by
  intro h_eq
  have h_ratio : ‖(2 : ℂ) ^ (-s)‖ / ‖(2 : ℂ) ^ (-(1 - s))‖ = 1 := by
    rw [h_eq, div_self (ne_of_gt (by rw [norm_two_cpow_neg_one_sub_s]; exact prime2Amplitude_pos s))]
  rw [norm_two_cpow_ratio_eq_primeDualGainRatio] at h_ratio
  have hδ_ne : s.re - 1 / 2 ≠ 0 := sub_ne_zero.mpr hne
  have h_ne_one := primeDualGainRatio_ne_one_of_delta_ne_zero hδ_ne
  exact h_ne_one h_ratio

/-- The safe prime tail threshold at complex argument $s$:
$$\tau_{\text{safe}}(s) = \frac{1}{2} (|\operatorname{Re}(s) - 1/2| \log 2) A_2(s).$$ -/
noncomputable def safePrimeTailThreshold (s : ℂ) : ℝ :=
  (1 / 2) * (|s.re - 1 / 2| * Real.log 2) * prime2Amplitude s

/-- Off the critical line, the safe prime tail threshold is strictly positive. -/
theorem safePrimeTailThreshold_pos {s : ℂ} (hne : s.re ≠ 1 / 2) :
    0 < safePrimeTailThreshold s := by
  unfold safePrimeTailThreshold
  have h_half : (0 : ℝ) < 1 / 2 := by norm_num
  have hδ_pos : 0 < |s.re - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hlog : 0 < Real.log 2 := by
    have h1 : (1 : ℝ) < 2 := by norm_num
    exact Real.log_pos h1
  have hA2 : 0 < prime2Amplitude s := prime2Amplitude_pos s
  have hprod : 0 < |s.re - 1 / 2| * Real.log 2 := mul_pos hδ_pos hlog
  have hprod2 : 0 < (1 / 2 : ℝ) * (|s.re - 1 / 2| * Real.log 2) := mul_pos h_half hprod
  exact mul_pos hprod2 hA2

/-- Any remainder $R$ bounded by $\tau_{\text{safe}}(s)$ satisfies `HasSafePrimeTailBound`. -/
theorem hasSafePrimeTailBound_of_le_threshold {s : ℂ} {R : ℂ}
    (hR : ‖R‖ ≤ safePrimeTailThreshold s) :
    HasSafePrimeTailBound R (s.re - 1 / 2) (prime2Amplitude s) := by
  unfold HasSafePrimeTailBound safePrimeTailThreshold at *
  exact hR

/-- **Master Non-Vanishing under Safe Remainder Threshold**:
For any point $s$ in the critical strip off the critical line, if $\zeta(s)$
admits a dual channel representation with remainder \|R\| \le \tau_{\text{safe}}(s),
then $\zeta(s) \ne 0$. -/
theorem zeta_ne_zero_of_safe_threshold {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (hne : s.re ≠ 1 / 2)
    (ψ θ : ℝ) (R : ℂ)
    (hR : ‖R‖ ≤ safePrimeTailThreshold s)
    (hw : riemannZeta s = ((primeDualGainRatio (s.re - 1 / 2) * prime2Amplitude s : ℝ) : ℂ) * channelWave (-θ) +
                         (prime2Amplitude s : ℂ) * channelWave (-2 * ψ + θ) + R) :
    riemannZeta s ≠ 0 := by
  have hA2_pos := prime2Amplitude_pos s
  have h_safe := hasSafePrimeTailBound_of_le_threshold hR
  exact strip_ne_zero_of_safe_bound h0 h1 hne hA2_pos ψ θ R h_safe hw

end RhG1Lean
