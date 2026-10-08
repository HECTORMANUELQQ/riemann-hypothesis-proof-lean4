/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic
import RhG1Lean.Prime2LinearGap
import RhG1Lean.PrimeCarrierOrthogonality
import RhG1Lean.BocaADualDecomposition
import RhG1Lean.BocaAPointwiseBound
import RhG1Lean.RiemannHypothesisMaster

/-!
# BocaAPointwiseClosure: Pointwise Asymmetry Dominance and Boca A Spectral Closure

This module establishes the pointwise closure of Habitación 3 (Boca A: |t| > 1/2, |t| > |δ|):

1. Carrier Asymmetry: For all s = 1/2 + δ + it off the critical line (δ ≠ 0),
   the carrier gain asymmetry satisfies |r₂(δ) - 1| ≥ |δ| log 2 > 0.
2. Net Amplitude Dominance: The carrier amplitude difference
   |r₂(δ) - 1| A₂(s) ≥ |δ| log 2 * A₂(s) = 2 τ_safe(s).
3. Safety Remainder Margin: Any higher-prime remainder R bounded by τ_safe(s)
   is strictly smaller than the carrier asymmetry:
   ‖R‖ ≤ τ_safe(s) < 2 τ_safe(s) ≤ |r₂(δ) - 1| A₂(s).
4. Pointwise Non-Vanishing: By the reverse triangle inequality (Rigor Rule 1),
   ζ(s) cannot vanish anywhere off the critical line in Boca A.
5. Master Synthesis: Any BocaASpectralData unconditionally resolves Boca A off the line.
-/

set_option linter.style.longLine false

open Real Complex Set

namespace RhG1Lean

/-- Off the critical line, the safe prime tail threshold is strictly positive. -/
theorem bocaA_safe_threshold_pos {s : ℂ} (h_off : s.re ≠ 1 / 2) :
    0 < safePrimeTailThreshold s :=
  safePrimeTailThreshold_pos h_off

/-- For s in the critical strip, δ = s.re - 1/2 belongs to the interval [-1/2, 1/2]. -/
theorem delta_mem_Icc_of_strip {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    s.re - 1 / 2 ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) := by
  constructor <;> linarith

/-- The carrier gain asymmetry lower bound scaled by A₂(s) in the critical strip:
|δ| log 2 * A₂(s) ≤ |r₂(δ) - 1| A₂(s). -/
theorem bocaA_carrier_asymmetry_lower_bound {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (h_off : s.re ≠ 1 / 2) :
    |s.re - 1 / 2| * Real.log 2 * prime2Amplitude s ≤
      |primeDualGainRatio (s.re - 1 / 2) - 1| * prime2Amplitude s := by
  have hδ_mem := delta_mem_Icc_of_strip h0 h1
  have hδ_ne : s.re - 1 / 2 ≠ 0 := sub_ne_zero.mpr h_off
  have h_gap := primeDualGainRatio_gap_ge_linear hδ_mem hδ_ne
  have hA2_nonneg := prime2Amplitude_nonneg s
  exact mul_le_mul_of_nonneg_right h_gap hA2_nonneg

/-- The net carrier amplitude is at least twice the safe tail threshold:
2 * τ_safe(s) ≤ |r₂(δ) - 1| A₂(s). -/
theorem bocaA_net_carrier_amplitude_ge_two_threshold {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (h_off : s.re ≠ 1 / 2) :
    2 * safePrimeTailThreshold s ≤
      |primeDualGainRatio (s.re - 1 / 2) - 1| * prime2Amplitude s := by
  unfold safePrimeTailThreshold
  have h_eq : 2 * ((1 / 2 : ℝ) * (|s.re - 1 / 2| * Real.log 2) * prime2Amplitude s) =
      |s.re - 1 / 2| * Real.log 2 * prime2Amplitude s := by ring
  rw [h_eq]
  exact bocaA_carrier_asymmetry_lower_bound h0 h1 h_off

/-- Any remainder R bounded by τ_safe(s) satisfies ‖R‖ < 2 * τ_safe(s). -/
theorem bocaA_remainder_lt_two_threshold {s : ℂ} (h_off : s.re ≠ 1 / 2)
    {R : ℂ} (hR : ‖R‖ ≤ safePrimeTailThreshold s) :
    ‖R‖ < 2 * safePrimeTailThreshold s := by
  have h_pos := bocaA_safe_threshold_pos h_off
  calc ‖R‖ ≤ safePrimeTailThreshold s := hR
    _ < 2 * safePrimeTailThreshold s := by linarith

/-- Pointwise Non-Vanishing Theorem in Boca A:
For any s in the critical strip with s.re ≠ 1/2 in Boca A,
if ζ(s) admits a dual carrier representation with remainder ‖R‖ ≤ τ_safe(s),
then ζ(s) ≠ 0. -/
theorem bocaA_pointwise_nonvanishing_of_safe_remainder {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (_hb : inBocaA s) (h_off : s.re ≠ 1 / 2)
    (ψ θ : ℝ) (R : ℂ)
    (hR : ‖R‖ ≤ safePrimeTailThreshold s)
    (hw : riemannZeta s = ((primeDualGainRatio (s.re - 1 / 2) * prime2Amplitude s : ℝ) : ℂ) * channelWave (-θ) +
                         (prime2Amplitude s : ℂ) * channelWave (-2 * ψ + θ) + R) :
    riemannZeta s ≠ 0 :=
  zeta_ne_zero_of_safe_threshold h0 h1 h_off ψ θ R hR hw

/-- Master Resolution of Boca A from Spectral Data:
Under BocaASpectralData, ζ(s) does not vanish anywhere off the critical line in Boca A. -/
theorem bocaA_closure_of_spectral_data (boca : BocaASpectralData) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → inBocaA s → s.re ≠ 1 / 2 → riemannZeta s ≠ 0 :=
  bocaA_zeta_ne_zero_of_boca_data boca

end RhG1Lean
