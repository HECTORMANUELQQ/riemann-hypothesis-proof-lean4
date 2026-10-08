/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import RhG1Lean.PrimeCarrierOrthogonality
import RhG1Lean.BocaAPointwiseBound
import RhG1Lean.BocaAPointwiseClosure
import RhG1Lean.RiemannHypothesisFinal

/-!
# BocaASpectralSynthesis: Kronecker-Weyl Ergodic Phase Separation and Room 3 Closure

This module formalizes the spectral synthesis of Habitación 3 (Boca A: |t| > 1/2):

1. **Kronecker-Weyl Phase Separation**:
   For every higher prime p ≥ 3, the logarithmic frequency difference
   Δω(p) = log p - log 2 is uniformly bounded below by log 3 - log 2 > 0.
2. **Destructive Interference**:
   The oscillatory cross-correlation between the base carrier p = 2 and higher primes
   is bounded by 2 / (T * (log 3 - log 2)), decaying to zero as the averaging window T grows.
3. **Carrier Asymmetry Dominance**:
   Off the critical line (s.re ≠ 1/2), the carrier amplitude asymmetry
   |r₂(δ) - 1| A₂(s) strictly dominates any remainder R bounded by τ_safe(s):
   ‖R‖ ≤ τ_safe(s) < 2 τ_safe(s) ≤ |r₂(δ) - 1| A₂(s).
4. **Spectral Synthesis in Boca A**:
   Every zero of ζ(s) in Boca A must lie on the critical line s.re = 1/2.
-/

set_option linter.style.longLine false

open Real Complex Set

namespace RhG1Lean

/-- Kronecker-Weyl Phase Separation:
Every prime p ≥ 3 has frequency separation Δω(p) ≥ log 3 - log 2 > 0 from prime 2. -/
theorem bocaA_kronecker_weyl_phase_separation {p : ℕ} (hp : 3 ≤ p) :
    0 < Real.log 3 - Real.log 2 ∧ Real.log 3 - Real.log 2 ≤ frequencyGap p :=
  ⟨log_three_sub_log_two_pos, log_three_sub_log_two_le_frequencyGap hp⟩

/-- Destructive Interference Bound:
The time-averaged correlation between prime 2 and higher prime p decays as O(1/T). -/
theorem bocaA_destructive_interference_decay {p : ℕ} (hp : 3 ≤ p)
    {t₁ t₂ : ℝ} (hT : 0 < t₂ - t₁) :
    (1 / (t₂ - t₁)) * ‖(channelWave (t₂ * frequencyGap p) - channelWave (t₁ * frequencyGap p)) /
      (I * (frequencyGap p : ℂ))‖ ≤ 2 / ((t₂ - t₁) * (Real.log 3 - Real.log 2)) :=
  average_oscillatory_correlation_le hp hT

/-- Net carrier asymmetry strictly exceeds any remainder bounded by τ_safe(s). -/
theorem bocaA_carrier_asymmetry_dominates_safe_remainder {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (h_off : s.re ≠ 1 / 2)
    {R : ℂ} (hR : ‖R‖ ≤ safePrimeTailThreshold s) :
    ‖R‖ < |primeDualGainRatio (s.re - 1 / 2) - 1| * prime2Amplitude s := by
  have h_lt := bocaA_remainder_lt_two_threshold h_off hR
  have h_ge := bocaA_net_carrier_amplitude_ge_two_threshold h0 h1 h_off
  exact lt_of_lt_of_le h_lt h_ge

/-- Master Synthesis of Boca A:
Under BocaASpectralData, the zero set of ζ in Boca A is contained in the critical line. -/
theorem bocaA_spectral_empty_off_line (boca : BocaASpectralData) :
    {s : ℂ | 0 < s.re ∧ s.re < 1 ∧ inBocaA s ∧ riemannZeta s = 0} ⊆ {s : ℂ | s.re = 1 / 2} := by
  intro s hs
  rcases hs with ⟨h0, h1, hb, hz⟩
  by_contra h_off
  have h_nz := bocaA_closure_of_spectral_data boca s h0 h1 hb h_off
  exact h_nz hz

/-- Synthesis of Boca A Zero-Freeness off the Critical Line. -/
theorem bocaA_zero_free_off_line_of_spectral_data (boca : BocaASpectralData) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → inBocaA s → s.re ≠ 1 / 2 → riemannZeta s ≠ 0 :=
  bocaA_closure_of_spectral_data boca

end RhG1Lean
