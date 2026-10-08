/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import RhG1Lean.Prime2LinearGap
import RhG1Lean.PrimeCarrierOrthogonality
import RhG1Lean.BocaADualDecomposition
import RhG1Lean.BocaAPointwiseBound
import RhG1Lean.BocaAPointwiseClosure
import RhG1Lean.BocaASpectralSynthesis

/-!
# BocaACanonicalRealization: Canonical Carrier Realization for Boca A

This module formalizes the canonical realization of the dual channel portadora wave
and higher-prime remainder in Room 3 (Boca A: |t| > 1/2):

1. Canonical Carrier Angles:
   - θ(s) = s.im * Real.log 2 (the logarithmic phase angle for prime 2).
   - ψ = 0 (the symmetric phase center).
2. Canonical Dual Carrier Wave:
   - W₂(s) = ((primeDualGainRatio (s.re - 1 / 2) * prime2Amplitude s : ℝ) : ℂ) * channelWave (-θ(s)) +
             (prime2Amplitude s : ℂ) * channelWave (-2 * 0 + θ(s)).
3. Canonical Remainder:
   - R_can(s) = riemannZeta s - W₂(s).
4. Exact Algebraic Decomposition:
   - riemannZeta s = W₂(s) + R_can(s) (holds identically by ring / abel).
5. Canonical BocaASpectralData Constructor:
   - Any bound ‖R_can(s)‖ ≤ safePrimeTailThreshold s yields valid BocaASpectralData.
-/

set_option linter.style.longLine false

open Real Complex Set

namespace RhG1Lean

/-- Canonical phase angle for the prime 2 carrier wave: θ(s) = s.im * log 2. -/
noncomputable def canonicalPhaseAngle (s : ℂ) : ℝ :=
  s.im * Real.log 2

/-- The canonical dual carrier wave for prime 2 in Boca A. -/
noncomputable def canonicalCarrierWave (s : ℂ) : ℂ :=
  let θ := canonicalPhaseAngle s
  let A₂ := prime2Amplitude s
  let r := primeDualGainRatio (s.re - 1 / 2)
  ((r * A₂ : ℝ) : ℂ) * channelWave (-θ) + (A₂ : ℂ) * channelWave (-2 * 0 + θ)

/-- The canonical higher-prime remainder: R_can(s) = riemannZeta s - canonicalCarrierWave s. -/
noncomputable def canonicalRemainder (s : ℂ) : ℂ :=
  riemannZeta s - canonicalCarrierWave s

/-- Exact Algebraic Decomposition Identity:
riemannZeta s is identically the sum of the canonical carrier wave and the remainder. -/
theorem riemannZeta_eq_canonicalCarrier_add_remainder (s : ℂ) :
    riemannZeta s = canonicalCarrierWave s + canonicalRemainder s := by
  unfold canonicalRemainder
  ring

/-- The canonical algebraic decomposition expressed in standard dual-wave form. -/
theorem riemannZeta_eq_canonical_dual_form (s : ℂ) :
    riemannZeta s =
      ((primeDualGainRatio (s.re - 1 / 2) * prime2Amplitude s : ℝ) : ℂ) *
        channelWave (-canonicalPhaseAngle s) +
      (prime2Amplitude s : ℂ) *
        channelWave (-2 * 0 + canonicalPhaseAngle s) +
      canonicalRemainder s := by
  have h := riemannZeta_eq_canonicalCarrier_add_remainder s
  unfold canonicalCarrierWave at h
  exact h

/-- Canonical Constructor of BocaASpectralData:
If the canonical remainder is bounded by the safe threshold everywhere off the critical line,
then valid BocaASpectralData is unconditionally obtained. -/
theorem bocaASpectralData_of_canonicalRemainder
    (h_safe : ∀ s : ℂ, 0 < s.re → s.re < 1 → inBocaA s → s.re ≠ 1 / 2 →
      ‖canonicalRemainder s‖ ≤ safePrimeTailThreshold s) :
    BocaASpectralData where
  safe_remainder := fun s h0 h1 hb h_off =>
    ⟨0, canonicalPhaseAngle s, canonicalRemainder s, h_safe s h0 h1 hb h_off,
     riemannZeta_eq_canonical_dual_form s⟩

/-- Non-vanishing of riemannZeta in Boca A off the critical line under the canonical remainder bound. -/
theorem bocaA_nonvanishing_of_canonicalRemainder
    (h_safe : ∀ s : ℂ, 0 < s.re → s.re < 1 → inBocaA s → s.re ≠ 1 / 2 →
      ‖canonicalRemainder s‖ ≤ safePrimeTailThreshold s) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → inBocaA s → s.re ≠ 1 / 2 → riemannZeta s ≠ 0 :=
  bocaA_closure_of_spectral_data (bocaASpectralData_of_canonicalRemainder h_safe)

end RhG1Lean
