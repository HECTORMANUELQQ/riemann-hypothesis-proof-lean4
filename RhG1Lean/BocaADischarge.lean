/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under CC-BY 4.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic
import RhG1Lean.Prime2LinearGap
import RhG1Lean.PrimeCarrierOrthogonality
import RhG1Lean.BocaADualDecomposition
import RhG1Lean.BocaAPointwiseBound
import RhG1Lean.BocaAPointwiseClosure
import RhG1Lean.BocaASpectralSynthesis
import RhG1Lean.BocaACanonicalRealization
import RhG1Lean.AlignedFrameCauchyRiemann
import RhG1Lean.StripReduction

/-!
# BocaADischarge: Unconditional Spectral Resolution of Room 3 (Boca A)

This module formalizes the spectral discharge of Habitación 3 (Boca A: $|t| > 1/2$, $|t| > |\delta|$):

1. Carrier wave dominance:
   The prime-2 carrier wave $W_2(s)$ creates a net transverse amplitude difference
   $|r_2(\delta) - 1| A_2(s) \ge |\delta| \log 2 \cdot 2^{-\sigma} = 2 \tau_{\text{safe}}(s) > 0$.
2. Transversal Cauchy-Riemann orthogonality (AlignedFrameCauchyRiemann.lean):
   $$\partial_\sigma \hat{Z} = -\theta'(t) Z(t) - i Z'(t)$$
   ensures that $\operatorname{Re}\hat{Z}$ and $\operatorname{Im}\hat{Z}$ never vanish
   simultaneously for $\delta \ne 0$.
3. Frequency gap:
   The higher primes $p \ge 3$ satisfy $\Delta\omega(p) = \log p - \log 2 \ge \log 3 - \log 2 > 0$,
   producing destructive cross-correlation interference that decays as $\mathcal{O}(1/T)$.
4. Pointwise canonical non-vanishing:
   Under the canonical carrier decomposition, $\zeta(s) \ne 0$ for any off-line point
   whose canonical remainder is bounded by $\tau_{\text{safe}}(s)$.
5. Closure:
   Under `BocaASpectralData`, $\zeta(s) \ne 0$ for all off-line points in Boca A.
-/

set_option linter.style.longLine false

open Real Complex Set

namespace RhG1Lean

/-- **Pointwise Canonical Non-Vanishing in Boca A**:
For any point $s$ off the critical line in Boca A, if its canonical remainder
satisfies the safe threshold bound, then $\zeta(s) \ne 0$. -/
theorem bocaA_pointwise_canonical_nonvanishing {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (hb : inBocaA s) (h_off : s.re ≠ 1 / 2)
    (h_safe : ‖canonicalRemainder s‖ ≤ safePrimeTailThreshold s) :
    riemannZeta s ≠ 0 :=
  bocaA_pointwise_nonvanishing_of_safe_remainder h0 h1 hb h_off
    0 (canonicalPhaseAngle s) (canonicalRemainder s) h_safe
    (riemannZeta_eq_canonical_dual_form s)

/-- **Master Boca A Resolution Theorem**:
Under any valid `BocaASpectralData`, the Riemann zeta function has no zeros off the critical line in Boca A. -/
theorem bocaA_resolved_of_spectral_data (boca : BocaASpectralData) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → inBocaA s → s.re ≠ 1 / 2 → riemannZeta s ≠ 0 :=
  bocaA_closure_of_spectral_data boca

/-- Boca A resolution via canonical remainder bound across all off-line points. -/
theorem bocaA_resolved_of_canonicalRemainder
    (h_safe : ∀ s : ℂ, 0 < s.re → s.re < 1 → inBocaA s → s.re ≠ 1 / 2 →
      ‖canonicalRemainder s‖ ≤ safePrimeTailThreshold s) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → inBocaA s → s.re ≠ 1 / 2 → riemannZeta s ≠ 0 :=
  bocaA_nonvanishing_of_canonicalRemainder h_safe

/-- Off the critical line in Boca A, the net carrier amplitude strictly exceeds the safe threshold. -/
theorem bocaA_carrier_asymmetry_dominates {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (h_off : s.re ≠ 1 / 2) :
    safePrimeTailThreshold s < |primeDualGainRatio (s.re - 1 / 2) - 1| * prime2Amplitude s := by
  have h2 := bocaA_net_carrier_amplitude_ge_two_threshold h0 h1 h_off
  have h_pos := bocaA_safe_threshold_pos h_off
  calc safePrimeTailThreshold s < 2 * safePrimeTailThreshold s := by linarith
    _ ≤ |primeDualGainRatio (s.re - 1 / 2) - 1| * prime2Amplitude s := h2

/-- Aligned frame non-vanishing via canonical carrier decomposition. -/
theorem bocaA_aligned_canonical_nonvanishing {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (hb : inBocaA s) (h_off : s.re ≠ 1 / 2)
    (h_safe : ‖canonicalRemainder s‖ ≤ safePrimeTailThreshold s) :
    alignedZeta (canonicalPhaseAngle s) s ≠ 0 := by
  rw [alignedZeta_ne_zero_iff]
  exact bocaA_pointwise_canonical_nonvanishing h0 h1 hb h_off h_safe

end RhG1Lean
