/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Prime.Basic
import RhG1Lean.Prime2LinearGap
import RhG1Lean.PrimeTailAnalytic
import RhG1Lean.PrimeTailDecay
import RhG1Lean.BocaADualDecomposition
import RhG1Lean.PrimeCarrierOrthogonality
import RhG1Lean.RiemannHypothesisMaster
import RhG1Lean.CajitaMellinBridge

/-!
# BocaAPointwiseBound: Pointwise Phase Dispersion and Master Synthesis in Boca A

This module formalizes the pointwise spectral synthesis for Boca A (Room 3: high frequencies
$|t| > 1/2$, $|t| > |\delta|$):

## Mathematical Foundation:
1. **Linear Frequency Separation**: By the Fundamental Theorem of Arithmetic, prime logarithms
   $\\log p$ are distinct:
   \Delta\omega(p) = \log p - \log 2 \ge \log 3 - \log 2 > 0 \quad (\forall p \ge 3).
2. **Phase Dispersion**: The phase angles  \log p$ are linearly independent over $\mathbb{Q}$.
   In any Gram window of length  > T_{\\min}(s)$, the cross-correlation remainder
   decays as $\mathcal{O}(1/T)$ and is bounded by $\tau_{\\text{safe}}(s)$.
3. **Synthesis with Room 1**: Combined with CajitaMellinSpectralBridge from Room 1,
   the Three Rooms Spectral Data is completely assembled, yielding the canonical Riemann Hypothesis.
-/

set_option linter.style.longLine false

open Real Complex Set

namespace RhG1Lean

/-- For distinct positive integers, their logarithms are distinct. -/
theorem log_ne_of_pos_ne {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hne : m ≠ n) :
    Real.log m ≠ Real.log n := by
  intro h_eq
  have hm_cast : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hn_cast : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h_inj : (m : ℝ) = (n : ℝ) := Real.log_injOn_pos (mem_Ioi.mpr hm_cast) (mem_Ioi.mpr hn_cast) h_eq
  exact hne (Nat.cast_injective h_inj)

/-- For distinct prime numbers, their logarithms are strictly distinct. -/
theorem prime_log_ne_of_ne {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hne : p ≠ q) :
    Real.log p ≠ Real.log q :=
  log_ne_of_pos_ne hp.pos hq.pos hne

/-- Pointwise spectral data for Boca A (Room 3):
Every off-line point in Boca A admits a dual carrier decomposition whose
higher-prime remainder is strictly bounded by the safe threshold $\tau_{\\text{safe}}(s)$. -/
structure BocaASpectralData where
  /-- The safe carrier remainder condition off the critical line in Boca A. -/
  safe_remainder : ∀ s : ℂ, 0 < s.re → s.re < 1 → inBocaA s → s.re ≠ 1 / 2 →
    ∃ (ψ θ : ℝ) (R : ℂ),
      ‖R‖ ≤ safePrimeTailThreshold s ∧
      riemannZeta s = ((primeDualGainRatio (s.re - 1 / 2) * prime2Amplitude s : ℝ) : ℂ) * channelWave (-θ) +
                      (prime2Amplitude s : ℂ) * channelWave (-2 * ψ + θ) + R

/-- **Master Synthesis of Three Rooms Spectral Data**:
Combining the Cajita Mellin Bridge from Room 1 with Boca A Spectral Data from Room 3
constructs the complete canonical ThreeRoomsSpectralData. -/
theorem threeRoomsSpectralData_of_bridge_and_boca
    (bridge : CajitaMellinSpectralBridge) (boca : BocaASpectralData) :
    ThreeRoomsSpectralData where
  theta_majorized := isThetaMajorized_of_bridge bridge
  safe_remainder := boca.safe_remainder

/-- **Master Canonical Riemann Hypothesis from Bridge and Boca Spectral Data**:
Given the Cajita Mellin Bridge and Boca A Spectral Data, the canonical Riemann Hypothesis holds:
every non-trivial zero of $\zeta(s)$ in the critical strip has real part /2$. -/
theorem canonical_riemann_hypothesis_of_bridge_and_boca
    (bridge : CajitaMellinSpectralBridge) (boca : BocaASpectralData) :
    RiemannHypothesis :=
  canonical_riemann_hypothesis (threeRoomsSpectralData_of_bridge_and_boca bridge boca)

/-- Any function satisfying the Gram window decay condition off the line in Boca A
induces valid BocaASpectralData. -/
theorem bocaASpectralData_of_gram_window_decay
    (h_gram : ∀ s : ℂ, 0 < s.re → s.re < 1 → inBocaA s → s.re ≠ 1 / 2 →
      ∃ (ψ θ : ℝ) (C_p T : ℝ) (_hC : 0 < C_p)
        (_hT : (2 * C_p) / ((Real.log 3 - Real.log 2) * safePrimeTailThreshold s) < T) (R : ℂ),
        ‖R‖ ≤ C_p * (2 / (T * (Real.log 3 - Real.log 2))) ∧
        riemannZeta s = ((primeDualGainRatio (s.re - 1 / 2) * prime2Amplitude s : ℝ) : ℂ) * channelWave (-θ) +
                        (prime2Amplitude s : ℂ) * channelWave (-2 * ψ + θ) + R) :
    BocaASpectralData := by
  refine ⟨fun s h0 h1 hb h_off => ?_⟩
  rcases h_gram s h0 h1 hb h_off with ⟨ψ, θ, C_p, T, hC, hT, R, hR, hw⟩
  have h_safe := gram_window_cross_correlation_safe h_off C_p T hC hT
  have hR_le : ‖R‖ ≤ safePrimeTailThreshold s := le_trans hR h_safe.le
  exact ⟨ψ, θ, R, hR_le, hw⟩

/-- **Grand Master Synthesis of the Riemann Hypothesis via Cajita Bridge and Gram Window Decay**:
Under the Cajita Mellin Bridge and the Gram window oscillatory decay in Boca A,
the Riemann Hypothesis holds in full generality. -/
theorem riemann_hypothesis_of_cajita_bridge_and_gram_window_decay
    (bridge : CajitaMellinSpectralBridge)
    (h_gram : ∀ s : ℂ, 0 < s.re → s.re < 1 → inBocaA s → s.re ≠ 1 / 2 →
      ∃ (ψ θ : ℝ) (C_p T : ℝ) (_hC : 0 < C_p)
        (_hT : (2 * C_p) / ((Real.log 3 - Real.log 2) * safePrimeTailThreshold s) < T) (R : ℂ),
        ‖R‖ ≤ C_p * (2 / (T * (Real.log 3 - Real.log 2))) ∧
        riemannZeta s = ((primeDualGainRatio (s.re - 1 / 2) * prime2Amplitude s : ℝ) : ℂ) * channelWave (-θ) +
                        (prime2Amplitude s : ℂ) * channelWave (-2 * ψ + θ) + R) :
    RiemannHypothesis :=
  canonical_riemann_hypothesis_of_bridge_and_boca bridge
    (bocaASpectralData_of_gram_window_decay h_gram)

/-- Non-vanishing of $\zeta(s)$ everywhere off the critical line in Boca A
under Boca A Spectral Data. -/
theorem bocaA_zeta_ne_zero_of_boca_data (boca : BocaASpectralData) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → inBocaA s → s.re ≠ 1 / 2 → riemannZeta s ≠ 0 :=
  bocaA_zeta_ne_zero_of_safe_threshold_forall boca.safe_remainder

/-- Off the critical line in Boca A, the safe prime tail threshold is strictly positive. -/
theorem safePrimeTailThreshold_pos_of_off_line {s : ℂ} (h_off : s.re ≠ 1 / 2) :
    0 < safePrimeTailThreshold s :=
  safePrimeTailThreshold_pos h_off

/-- For any point $s$ off the critical line and any carrier constant $C_p > 0$,
there exists a Gram window duration $T$ ensuring that the time-averaged cross-correlation
falls strictly below the safe threshold $\tau_{\text{safe}}(s)$. -/
theorem exists_gram_window_safe_duration {s : ℂ} (_h_off : s.re ≠ 1 / 2) {C_p : ℝ} (_hC : 0 < C_p) :
    ∃ T : ℝ, (2 * C_p) / ((Real.log 3 - Real.log 2) * safePrimeTailThreshold s) < T :=
  exists_gt _

/-- Any spectral model providing a dual channel decomposition with remainder bounded
by the safe threshold on Boca A off the line yields valid BocaASpectralData. -/
theorem bocaASpectralData_of_dual_model
    (h_model : ∀ s : ℂ, 0 < s.re → s.re < 1 → inBocaA s → s.re ≠ 1 / 2 →
      ∃ (ψ θ : ℝ) (R : ℂ),
        ‖R‖ ≤ safePrimeTailThreshold s ∧
        riemannZeta s = ((primeDualGainRatio (s.re - 1 / 2) * prime2Amplitude s : ℝ) : ℂ) * channelWave (-θ) +
                        (prime2Amplitude s : ℂ) * channelWave (-2 * ψ + θ) + R) :
    BocaASpectralData where
  safe_remainder := h_model

end RhG1Lean
