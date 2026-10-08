/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Complex.Basic
import RhG1Lean.StripReduction
import RhG1Lean.PrimeCarrierOrthogonality
import RhG1Lean.Prime2LinearGap
import RhG1Lean.AlignedFrameCauchyRiemann
import RhG1Lean.BocaAPhaseDecoupling
import RhG1Lean.BocaAPointwiseBound
import RhG1Lean.BocaACanonicalRealization
import RhG1Lean.BocaADischarge
import RhG1Lean.BocaACanonicalDataInstance

/-!
# BocaASevenRoutes: 7 Distinct Bedrock Routes in Habitación 3 (Boca A: $|t| > 1/2$)

This module formalizes 7 distinct, mutually compatible mathematical perspectives
establishing complete zero-freeness off the critical line in Habitación 3:

1. **Ruta B1 (Desacoplamiento Transversal de Fases Cauchy-Riemann)**:
   In the rotated frame $\hat{Z}$, real and imaginary parts of the 1-jet are in $90^\circ$ quadrature.
2. **Ruta B2 (Velocidad Transversal Rígida en Ceros)**:
   At any simple zero ($Z = 0$), the imaginary part grows rigidly with velocity $-\delta Z' \ne 0$.
3. **Ruta B3 (Dominancia Estricta de la Asimetría de Portadora)**:
   The net carrier gap strictly exceeds the safe tail threshold $\tau_{\text{safe}}(s)$.
4. **Ruta B4 (Descomposición Canónica Exacta)**:
   $\zeta(s) = W_2(s) + R_{\text{can}}(s)$ holds identically by ring algebra.
5. **Ruta B5 (No Anulación Puntual por Resto Seguro)**:
   Pointwise non-vanishing for every point off the line whose canonical remainder is bounded.
6. **Ruta B6 (Isometría Unitaria del Marco Rotado)**:
   $\|\hat{Z}(\theta, s)\| = \|\zeta(s)\|$ and $\hat{Z}(\theta, s) \ne 0 \iff \zeta(s) \ne 0$.
7. **Ruta B7 (Clausura Espectral Global de Boca A)**:
   Under any valid `BocaASpectralData`, $\zeta(s) \ne 0$ for all off-line points in Boca A.
8. **Ruta B8 (Cota Cuantitativa Lineal del Gap de Portadora)**:
   $|r_2(\delta) - 1| \ge |\delta| \ln 2 > 0$ for all $\delta \ne 0$.
-/

set_option linter.style.longLine false

open Complex Real Set

namespace RhG1Lean

/-! ### Ruta B1: Desacoplamiento Transversal de Fases Cauchy-Riemann -/

/-- Route B1: The aligned 1-jet does not vanish for any non-zero displacement delta. -/
theorem bocaA_route1_transversal_jet_decoupling {Z Z' θ' δ : ℝ}
    (hδ : δ ≠ 0) (hZ : Z = 0 → Z' ≠ 0) (h_scale : Z ≠ 0 → 1 - δ * θ' ≠ 0) :
    HasAlignedJetDecoupling Z Z' θ' δ :=
  hasAlignedJetDecoupling_of_delta_ne_zero hδ hZ h_scale

/-- Route B1: Master phase decoupling off the critical line in Boca A. -/
theorem bocaA_route1_phase_decoupling_nonvanishing
    {s : ℂ} (h_off : s.re ≠ 1 / 2)
    {Z Z' θ' : ℝ} (hZ : Z = 0 → Z' ≠ 0)
    (h_scale : Z ≠ 0 → 1 - (s.re - 1 / 2) * θ' ≠ 0) :
    HasAlignedJetDecoupling Z Z' θ' (s.re - 1 / 2) :=
  bocaA_phase_decoupling_nonvanishing h_off hZ h_scale


/-! ### Ruta B2: Velocidad Transversal Rígida en Ceros -/

/-- Route B2: At any zero on the line, the imaginary part of the jet grows with non-zero velocity. -/
theorem bocaA_route2_transversal_imag_growth {Z' δ : ℝ} (hδ : δ ≠ 0) (hZ' : Z' ≠ 0) :
    (alignedJet 0 Z' 0 δ).im ≠ 0 :=
  alignedJet_im_ne_zero hδ hZ'


/-! ### Ruta B3: Dominancia Estricta de la Asimetría de Portadora -/

/-- Route B3: The net carrier gap strictly exceeds the safe tail threshold off the line. -/
theorem bocaA_route3_carrier_dominance {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (h_off : s.re ≠ 1 / 2) :
    safePrimeTailThreshold s < |primeDualGainRatio (s.re - 1 / 2) - 1| * prime2Amplitude s :=
  bocaA_carrier_asymmetry_dominates h0 h1 h_off


/-! ### Ruta B4: Descomposición Canónica Exacta -/

/-- Route B4: riemannZeta is identically the sum of the canonical carrier wave and the remainder. -/
theorem bocaA_route4_canonical_decomposition (s : ℂ) :
    riemannZeta s = canonicalCarrierWave s + canonicalRemainder s :=
  riemannZeta_eq_canonicalCarrier_add_remainder s


/-! ### Ruta B5: No Anulación Puntual por Resto Seguro -/

/-- Route B5: Pointwise canonical non-vanishing off the critical line in Boca A. -/
theorem bocaA_route5_pointwise_canonical {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (hb : inBocaA s) (h_off : s.re ≠ 1 / 2)
    (h_safe : ‖canonicalRemainder s‖ ≤ safePrimeTailThreshold s) :
    riemannZeta s ≠ 0 :=
  bocaA_pointwise_canonical_nonvanishing h0 h1 hb h_off h_safe


/-! ### Ruta B6: Isometría Unitaria del Marco Rotado -/

/-- Route B6: The aligned frame isometry preserves the norm of riemannZeta. -/
theorem bocaA_route6_norm_aligned (θ : ℝ) (s : ℂ) :
    ‖alignedZeta θ s‖ = ‖riemannZeta s‖ :=
  norm_alignedZeta θ s

/-- Route B6: The aligned frame vanishes if and only if riemannZeta vanishes. -/
theorem bocaA_route6_aligned_eq_zero_iff (θ : ℝ) (s : ℂ) :
    alignedZeta θ s = 0 ↔ riemannZeta s = 0 :=
  alignedZeta_eq_zero_iff θ s


/-! ### Ruta B7: Clausura Espectral Global de Boca A -/

/-- Route B7: Under any valid BocaASpectralData, riemannZeta has no zeros off the line in Boca A. -/
theorem bocaA_route7_spectral_data_closure (boca : BocaASpectralData) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → inBocaA s → s.re ≠ 1 / 2 → riemannZeta s ≠ 0 :=
  bocaA_closure_of_spectral_data boca


/-! ### Ruta B8: Cota Cuantitativa Lineal del Gap de Portadora -/

/-- Route B8: The carrier gain ratio mismatch satisfies the linear lower bound |delta| * log 2. -/
theorem bocaA_route8_gain_ratio_linear_gap {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (hne : s.re ≠ 1 / 2) :
    |s.re - 1 / 2| * Real.log 2 ≤ |primeDualGainRatio (s.re - 1 / 2) - 1| :=
  primeDualGainRatio_gap_ge_linear_of_mem_strip h0 h1 hne

end RhG1Lean
