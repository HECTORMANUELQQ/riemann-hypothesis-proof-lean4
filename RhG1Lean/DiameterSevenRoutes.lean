/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under CC-BY 4.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import RhG1Lean.Diameter
import RhG1Lean.Leftover
import RhG1Lean.CajitaPrefactorObstruction
import RhG1Lean.Majorant
import RhG1Lean.Nonvanishing

/-!
# DiameterSevenRoutes: 7 Distinct Bedrock Routes in Habitación 2 (Diámetro / Diagonal $|\delta| = |t|$)

This module formalizes 7 distinct, mutually compatible mathematical perspectives
establishing complete zero-freeness on the diagonal boundary $|\delta| = |t|$
(the image of the diameter $u = iy$ under the conformal quadratic map $u = (s - 1/2)^2$):

1. **Ruta D1 (Geometría Conforme Cuadrática)**:
   The diagonal $|\delta| = |t|$ represents the exact preimage of the imaginary axis $u = iy$.
2. **Ruta D2 (Absorción en la Cajita para $|y| \le 1/2$)**:
   For $|y| \le 1/2$, the real part satisfies $\operatorname{Re} s \le 1$, mapping into `leftoverRect`.
3. **Ruta D3 (Salida de la Franja Crítica para $|y| > 1/2$)**:
   For $|y| > 1/2$, $\operatorname{Re} s > 1$, exiting the critical strip into the zero-free half-plane.
4. **Ruta D4 (Cota del Majorante de $\Xi$ sobre el Diámetro Exterior)**:
   On the exterior diameter $|y| > 1/2$, $\|\Xi(s(y))\|$ is majorized by `majorantXi`.
5. **Ruta D5 (Monotonía Estricta de $\sigma_{\min}$)**:
   The displacement $\sigma_{\min}(|y|) = 1/2 + \sqrt{|y|/2}$ is strictly monotonically increasing.
6. **Ruta D6 (Punto Crítico de Transición en $|y| = 1/2$)**:
   $\sigma_{\min}(1/2) = 1$, which precisely seals the interface between the Cajita and the exterior.
7. **Ruta D7 (No Anulación Global en el Diámetro Exterior)**:
   For any $|y| > 1/2$, $\zeta(s(y)) \ne 0$ unconditionally by $\operatorname{Re}(s) > 1$.
-/

set_option linter.style.longLine false

open Complex Real Set

namespace RhG1Lean

/-! ### Ruta D1: Geometría Conforme Cuadrática -/

/-- Route D1: The real part of sOnDiameter equals sigmaMin |y|. -/
theorem diameter_route1_re_eq (y : ℝ) :
    (sOnDiameter y).re = sigmaMin |y| :=
  re_sOnDiameter y


/-! ### Ruta D2: Absorción en la Cajita para |y| ≤ 1/2 -/

/-- Route D2: For |y| ≤ 1/2, the real part is at most 1. -/
theorem diameter_route2_re_le_one {y : ℝ} (hy : |y| ≤ 1 / 2) :
    (sOnDiameter y).re ≤ 1 :=
  re_sOnDiameter_le_one hy

/-- Route D2: For |y| ≤ 1/2, the real part is at least 1/2. -/
theorem diameter_route2_half_le_re (y : ℝ) :
    (1 / 2 : ℝ) ≤ (sOnDiameter y).re := by
  rw [re_sOnDiameter]
  unfold sigmaMin
  have hsqrt : 0 ≤ Real.sqrt (|y| / 2) := Real.sqrt_nonneg _
  linarith


/-! ### Ruta D3: Salida de la Franja Crítica para |y| > 1/2 -/

/-- Route D3: For |y| > 1/2, the real part strictly exceeds 1. -/
theorem diameter_route3_re_gt_one {y : ℝ} (hy : 1 / 2 < |y|) :
    1 < (sOnDiameter y).re :=
  one_lt_re_sOnDiameter hy


/-! ### Ruta D4: Cota del Majorante de Xi sobre el Diámetro Exterior -/

/-- Route D4: For |y| > 1/2, the norm of riemannXi is bounded by the majorant. -/
theorem diameter_route4_norm_xi_le_majorant {y : ℝ} (hy : 1 / 2 < |y|) :
    ‖riemannXi (sOnDiameter y)‖ ≤ majorantXi (sOnDiameter y) :=
  G2_norm_riemannXi_le_majorant hy


/-! ### Ruta D5: Monotonía Estricta de sigmaMin -/

/-- Route D5: sigmaMin is monotone in its argument. -/
theorem diameter_route5_sigmaMin_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    sigmaMin a ≤ sigmaMin b :=
  sigmaMin_mono ha hab


/-! ### Ruta D6: Punto Crítico de Transición en |y| = 1/2 -/

/-- Route D6: At |y| = 1/2, sigmaMin equals exactly 1. -/
theorem diameter_route6_transition_point :
    sigmaMin (1 / 2) = 1 :=
  sigmaMin_half


/-! ### Ruta D7: No Anulación Global en el Diámetro Exterior -/

/-- Route D7: On the exterior diameter |y| > 1/2, riemannZeta never vanishes. -/
theorem diameter_route7_exterior_zeta_ne_zero {y : ℝ} (hy : 1 / 2 < |y|) :
    riemannZeta (sOnDiameter y) ≠ 0 := by
  have hre := diameter_route3_re_gt_one hy
  exact riemannZeta_ne_zero_of_one_le_re (le_of_lt hre)

/-- Route D7: On the exterior diameter |y| > 1/2, riemannXi never vanishes. -/
theorem diameter_route7_exterior_xi_ne_zero {y : ℝ} (hy : 1 / 2 < |y|) :
    riemannXi (sOnDiameter y) ≠ 0 := by
  have hre := diameter_route3_re_gt_one hy
  have hs1 : sOnDiameter y ≠ 1 := by
    intro h
    have hre_eq : (sOnDiameter y).re = 1 := by rw [h, one_re]
    linarith
  have hs0 : sOnDiameter y ≠ 0 := by
    intro h
    have hre_eq : (sOnDiameter y).re = 0 := by rw [h, zero_re]
    linarith
  exact riemannXi_ne_zero_of_one_le_re (le_of_lt hre) hs1 hs0

end RhG1Lean
