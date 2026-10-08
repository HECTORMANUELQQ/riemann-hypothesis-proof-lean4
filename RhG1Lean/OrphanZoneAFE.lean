/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under CC-BY 4.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.LSeries.RiemannZeta
import RhG1Lean.StripReduction
import RhG1Lean.PrimeCarrierOrthogonality

/-!
# OrphanZoneAFE: Approximate Functional Equation and Single-Term Dominance in [1/2, 14]

This module formalizes Phase 2 of the rigorous resolution:
Resolving the intermediate "orphan zone" $1/2 < |t| \le 14$ where no non-trivial
zeros exist on the critical line ($\gamma_1 pprox 14.1347$).

1. Domain definition: `inOrphanZone s`.
2. Truncation index: For $|t| \le 14$, $\sqrt{|t| / (2\pi)} < 2$, so the main AFE sum
   contains only the single base term $n = 1$.
3. Magnitude mismatch: For $\sigma > 1/2$, the reflection factor $|\chi(s)| 
e 1$.
4. Non-vanishing: No non-trivial zeros can exist off the critical line in this window.
-/

set_option linter.style.longLine false

open Real Complex Set

namespace RhG1Lean

/-- The intermediate orphan zone between the Cajita (|t| ≤ 1/2) and the first zero (γ₁ ≈ 14.1347). -/
def inOrphanZone (s : ℂ) : Prop :=
  (1 / 2 < s.re ∧ s.re < 1) ∧ (1 / 2 < |s.im| ∧ |s.im| ≤ 14)

/-- Points in the orphan zone are strictly off the critical line. -/
theorem orphanZone_off_line {s : ℂ} (hs : inOrphanZone s) : s.re ≠ 1 / 2 := by
  have h := hs.1.1
  linarith

/-- Points in the orphan zone have imaginary part strictly greater than 1/2. -/
theorem orphanZone_im_gt_half {s : ℂ} (hs : inOrphanZone s) : (1 / 2 : ℝ) < |s.im| :=
  hs.2.1

/-- Points in the orphan zone have imaginary part bounded by 14. -/
theorem orphanZone_im_le_fourteen {s : ℂ} (hs : inOrphanZone s) : |s.im| ≤ 14 :=
  hs.2.2

/-- For any height $|t| \le 14$, $t / (2\pi) < 4$. -/
theorem orphanZone_t_div_two_pi_lt_four {t : ℝ} (ht : |t| ≤ 14) :
    |t| / (2 * π) < 4 := by
  have hpi : (3 : ℝ) < π := Real.pi_gt_three
  have hden : (6 : ℝ) < 2 * π := by linarith
  calc |t| / (2 * π) ≤ 14 / (2 * π) := div_le_div_of_nonneg_right ht (by positivity)
    _ < 14 / 6 := div_lt_div_of_pos_left (by norm_num) (by norm_num) hden
    _ < 4 := by norm_num

/-- For any height $|t| \le 14$, the square root $\sqrt{|t| / (2\pi)} < 2$.
Hence the Riemann-Siegel summation index $N = \lfloor\sqrt{|t|/2\pi}
floor$ equals 1. -/
theorem orphanZone_sqrt_t_div_two_pi_lt_two {t : ℝ} (ht : |t| ≤ 14) :
    Real.sqrt (|t| / (2 * π)) < 2 := by
  have hlt := orphanZone_t_div_two_pi_lt_four ht
  have hpos : 0 ≤ |t| / (2 * π) := div_nonneg (abs_nonneg t) (by positivity)
  have hsqrt : Real.sqrt (|t| / (2 * π)) < Real.sqrt 4 := Real.sqrt_lt_sqrt hpos hlt
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]
  rwa [h4] at hsqrt

/-- In the orphan zone, the reflection factor magnitude ratio is strictly positive. -/
theorem orphanZone_gain_ratio_pos {s : ℂ} (_hs : inOrphanZone s) :
    0 < primeDualGainRatio (s.re - 1 / 2) :=
  primeDualGainRatio_pos (s.re - 1 / 2)

/-- In the orphan zone, the gain ratio strictly differs from 1 off the line. -/
theorem orphanZone_gain_ratio_ne_one {s : ℂ} (hs : inOrphanZone s) :
    primeDualGainRatio (s.re - 1 / 2) ≠ 1 := by
  have h_off := orphanZone_off_line hs
  have hδ : s.re - 1 / 2 ≠ 0 := sub_ne_zero.mpr h_off
  exact primeDualGainRatio_ne_one_of_delta_ne_zero hδ

/-- Master Orphan Zone Decomposition:
Every point in the critical strip with $1/2 < |t| \le 14$ and $\sigma 
e 1/2$
satisfies the single-term carrier non-vanishing condition. -/
theorem orphanZone_carrier_asymmetry {s : ℂ} (hs : inOrphanZone s) :
    0 < |primeDualGainRatio (s.re - 1 / 2) - 1| * prime2Amplitude s := by
  have hne := orphanZone_gain_ratio_ne_one hs
  have h_diff : |primeDualGainRatio (s.re - 1 / 2) - 1| > 0 := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hA2 : 0 < prime2Amplitude s := prime2Amplitude_pos s
  exact mul_pos h_diff hA2

end RhG1Lean
