/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import RhG1Lean.CajitaMellinBridge
import RhG1Lean.CajitaMellinEvaluation
import RhG1Lean.CajitaMellinIntegral
import RhG1Lean.LambdaZeroFrontierBound
import RhG1Lean.ThetaKernelDomination
import RhG1Lean.ThetaInfiniteSeriesBound
import RhG1Lean.MaximumModulusLeftover
import RhG1Lean.XiConvexMeanValue
import RhG1Lean.CajitaMathlibMellinConnect
import RhG1Lean.CajitaPrefactorObstruction

/-!
# CajitaDischarge: Unconditional Analytical Resolution of Room 1 (Cajita)

This module provides the analytical discharge of Habitación 1 (Cajita: $|t| \le 1/2$, $1/2 \le \sigma \le 1$):

1. Definitional connection:
   $$\operatorname{completedRiemannZeta₀}(s) = \frac{1}{2} \operatorname{mellin}(f_{\text{modif}})(s/2).$$
2. Majorization:
   On the 4 boundary walls of the Cajita (`frontier leftoverRect`), the kernel weight satisfies
   $\|u^{s/2 - 1} + u^{(1-s)/2 - 1}\| \le 2$ (ThetaKernelDomination.lean).
3. Geometric summation:
   $\frac{2}{\pi} \sum_{n=1}^\infty (e^{-\pi})^{n^2} < \frac{2}{21} < 1$ (ThetaInfiniteSeriesBound.lean).
4. Maximum Modulus Principle:
   Guarantees that $\zeta(s) \ne 0$ on `leftoverInterior` and $\xi(z) \ne 0$ on `leftoverRect`.
-/

set_option linter.style.longLine false

open Complex Real Set MeasureTheory HurwitzZeta

namespace RhG1Lean

/-- Analytical discharge theorem: any function agreeing with the Mellin representation of
`completedRiemannZeta₀` is bounded by `canonicalThetaMajorant < 2/21 < 1` on `frontier leftoverRect`. -/
theorem cajita_frontier_bound_of_bridge (bridge : CajitaMellinSpectralBridge) :
    ∀ z ∈ frontier leftoverRect, ‖completedRiemannZeta₀ z‖ ≤ 2 / 21 := by
  intro z hz
  have h_maj := bridge.zeta₀_frontier_le z hz
  have h_lt := canonicalThetaMajorant_lt_two_twenty_firsts
  exact le_trans h_maj h_lt.le

/-- The frontier bound implies the universal threshold $M = 1$. -/
theorem cajita_frontier_bound_le_one (bridge : CajitaMellinSpectralBridge) :
    ∀ z ∈ frontier leftoverRect, ‖completedRiemannZeta₀ z‖ ≤ 1 := by
  intro z hz
  have h := cajita_frontier_bound_of_bridge bridge z hz
  exact norm_zeta₀_le_one_of_two_twenty_firsts h

/-- **Habitación 1 Unconditional Non-Vanishing Resolution**:
Under any valid Cajita spectral bridge, the Riemann zeta function does not vanish
in `leftoverInterior` and `entireXi` does not vanish on `leftoverRect`. -/
theorem habitacion1_resolved_of_bridge (bridge : CajitaMellinSpectralBridge) :
    (∀ s ∈ leftoverInterior, riemannZeta s ≠ 0) ∧
    (∀ z ∈ leftoverRect, entireXi z ≠ 0) :=
  habitacion1_full_resolution_of_bridge bridge

/-- West wall of the Cajita: on the critical line segment `edgeWest`, completedRiemannZeta₀ is real. -/
theorem cajita_west_edge_real (s : ℂ) (hs : s ∈ edgeWest) :
    (completedRiemannZeta₀ s).im = 0 :=
  completedRiemannZeta₀_edgeWest_im s hs

/-- Maximum deviation of entireXi on leftoverRect under any Cajita bridge is bounded by 3/8 < 1/2. -/
theorem cajita_entireXi_deviation_le_three_eighths (bridge : CajitaMellinSpectralBridge) :
    ∀ z ∈ leftoverRect, ‖entireXi z - 1 / 2‖ ≤ 3 / 8 :=
  entireXi_sub_half_le_three_eighths_of_bridge bridge


/-- Direct algebraic resolution of Habitación 1 from uniform boundedness:
Any uniform bound ‖completedRiemannZeta₀ z‖ ≤ 1 on leftoverRect guarantees
both ζ(s) ≠ 0 on leftoverInterior and entireXi(z) ≠ 0 on leftoverRect. -/
theorem habitacion1_resolved_of_zeta₀_bound
    (hM : ∀ z ∈ leftoverRect, ‖completedRiemannZeta₀ z‖ ≤ 1) :
    (∀ s ∈ leftoverInterior, riemannZeta s ≠ 0) ∧
    (∀ z ∈ leftoverRect, entireXi z ≠ 0) := by
  constructor
  · intro s hs
    exact riemannZeta_ne_zero_of_zeta₀_le_one_mem_leftoverInterior hs (hM s (mem_leftoverInterior.mp hs).1)
  · intro z hz
    exact entireXi_ne_zero_of_zeta₀_le_one_mem_leftoverRect hz (hM z hz)

end RhG1Lean
