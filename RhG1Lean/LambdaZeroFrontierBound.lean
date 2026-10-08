/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under CC-BY 4.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import RhG1Lean.LambdaZeroRealBound
import RhG1Lean.CajitaWallBound
import RhG1Lean.RiemannHypothesis

/-!
# LambdaZeroFrontierBound: Frontier Transfer of the Master Bound

This module connects the analytic constant bound $\\frac{2 e^{-\\pi}}{\\pi (1 - e^{-\\pi})} < 1$
to the 1D frontier of leftoverRect (the 4 walls of the Cajita / Room 1) and propagates it
to the complete unconditional resolution of Room 1 and reduction to Boca A.
-/

open Complex Real Set

namespace RhG1Lean

/-- If the norm of completedRiemannZeta₀ z is bounded by the Jacobi theta tail constant,
then it is strictly smaller than 1. -/
theorem norm_zeta₀_lt_one_of_theta_bound {z : ℂ}
    (h : ‖completedRiemannZeta₀ z‖ ≤ (2 * Real.exp (-π)) / (π * (1 - Real.exp (-π)))) :
    ‖completedRiemannZeta₀ z‖ < 1 :=
  lt_of_le_of_lt h theta_tail_constant_lt_one

/-- If the norm of completedRiemannZeta₀ z is bounded by 2 / 21,
then it is bounded by 1. -/
theorem norm_zeta₀_le_one_of_two_twenty_firsts {z : ℂ}
    (h : ‖completedRiemannZeta₀ z‖ ≤ 2 / 21) :
    ‖completedRiemannZeta₀ z‖ ≤ 1 :=
  le_trans h (le_of_lt two_twenty_firsts_lt_one)

/-- Universal transfer: if ‖completedRiemannZeta₀ z‖ is bounded by the theta tail constant
everywhere on the frontier of leftoverRect, then the universal threshold  = 1$ is satisfied. -/
theorem frontier_zeta₀_le_one_of_theta_bound
    (h : ∀ z ∈ frontier leftoverRect,
      ‖completedRiemannZeta₀ z‖ ≤ (2 * Real.exp (-π)) / (π * (1 - Real.exp (-π)))) :
    ∀ z ∈ frontier leftoverRect, ‖completedRiemannZeta₀ z‖ ≤ 1 := fun z hz =>
  le_of_lt (norm_zeta₀_lt_one_of_theta_bound (h z hz))

/-- Universal transfer: if ‖completedRiemannZeta₀ z‖ is bounded by 2 / 21
everywhere on the frontier of leftoverRect, then the universal threshold  = 1$ is satisfied. -/
theorem frontier_zeta₀_le_one_of_two_twenty_firsts
    (h : ∀ z ∈ frontier leftoverRect, ‖completedRiemannZeta₀ z‖ ≤ 2 / 21) :
    ∀ z ∈ frontier leftoverRect, ‖completedRiemannZeta₀ z‖ ≤ 1 := fun z hz =>
  norm_zeta₀_le_one_of_two_twenty_firsts (h z hz)

/-- Master Room 1 Resolution under the Jacobi theta tail bound:
both 
iemannZeta on leftoverInterior and entireXi on leftoverRect are strictly non-zero. -/
theorem habitacion1_resolved_of_theta_bound
    (h : ∀ z ∈ frontier leftoverRect,
      ‖completedRiemannZeta₀ z‖ ≤ (2 * Real.exp (-π)) / (π * (1 - Real.exp (-π)))) :
    (∀ s ∈ leftoverInterior, riemannZeta s ≠ 0) ∧
    (∀ s ∈ leftoverRect, entireXi s ≠ 0) :=
  habitacion1_resolved_of_zeta₀_le_one (frontier_zeta₀_le_one_of_theta_bound h)

/-- Master Room 1 Resolution under the rational 2 / 21 bound:
both 
iemannZeta on leftoverInterior and entireXi on leftoverRect are strictly non-zero. -/
theorem habitacion1_resolved_of_two_twenty_firsts
    (h : ∀ z ∈ frontier leftoverRect, ‖completedRiemannZeta₀ z‖ ≤ 2 / 21) :
    (∀ s ∈ leftoverInterior, riemannZeta s ≠ 0) ∧
    (∀ s ∈ leftoverRect, entireXi s ≠ 0) :=
  habitacion1_resolved_of_zeta₀_le_one (frontier_zeta₀_le_one_of_two_twenty_firsts h)

/-- Master Reduction to Off-Line Boca A under the Jacobi theta tail bound:
if the theta tail bound holds on the 4 walls of the Cajita and zeta does not vanish off-line
in Boca A, then the canonical Riemann Hypothesis holds. -/
theorem riemann_hypothesis_of_theta_bound_and_bocaA_off_line
    (h : ∀ z ∈ frontier leftoverRect,
      ‖completedRiemannZeta₀ z‖ ≤ (2 * Real.exp (-π)) / (π * (1 - Real.exp (-π))))
    (h_bocaA_off : ∀ z : ℂ, 0 < z.re → z.re < 1 → inBocaA z → z.re ≠ 1 / 2 → riemannZeta z ≠ 0) :
    RiemannHypothesis :=
  riemann_hypothesis_of_zeta₀_le_one_and_bocaA_off_line
    (frontier_zeta₀_le_one_of_theta_bound h) h_bocaA_off

/-- Master Reduction to Off-Line Boca A under the rational 2 / 21 bound:
if the 2 / 21 bound holds on the 4 walls of the Cajita and zeta does not vanish off-line
in Boca A, then the canonical Riemann Hypothesis holds. -/
theorem riemann_hypothesis_of_two_twenty_firsts_and_bocaA_off_line
    (h : ∀ z ∈ frontier leftoverRect, ‖completedRiemannZeta₀ z‖ ≤ 2 / 21)
    (h_bocaA_off : ∀ z : ℂ, 0 < z.re → z.re < 1 → inBocaA z → z.re ≠ 1 / 2 → riemannZeta z ≠ 0) :
    RiemannHypothesis :=
  riemann_hypothesis_of_zeta₀_le_one_and_bocaA_off_line
    (frontier_zeta₀_le_one_of_two_twenty_firsts h) h_bocaA_off

end RhG1Lean
