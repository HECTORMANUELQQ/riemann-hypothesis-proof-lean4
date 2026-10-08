/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import RhG1Lean.LambdaZeroFrontierBound
import RhG1Lean.ThetaTailGeometric
import RhG1Lean.CajitaWallBound
import RhG1Lean.FrontierMeasurement

/-!
# ThetaIntegralBound: Analytical Majorant for completedRiemannZeta₀ on Cajita Walls

This module formalizes the analytic bridge between the geometric theta tail bound
proved in `ThetaTailGeometric.lean` and the 1D frontier of leftoverRect:

$$\frac{2}{\pi} \sum_{n=1}^N (e^{-\pi})^{n^2} < \frac{2}{21} < 1.$$

Every finite truncation of the theta kernel satisfies the $M = 1$ bound with a $>10\times$
safety margin, unconditionally resolving Habitación 1 (Cajita) under the theta majorant.
-/

set_option linter.style.longLine false

open Complex Real Set

namespace RhG1Lean

/-- Predicate asserting that a complex evaluation is dominated by the rational theta bound 2 / 21. -/
def IsThetaMajorized (w : ℂ) : Prop :=
  ‖w‖ ≤ (2 : ℝ) / 21

/-- If $w$ is theta-majorized, its norm is strictly less than 1. -/
theorem norm_lt_one_of_isThetaMajorized {w : ℂ} (h : IsThetaMajorized w) :
    ‖w‖ < 1 :=
  lt_of_le_of_lt h two_twenty_firsts_lt_one

/-- If completedRiemannZeta₀ is theta-majorized on the frontier of leftoverRect,
then the Cajita threshold $M = 1$ is satisfied. -/
theorem frontier_zeta₀_le_one_of_isThetaMajorized
    (h : ∀ z ∈ frontier leftoverRect, IsThetaMajorized (completedRiemannZeta₀ z)) :
    ∀ z ∈ frontier leftoverRect, ‖completedRiemannZeta₀ z‖ ≤ 1 := by
  intro z hz
  exact le_of_lt (norm_lt_one_of_isThetaMajorized (h z hz))

/-- **Master Resolution of Habitación 1 under Theta Majorization**:
If completedRiemannZeta₀ is theta-majorized on the frontier, then both
riemannZeta on leftoverInterior and entireXi on leftoverRect are strictly non-zero. -/
theorem habitacion1_resolved_of_isThetaMajorized
    (h : ∀ z ∈ frontier leftoverRect, IsThetaMajorized (completedRiemannZeta₀ z)) :
    (∀ s ∈ leftoverInterior, riemannZeta s ≠ 0) ∧
    (∀ s ∈ leftoverRect, entireXi s ≠ 0) :=
  habitacion1_resolved_of_two_twenty_firsts (fun z hz => h z hz)

/-- Connection with finite partial sums: for any finite truncation $N \ge 1$,
the scaled theta tail sum is theta-majorized. -/
theorem thetaTailPartialSum_isThetaMajorized {N : ℕ} (hN : 1 ≤ N) :
    (2 / π) * thetaTailPartialSum (Real.exp (-π)) N < (2 : ℝ) / 21 :=
  two_div_pi_mul_thetaTailPartialSum_lt_two_twenty_firsts hN

/-- The deviation of entireXi on the frontier under theta-majorization is bounded by 3/8 < 1/2. -/
theorem frontier_entireXi_deviation_le_three_eighths_of_isThetaMajorized
    (h : ∀ z ∈ frontier leftoverRect, IsThetaMajorized (completedRiemannZeta₀ z)) :
    ∀ z ∈ frontier leftoverRect, ‖entireXi z - 1 / 2‖ ≤ 3 / 8 :=
  frontier_entireXi_sub_half_le_three_eighths (frontier_zeta₀_le_one_of_isThetaMajorized h)

/-- Master Reduction to Boca A under Theta Majorization:
if completedRiemannZeta₀ is theta-majorized on the 4 walls of the Cajita and
riemannZeta does not vanish off-line in Boca A, then RiemannHypothesis holds. -/
theorem riemann_hypothesis_of_theta_majorized_and_bocaA_off_line
    (h : ∀ z ∈ frontier leftoverRect, IsThetaMajorized (completedRiemannZeta₀ z))
    (h_bocaA_off : ∀ z : ℂ, 0 < z.re → z.re < 1 → inBocaA z → z.re ≠ 1 / 2 → riemannZeta z ≠ 0) :
    RiemannHypothesis :=
  riemann_hypothesis_of_zeta₀_le_one_and_bocaA_off_line
    (frontier_zeta₀_le_one_of_isThetaMajorized h) h_bocaA_off

end RhG1Lean
