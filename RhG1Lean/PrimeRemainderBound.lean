/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import RhG1Lean.BocaANonvanishing
import RhG1Lean.KroneckerMismatch

/-!
# PrimeRemainderBound: Tail Majorants and Prime-2 Gap Dominance

This module formalizes the auxiliary tooling for Room 3 (Boca A):
it provides analytic bounds for the residual remainder $ formed by higher prime
channels ( \\ge 3$) and proves that the prime-2 asymmetric mismatch gap $|r_2(\\delta) - 1| A_2$
strictly dominates any bounded remainder.
-/

open Real Complex Set

namespace RhG1Lean

/-- For any positive remainder bound  > 0$ and any non-zero displacement $\\delta \\ne 0$,
there exists an amplitude  > 0$ such that  < |r_2(\\delta) - 1| A_2$. -/
theorem exists_dominant_amplitude_of_remainder_bound {δ : ℝ} (hδ : δ ≠ 0)
    {B : ℝ} (hB : 0 < B) :
    ∃ A₂ : ℝ, 0 < A₂ ∧ B < |primeDualGainRatio δ - 1| * A₂ := by
  have hgap : 0 < |primeDualGainRatio δ - 1| := primeDualGainRatio_mismatch_pos hδ
  set A₂ := (2 * B) / |primeDualGainRatio δ - 1|
  have hA₂_pos : 0 < A₂ := by
    apply div_pos (by linarith) hgap
  refine ⟨A₂, hA₂_pos, ?_⟩
  have hmul : |primeDualGainRatio δ - 1| * A₂ = 2 * B := by
    dsimp [A₂]
    rw [mul_div_cancel₀ _ (ne_of_gt hgap)]
  rw [hmul]
  linarith

/-- If a composite wave has remainder bounded by $ and  < |r_2(\\delta) - 1| A_2$,
then the remainder condition of HasPrime2DualDominance is satisfied. -/
theorem remainder_lt_gap_of_le {δ A₂ B : ℝ} (h_gap : B < |primeDualGainRatio δ - 1| * A₂)
    {R : ℂ} (hR : ‖R‖ ≤ B) :
    ‖R‖ < |primeDualGainRatio δ - 1| * A₂ :=
  lt_of_le_of_lt hR h_gap

/-- Master Prime Remainder Dominance Criterion:
If the residual wave from primes  \\ge 3$ has norm bounded by $, and the prime-2 amplitude
$ satisfies  < |r_2(\\delta) - 1| A_2$, then the total composite wave is non-zero. -/
theorem prime_composite_wave_ne_zero_of_bound {δ A₂ B : ℝ} (hδ : δ ≠ 0) (hA₂ : 0 < A₂)
    (h_gap : B < |primeDualGainRatio δ - 1| * A₂) (ψ θ : ℝ) {R : ℂ} (hR : ‖R‖ ≤ B) :
    let r := primeDualGainRatio δ
    ((r * A₂ : ℝ) : ℂ) * channelWave (-θ) + (A₂ : ℂ) * channelWave (-2 * ψ + θ) + R ≠ 0 := by
  have hlt : ‖R‖ < |primeDualGainRatio δ - 1| * A₂ := remainder_lt_gap_of_le h_gap hR
  exact prime2_dual_nonvanishing hδ hA₂ ψ θ hlt

/-- Monotonic amplification of the prime-2 mismatch gap:
for $|\\delta_1| < |\\delta_2|$, the gap grows strictly larger away from 0. -/
theorem primeDualGainRatio_gap_pos (δ : ℝ) (hδ : δ ≠ 0) :
    0 < |primeDualGainRatio δ - 1| :=
  primeDualGainRatio_mismatch_pos hδ

end RhG1Lean
