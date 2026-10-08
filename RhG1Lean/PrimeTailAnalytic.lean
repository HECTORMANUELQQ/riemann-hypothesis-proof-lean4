/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Group.Basic
import RhG1Lean.KroneckerMismatch
import RhG1Lean.BocaADualCancellation
import RhG1Lean.BocaANonvanishing
import RhG1Lean.PrimeRemainderBound
import RhG1Lean.Prime2LinearGap

/-!
# PrimeTailAnalytic: Analytic Tail Bounds for Higher Primes in Boca A

This module formalizes the quantitative barrier against vanishing for composite waves
in the Boca A regime:

$$\|R\| \le \frac{1}{2} (|\delta| \log 2) A_2 < |r_2(\delta) - 1| A_2.$$

Any higher-prime remainder $R$ bounded by half of the linear gap guarantees strict
prime-2 dual dominance and prohibits vanishing off the critical line.
-/

set_option linter.style.longLine false

open Real Complex Set

namespace RhG1Lean

/-- Predicate stating that a higher-prime remainder $R$ is bounded by a safe fraction
of the linear gap $(|\delta| \log 2) A_2$. -/
def HasSafePrimeTailBound (R : ℂ) (δ A₂ : ℝ) : Prop :=
  ‖R‖ ≤ (1 / 2 : ℝ) * (|δ| * Real.log 2) * A₂

/-- A safe prime tail bound strictly implies the gap condition $\|R\| < (|\delta| \log 2) A_2$. -/
theorem remainder_lt_linear_gap_of_safe_bound {R : ℂ} {δ A₂ : ℝ}
    (hδ_ne : δ ≠ 0) (hA₂ : 0 < A₂)
    (h_safe : HasSafePrimeTailBound R δ A₂) :
    ‖R‖ < (|δ| * Real.log 2) * A₂ := by
  unfold HasSafePrimeTailBound at h_safe
  have hpos : 0 < (|δ| * Real.log 2) * A₂ := by
    have hlin := primeDualGainRatio_linear_bound_pos hδ_ne
    exact mul_pos hlin hA₂
  have hhalf : (1 / 2 : ℝ) * ((|δ| * Real.log 2) * A₂) < (|δ| * Real.log 2) * A₂ := by
    linarith
  have h_mul_assoc : (1 / 2 : ℝ) * (|δ| * Real.log 2) * A₂ = (1 / 2 : ℝ) * ((|δ| * Real.log 2) * A₂) := by
    ring
  rw [h_mul_assoc] at h_safe
  exact lt_of_le_of_lt h_safe hhalf

/-- **Master Dominance from Safe Prime Tail Bound**:
If $R$ obeys the safe tail bound, the composite wave has prime-2 dual dominance. -/
theorem hasPrime2DualDominance_of_safe_bound {w : ℂ} {δ A₂ : ℝ}
    (hδ_mem : δ ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) (hδ_ne : δ ≠ 0) (hA₂ : 0 < A₂)
    (ψ θ : ℝ) (R : ℂ)
    (h_safe : HasSafePrimeTailBound R δ A₂)
    (hw : w = ((primeDualGainRatio δ * A₂ : ℝ) : ℂ) * channelWave (-θ) +
              (A₂ : ℂ) * channelWave (-2 * ψ + θ) + R) :
    HasPrime2DualDominance w δ := by
  have hlt := remainder_lt_linear_gap_of_safe_bound hδ_ne hA₂ h_safe
  exact hasPrime2DualDominance_of_linear_bound hδ_mem hδ_ne hA₂ ψ θ R hlt hw

/-- **Master Non-vanishing from Safe Prime Tail Bound**:
Any composite wave with a safe prime tail bound cannot vanish off the critical line. -/
theorem ne_zero_of_safe_bound {w : ℂ} {δ A₂ : ℝ}
    (hδ_mem : δ ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) (hδ_ne : δ ≠ 0) (hA₂ : 0 < A₂)
    (ψ θ : ℝ) (R : ℂ)
    (h_safe : HasSafePrimeTailBound R δ A₂)
    (hw : w = ((primeDualGainRatio δ * A₂ : ℝ) : ℂ) * channelWave (-θ) +
              (A₂ : ℂ) * channelWave (-2 * ψ + θ) + R) :
    w ≠ 0 := by
  have hdom := hasPrime2DualDominance_of_safe_bound hδ_mem hδ_ne hA₂ ψ θ R h_safe hw
  exact ne_zero_of_hasPrime2DualDominance hδ_ne hdom

/-- Critical strip specialization: for any $s$ in the critical strip off the line,
a safe remainder bound ensures non-vanishing. -/
theorem strip_ne_zero_of_safe_bound {w : ℂ} {s : ℂ} {A₂ : ℝ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (hne : s.re ≠ 1 / 2) (hA₂ : 0 < A₂)
    (ψ θ : ℝ) (R : ℂ)
    (h_safe : HasSafePrimeTailBound R (s.re - 1 / 2) A₂)
    (hw : w = ((primeDualGainRatio (s.re - 1 / 2) * A₂ : ℝ) : ℂ) * channelWave (-θ) +
              (A₂ : ℂ) * channelWave (-2 * ψ + θ) + R) :
    w ≠ 0 := by
  have hδ_mem : s.re - 1 / 2 ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) := ⟨by linarith, by linarith⟩
  have hδ_ne : s.re - 1 / 2 ≠ 0 := sub_ne_zero.mpr hne
  exact ne_zero_of_safe_bound hδ_mem hδ_ne hA₂ ψ θ R h_safe hw

end RhG1Lean
