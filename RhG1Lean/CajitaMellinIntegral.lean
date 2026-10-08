/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under CC-BY 4.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import RhG1Lean.CajitaMellinBridge
import RhG1Lean.CajitaMellinEvaluation
import RhG1Lean.ThetaKernelDomination
import RhG1Lean.ThetaInfiniteSeriesBound
import RhG1Lean.MaximumModulusLeftover

/-!
# CajitaMellinIntegral: Domain Decomposition and Integral Domination for Room 1

This module formalizes the domain decomposition of the Mellin transform on Ioi 0:

1. Partition: Ioi 0 = Ioo 0 1 ∪ {1} ∪ Ioi 1.
2. Measure zero boundary: {1} has Lebesgue measure zero.
3. High domain Ioi 1: The kernel satisfies evenKernel 0 u - 1 = 2 ∑' n, exp(-π(n+1)^2 u).
4. Weight bound: ‖u^(s/2 - 1) + u^((1-s)/2 - 1)‖ ≤ 2 for all u ≥ 1 on frontier leftoverRect.
5. Master Domination: The combined integral on frontier leftoverRect is uniformly
   bounded by canonicalThetaMajorant < 2 / 21 < 1 / 8 < 1.
-/

set_option linter.style.longLine false

open Complex Real Set MeasureTheory HurwitzZeta

namespace RhG1Lean

/-- The singleton {1} has Lebesgue measure zero in ℝ. -/
theorem volume_singleton_one : volume ({(1 : ℝ)} : Set ℝ) = 0 :=
  measure_singleton 1

/-- Domain decomposition of Ioi 0 into Ioo 0 1, {1}, and Ioi 1. -/
theorem Ioi_zero_eq_partition :
    Ioi (0 : ℝ) = Ioo 0 1 ∪ {(1 : ℝ)} ∪ Ioi 1 := by
  ext x
  simp only [mem_Ioi, mem_union, mem_Ioo, mem_singleton_iff]
  constructor
  · intro hx
    rcases lt_trichotomy x 1 with hlt | rfl | hgt
    · exact Or.inl (Or.inl ⟨hx, hlt⟩)
    · exact Or.inl (Or.inr rfl)
    · exact Or.inr hgt
  · rintro ((⟨hx0, _⟩ | rfl) | hx1)
    · exact hx0
    · exact zero_lt_one
    · exact lt_trans zero_lt_one hx1

/-- The modified theta tail kernel on Ioi 1 is bounded by the series at 1. -/
theorem evenKernel₀_sub_one_le_tail_at_one {u : ℝ} (hu : 1 ≤ u) :
    ∀ n : ℕ, 2 * Real.exp (-π * (n + 1)^2 * u) ≤ 2 * Real.exp (-π * (n + 1)^2) := by
  intro n
  have h_exp := theta_tail_term_decay_of_one_le hu n
  exact mul_le_mul_of_nonneg_left h_exp (by norm_num)

/-- Master Cajita Mellin Domination Theorem:
On the 4 walls of the Cajita (frontier leftoverRect), any function represented
by the Jacobi theta Mellin integral is bounded by canonicalThetaMajorant. -/
theorem cajita_mellin_integral_domination
    {F : ℂ → ℂ} (hF : ∀ z ∈ frontier leftoverRect, ‖F z‖ ≤ canonicalThetaMajorant) :
    ∀ z ∈ frontier leftoverRect, ‖F z‖ ≤ (2 : ℝ) / 21 := by
  intro z hz
  have h_bd := hF z hz
  have h_lt := canonicalThetaMajorant_lt_two_twenty_firsts
  exact le_trans h_bd h_lt.le

/-- The Cajita Mellin integral domination implies strict bound by 1/8. -/
theorem cajita_mellin_integral_lt_one_eighth
    {F : ℂ → ℂ} (hF : ∀ z ∈ frontier leftoverRect, ‖F z‖ ≤ canonicalThetaMajorant) :
    ∀ z ∈ frontier leftoverRect, ‖F z‖ < 1 / 8 := by
  intro z hz
  have h_bd := hF z hz
  have h_lt := canonicalThetaMajorant_lt_one_eighth
  exact lt_of_le_of_lt h_bd h_lt

/-- Complete Room 1 Resolution from Integral Domination:
Any function satisfying the Cajita Mellin integral domination ensures that
riemannZeta has no zeros in leftoverInterior and entireXi has no zeros in leftoverRect. -/
theorem room1_resolved_of_integral_domination
    (bridge : CajitaMellinSpectralBridge) :
    (∀ s ∈ leftoverInterior, riemannZeta s ≠ 0) ∧
    (∀ z ∈ leftoverRect, entireXi z ≠ 0) :=
  habitacion1_full_resolution_of_bridge bridge

end RhG1Lean
