/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under CC-BY 4.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import RhG1Lean.Leftover
import RhG1Lean.LeftoverCompact
import RhG1Lean.Split
import RhG1Lean.Nonvanishing

/-!
# Gap 5.1 advance — right face and near s=1

1. Closed right face of leftoverRect: ζ ≠ 0 for Re ≥ 1.
2. A neighborhood of s = 1 meets leftoverRect zero-free
   (
iemannZeta_eventually_ne_zero_nhds_one).
3. Remaining OPEN locus: leftoverInterior = leftoverRect ∩ {Re s < 1}.
4. Zeros of leftoverRect lie in leftoverInterior \ U for a nbhd U of 1.

Does not claim leftoverRect empty. Does not declare RH.
-/

open Complex Filter Topology Set

namespace RhG1Lean

/-! ### Closed right face of the leftover box -/

/-- Points of leftoverRect with real part at least 1. -/
def leftoverRectRight : Set ℂ :=
  leftoverRect ∩ {s : ℂ | 1 ≤ s.re}

lemma mem_leftoverRectRight {s : ℂ} :
    s ∈ leftoverRectRight ↔ s ∈ leftoverRect ∧ 1 ≤ s.re :=
  Iff.rfl

/--
ζ has no zeros on the closed right face of leftoverRect (Re ≥ 1).
Generalizes leftoverRect_right_edge_zeta_ne_zero.
-/
theorem leftoverRect_right_zeta_ne_zero {s : ℂ}
    (hs : s ∈ leftoverRectRight) :
    riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hs.2

/-- ξ nonvanishing on the same closed right face, excluding s=0 and s=1. -/
theorem leftoverRect_right_xi_ne_zero {s : ℂ}
    (hs : s ∈ leftoverRectRight) (hs1 : s ≠ 1) (hs0 : s ≠ 0) :
    riemannXi s ≠ 0 :=
  riemannXi_ne_zero_of_one_le_re hs.2 hs1 hs0

/-! ### Neighborhood of s = 1 inside leftoverRect -/

/--
From mathlib 
iemannZeta_eventually_ne_zero_nhds_one:
there is a neighborhood of 1 on which ζ has no zeros.
-/
theorem exists_nhds_one_leftoverRect_zeta_ne_zero :
    ∃ U ∈ 𝓝 (1 : ℂ), ∀ s ∈ U ∩ leftoverRect, riemannZeta s ≠ 0 := by
  obtain ⟨U, hU, hOpen, h1⟩ := eventually_nhds_iff.mp riemannZeta_eventually_ne_zero_nhds_one
  refine ⟨U, IsOpen.mem_nhds hOpen h1, ?_⟩
  intro s hs
  exact hU s hs.1

/-- Same fact packaged with an explicit open set containing 1. -/
theorem exists_open_nhds_one_leftoverRect_zeta_ne_zero :
    ∃ U : Set ℂ, IsOpen U ∧ (1 : ℂ) ∈ U ∧
      ∀ s ∈ U ∩ leftoverRect, riemannZeta s ≠ 0 := by
  obtain ⟨U, _hU, hne⟩ := exists_nhds_one_leftoverRect_zeta_ne_zero
  obtain ⟨V, hVU, hVopen, h1V⟩ := mem_nhds_iff.mp _hU
  refine ⟨V, hVopen, h1V, ?_⟩
  intro s hs
  exact hne s ⟨hVU hs.1, hs.2⟩

/-! ### Remaining OPEN interior — reduction of gap 5.1 -/

/-- Still-OPEN part of gap 5.1: leftoverRect with Re s < 1. -/
def leftoverInterior : Set ℂ :=
  leftoverRect ∩ {s : ℂ | s.re < 1}

lemma mem_leftoverInterior {s : ℂ} :
    s ∈ leftoverInterior ↔ s ∈ leftoverRect ∧ s.re < 1 :=
  Iff.rfl

lemma leftoverRect_eq_right_union_interior :
    leftoverRect = leftoverRectRight ∪ leftoverInterior := by
  ext s
  constructor
  · intro hs
    by_cases h : 1 ≤ s.re
    · exact Or.inl ⟨hs, h⟩
    · exact Or.inr ⟨hs, lt_of_not_ge h⟩
  · intro h
    exact h.elim (fun hr => hr.1) (fun hi => hi.1)

/--
**Reduction of gap 5.1.** Any ζ-zero in leftoverRect lies in leftoverInterior.
-/
theorem zeta_zero_mem_leftoverRect_imp_leftoverInterior {s : ℂ}
    (hs : s ∈ leftoverRect) (hz : riemannZeta s = 0) :
    s ∈ leftoverInterior := by
  by_cases hre : 1 ≤ s.re
  · exact (leftoverRect_right_zeta_ne_zero ⟨hs, hre⟩ hz).elim
  · exact ⟨hs, lt_of_not_ge hre⟩

/-- No ζ-zeros on leftoverRect \ leftoverInterior. -/
theorem leftoverRect_diff_interior_zeta_ne_zero {s : ℂ}
    (hs : s ∈ leftoverRect \ leftoverInterior) :
    riemannZeta s ≠ 0 := by
  have hsR : s ∈ leftoverRect := hs.1
  have hre : 1 ≤ s.re := le_of_not_gt fun h => hs.2 ⟨hsR, h⟩
  exact leftoverRect_right_zeta_ne_zero ⟨hsR, hre⟩

/-! ### Shrink leftoverInterior by nhds(1) -/

/--
Any ζ-zero in leftoverInterior lies outside every zero-free set U
on U ∩ leftoverRect.
-/
theorem zeta_zero_leftoverInterior_notMem_nhds_one
    {U : Set ℂ}
    (hne : ∀ s ∈ U ∩ leftoverRect, riemannZeta s ≠ 0)
    {s : ℂ} (hs : s ∈ leftoverInterior) (hz : riemannZeta s = 0) :
    s ∉ U := by
  intro hsU
  exact hne s ⟨hsU, hs.1⟩ hz

/--
**Reduction.** If U is zero-free on leftoverRect, then every ζ-zero
of leftoverRect lies in leftoverInterior \ U.
-/
theorem zeta_zero_mem_leftoverInterior_diff_nhds
    {U : Set ℂ}
    (hne : ∀ s ∈ U ∩ leftoverRect, riemannZeta s ≠ 0)
    {s : ℂ} (hs : s ∈ leftoverRect) (hz : riemannZeta s = 0) :
    s ∈ leftoverInterior \ U :=
  ⟨zeta_zero_mem_leftoverRect_imp_leftoverInterior hs hz,
    zeta_zero_leftoverInterior_notMem_nhds_one hne
      (zeta_zero_mem_leftoverRect_imp_leftoverInterior hs hz) hz⟩

/-- Concrete form using the mathlib nbhd existence. -/
theorem exists_open_cut_leftoverInterior_zeros :
    ∃ U : Set ℂ, IsOpen U ∧ (1 : ℂ) ∈ U ∧
      ∀ s ∈ leftoverRect, riemannZeta s = 0 → s ∈ leftoverInterior \ U := by
  obtain ⟨U, hOpen, h1, hne⟩ := exists_open_nhds_one_leftoverRect_zeta_ne_zero
  refine ⟨U, hOpen, h1, ?_⟩
  intro s hs hz
  exact zeta_zero_mem_leftoverInterior_diff_nhds hne hs hz

end RhG1Lean
