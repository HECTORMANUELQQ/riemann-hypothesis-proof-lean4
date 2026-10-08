/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under CC-BY 4.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import RhG1Lean.Split
import RhG1Lean.LeftoverNonvanishing
import RhG1Lean.XiEntire
import RhG1Lean.DualCancellation
import RhG1Lean.KroneckerMismatch

/-!
# StripReduction: Decomposition of the Critical Strip and RH Reduction

This module proves:
1. Every point in the critical strip `0 < Re s < 1` falls into exactly one of four regions:
   - The critical line `Re s = 1/2`.
   - `leftoverInterior` (East low box: `1/2 < Re s < 1` and `|Im s| ≤ 1/2`).
   - `1 - s ∈ leftoverInterior` (West low box: `0 < Re s < 1/2` and `|Im s| ≤ 1/2`).
   - Boca A (`|Re s - 1/2| < |Im s|` with `1/2 < |Im s|`).
2. The Diameter (`Re u = 0`, i.e., `|t| = |δ|`) inside the critical strip is
   absorbed by the critical line and `leftoverInterior`.
3. In the critical strip, `entireXi s = 0 ↔ riemannZeta s = 0`.
4. The functional equation gives `riemannZeta (1 - s) = 0 ↔ riemannZeta s = 0`.
5. Non-vanishing on `leftoverInterior` automatically rules out zeros on the West box.
6. **RH Reduction Theorem**: If `riemannZeta` does not vanish on `leftoverInterior`
   and does not vanish on Boca A, then every non-trivial zero of `riemannZeta`
   satisfies `Re s = 1/2`.
-/

open Complex Real Set Filter Topology Metric
open scoped NNReal

namespace RhG1Lean

/-! ### 1. Metric bounds and inclusion lemmas in the strip -/

/-- In the critical strip `0 < Re s < 1`, the transversal displacement satisfies
`|Re s - 1/2| < 1/2`. -/
theorem delta_lt_half_of_mem_strip {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    |s.re - 1 / 2| < 1 / 2 := by
  rw [abs_lt]
  constructor <;> linarith

/-- Low height on the East side falls in `leftoverRect`. -/
theorem mem_leftoverRect_of_half_le_and_height_le {s : ℂ}
    (h_half : 1 / 2 ≤ s.re) (h1 : s.re ≤ 1) (him : |s.im| ≤ 1 / 2) :
    s ∈ leftoverRect := by
  refine ⟨?_, h1, ?_⟩
  · have : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
    rw [this]
    exact h_half
  · have : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
    rw [this]
    exact him

/-- Low height strictly inside the East side falls in `leftoverInterior`. -/
theorem mem_leftoverInterior_of_half_le_and_height_le {s : ℂ}
    (h_half : 1 / 2 ≤ s.re) (h1 : s.re < 1) (him : |s.im| ≤ 1 / 2) :
    s ∈ leftoverInterior :=
  ⟨mem_leftoverRect_of_half_le_and_height_le h_half h1.le him, h1⟩

/-- Low height on the West side maps into `leftoverInterior` under reflection `s ↦ 1 - s`. -/
theorem mem_leftoverInterior_one_sub_of_re_lt_half {s : ℂ}
    (h0 : 0 < s.re) (h_half : s.re < 1 / 2) (him : |s.im| ≤ 1 / 2) :
    1 - s ∈ leftoverInterior := by
  have hre : 1 / 2 ≤ (1 - s).re := by
    have : (1 - s).re = 1 - s.re := by simp
    rw [this]; linarith
  have hre1 : (1 - s).re < 1 := by
    have : (1 - s).re = 1 - s.re := by simp
    rw [this]; linarith
  have him_sub : |(1 - s).im| ≤ 1 / 2 := by
    have : (1 - s).im = -s.im := by simp
    rw [this, abs_neg]
    exact him
  exact mem_leftoverInterior_of_half_le_and_height_le hre hre1 him_sub

/-- Points at height `|Im s| > 1/2` in the critical strip are automatically in Boca A
(`|δ| < |t|`). -/
theorem bocaA_of_high_height_in_strip {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (him : 1 / 2 < |s.im|) :
    |s.re - 1 / 2| < |s.im| :=
  lt_trans (delta_lt_half_of_mem_strip h0 h1) him

/-! ### 2. 4-Way Critical Strip Decomposition -/

/-- **Theorem 1 (Critical Strip Decomposition)**:
Every point in the critical strip `0 < Re s < 1` is either:
1. On the critical line `Re s = 1/2`.
2. In `leftoverInterior` (East low box).
3. Has `1 - s ∈ leftoverInterior` (West low box).
4. In Boca A at high height (`|Re s - 1/2| < |Im s|` and `1/2 < |Im s|`). -/
theorem critical_strip_decomposition {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    s.re = 1 / 2 ∨
    s ∈ leftoverInterior ∨
    1 - s ∈ leftoverInterior ∨
    (|s.re - 1 / 2| < |s.im| ∧ 1 / 2 < |s.im|) := by
  by_cases him : |s.im| ≤ 1 / 2
  · rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
    · right; right; left
      exact mem_leftoverInterior_one_sub_of_re_lt_half h0 hlt him
    · left
      exact heq
    · right; left
      exact mem_leftoverInterior_of_half_le_and_height_le hgt.le h1 him
  · have him_gt : 1 / 2 < |s.im| := not_le.mp him
    right; right; right
    exact ⟨bocaA_of_high_height_in_strip h0 h1 him_gt, him_gt⟩

/-! ### 3. Absorption of Habitación 2 (Diameter) -/

/-- Any point on the diameter `|t| = |δ|` inside the critical strip with `Re s > 1/2`
lies in `leftoverInterior`. -/
theorem diameter_in_strip_east_subset_leftoverInterior {s : ℂ}
    (h_half : 1 / 2 < s.re) (h1 : s.re < 1) (h_diag : |s.im| = |s.re - 1 / 2|) :
    s ∈ leftoverInterior := by
  have hδ : |s.re - 1 / 2| < 1 / 2 := by
    rw [abs_lt]
    constructor <;> linarith
  have him : |s.im| ≤ 1 / 2 := by
    rw [h_diag]
    exact hδ.le
  exact mem_leftoverInterior_of_half_le_and_height_le h_half.le h1 him

/-- Any point on the diameter `|t| = |δ|` inside the critical strip with `Re s < 1/2`
has `1 - s ∈ leftoverInterior`. -/
theorem diameter_in_strip_west_subset_leftoverInterior {s : ℂ}
    (h0 : 0 < s.re) (h_half : s.re < 1 / 2) (h_diag : |s.im| = |s.re - 1 / 2|) :
    1 - s ∈ leftoverInterior := by
  have hδ : |s.re - 1 / 2| < 1 / 2 := by
    rw [abs_lt]
    constructor <;> linarith
  have him : |s.im| ≤ 1 / 2 := by
    rw [h_diag]
    exact hδ.le
  exact mem_leftoverInterior_one_sub_of_re_lt_half h0 h_half him

/-! ### 4. Exact equivalence between entireXi and riemannZeta in the strip -/

/-- `Gammaℝ s ≠ 0` everywhere in the half-plane `Re s > 0`. -/
theorem Gammaℝ_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : Gammaℝ s ≠ 0 := by
  rw [Gammaℝ_def]
  have hπ : (π : ℂ) ^ (-s / 2) ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr pi_ne_zero))
  have hG : Complex.Gamma (s / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    rw [re_div_two]
    linarith
  exact mul_ne_zero hπ hG

/-- In the critical strip, `entireXi s = riemannXi s`. -/
theorem entireXi_eq_riemannXi_of_mem_strip {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    entireXi s = riemannXi s := by
  have hs0 : s ≠ 0 := by
    intro h
    have hre0 : s.re = 0 := by rw [h, zero_re]
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    have hre1 : s.re = 1 := by rw [h, one_re]
    linarith
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos h0
  exact entireXi_eq_riemannXi hs0 hs1 hG

/-- The prefactor `s * (s - 1) / 2` does not vanish in the critical strip. -/
theorem prefactor_ne_zero_of_mem_strip {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    s * (s - 1) / 2 ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro h
    have hre0 : s.re = 0 := by rw [h, zero_re]
    linarith
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have hre1 : s.re = 1 := by
      have hsub : (s - 1).re = 0 := by rw [h, zero_re]
      simp only [sub_re, one_re] at hsub
      linarith
    linarith
  have hprod : s * (s - 1) ≠ 0 := mul_ne_zero hs0 hs1
  exact div_ne_zero hprod (by norm_num)

/-- In the critical strip, `riemannXi s = 0 ↔ riemannZeta s = 0`. -/
theorem riemannXi_eq_zero_iff_zeta_of_mem_strip {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    riemannXi s = 0 ↔ riemannZeta s = 0 := by
  have hpref : s * (s - 1) / 2 ≠ 0 := prefactor_ne_zero_of_mem_strip h0 h1
  have hπ : (π : ℂ) ^ (-s / 2) ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr pi_ne_zero))
  have hG : Complex.Gamma (s / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    rw [re_div_two]
    linarith
  have hfact : s * (s - 1) / 2 * (π : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hpref hπ) hG
  unfold riemannXi
  constructor
  · intro h
    have hmul : s * (s - 1) / 2 * (π : ℂ) ^ (-s / 2) *
        Complex.Gamma (s / 2) * riemannZeta s = 0 := h
    cases mul_eq_zero.mp hmul with
    | inl hleft => exact (hfact hleft).elim
    | inr hright => exact hright
  · intro h
    rw [h, mul_zero]

/-- In the critical strip, `entireXi s = 0 ↔ riemannZeta s = 0`. -/
theorem entireXi_eq_zero_iff_zeta_of_mem_strip {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    entireXi s = 0 ↔ riemannZeta s = 0 := by
  rw [entireXi_eq_riemannXi_of_mem_strip h0 h1]
  exact riemannXi_eq_zero_iff_zeta_of_mem_strip h0 h1

/-- Functional equation symmetry for `riemannZeta` zeros in the critical strip:
`riemannZeta (1 - s) = 0 ↔ riemannZeta s = 0`. -/
theorem zeta_zero_one_sub_iff_of_mem_strip {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    riemannZeta (1 - s) = 0 ↔ riemannZeta s = 0 := by
  have h0_sub : 0 < (1 - s).re := by
    have : (1 - s).re = 1 - s.re := by simp
    rw [this]; linarith
  have h1_sub : (1 - s).re < 1 := by
    have : (1 - s).re = 1 - s.re := by simp
    rw [this]; linarith
  rw [← entireXi_eq_zero_iff_zeta_of_mem_strip h0_sub h1_sub,
      ← entireXi_eq_zero_iff_zeta_of_mem_strip h0 h1,
      entireXi_one_sub]

/-! ### 5. West box non-vanishing from leftoverInterior -/

/-- If `riemannZeta` does not vanish on `leftoverInterior`, then it does not vanish
on the reflected West box. -/
theorem zeta_ne_zero_of_one_sub_mem_leftoverInterior
    (h_east : ∀ z ∈ leftoverInterior, riemannZeta z ≠ 0)
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (h_sub : 1 - s ∈ leftoverInterior) :
    riemannZeta s ≠ 0 := by
  intro hz
  have hz_sub : riemannZeta (1 - s) = 0 := (zeta_zero_one_sub_iff_of_mem_strip h0 h1).mpr hz
  exact h_east (1 - s) h_sub hz_sub

/-! ### 6. Master Reduction Theorem -/

/-- Definition of Boca A in the critical strip. -/
def inBocaA (s : ℂ) : Prop :=
  |s.re - 1 / 2| < |s.im| ∧ 1 / 2 < |s.im|

/-- **Master Reduction Theorem for the Riemann Hypothesis (Off-Line Boca A Formulation)**:
If `riemannZeta` does not vanish on `leftoverInterior` (Habitación 1)
and does not vanish off the critical line in Boca A (Habitación 3), then every zero
of `riemannZeta` in the critical strip `0 < Re s < 1` lies strictly on the critical line `Re s = 1/2`. -/
theorem riemann_hypothesis_reduction_to_bocaA_off_line_and_leftover
    (h_leftover : ∀ z ∈ leftoverInterior, riemannZeta z ≠ 0)
    (h_bocaA_off : ∀ z : ℂ, 0 < z.re → z.re < 1 → inBocaA z → z.re ≠ 1 / 2 → riemannZeta z ≠ 0)
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hz : riemannZeta s = 0) :
    s.re = 1 / 2 := by
  rcases critical_strip_decomposition h0 h1 with heq | h_east | h_west | h_boca
  · exact heq
  · exact (h_leftover s h_east hz).elim
  · exact (zeta_ne_zero_of_one_sub_mem_leftoverInterior h_leftover h0 h1 h_west hz).elim
  · by_cases h_re : s.re = 1 / 2
    · exact h_re
    · exact (h_bocaA_off s h0 h1 h_boca h_re hz).elim

/-- **Master Reduction Theorem for the Riemann Hypothesis**:
If `riemannZeta` does not vanish on `leftoverInterior` (Habitación 1)
and does not vanish on Boca A (Habitación 3), then every zero of `riemannZeta`
in the critical strip `0 < Re s < 1` lies strictly on the critical line `Re s = 1/2`. -/
theorem riemann_hypothesis_reduction_to_bocaA_and_leftover
    (h_leftover : ∀ z ∈ leftoverInterior, riemannZeta z ≠ 0)
    (h_bocaA : ∀ z : ℂ, 0 < z.re → z.re < 1 → inBocaA z → riemannZeta z ≠ 0)
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hz : riemannZeta s = 0) :
    s.re = 1 / 2 :=
  riemann_hypothesis_reduction_to_bocaA_off_line_and_leftover h_leftover
    (fun z hz0 hz1 hzb _ => h_bocaA z hz0 hz1 hzb) h0 h1 hz

end RhG1Lean
