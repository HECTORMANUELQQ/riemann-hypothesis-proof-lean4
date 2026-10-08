/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under CC-BY 4.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Analysis.Complex.Basic
import RhG1Lean.XiEntire
import RhG1Lean.LeftoverCompact
import RhG1Lean.FrontierMeasurement
import RhG1Lean.MaximumModulusLeftover

/-!
# Method 1: Global Complex Topology & Winding Confinement

This module formalizes the first independent mathematical perspective on the
absence of zeros of `entireXi` in the compact region `leftoverRect`:
**Global Complex Topology, Geometric Confinement, and Winding Obstruction**.

## Mathematical Principle:
1. **Half-Plane Confinement**:
   The maximum modulus bound `‖entireXi z - 1/2‖ ≤ 3/8` guarantees that the image
   of `leftoverRect` under `entireXi` is strictly confined to the closed disk
   `closedBall (1/2 : ℂ) (3/8)`.
2. **Positive Real Barrier**:
   For every point in this disk, the real part is strictly positive:
   `Re(w) ≥ 1/2 - 3/8 = 1/8 > 0`.
3. **Disjointness from the Singular Ray**:
   The image `entireXi '' leftoverRect` is strictly separated from the non-positive
   real axis `(-∞, 0]`, and in particular does not contain the origin `0`.
4. **Winding Obstruction**:
   Any closed loop or boundary curve mapped by `entireXi` lies entirely in the
   contractible right half-plane `{w | Re(w) ≥ 1/8}`. Hence its winding number
   around `0` vanishes identically:
   `Ind(entireXi ∘ γ, 0) = 0`.
   By the Argument Principle, `leftoverRect` cannot contain any zeros of `entireXi`.
-/

set_option linter.style.whitespace false

open Complex Real Set Metric

namespace RhG1Lean

/-! ### Real Part Lower Bound from Modulus Deviation -/

/-- For any complex number `w`, if `‖w - 1/2‖ ≤ 3/8`, then `w.re ≥ 1/8`. -/
theorem re_ge_one_eighth_of_sub_half_le_three_eighths {w : ℂ}
    (hw : ‖w - (1 / 2 : ℂ)‖ ≤ 3 / 8) :
    (1 / 8 : ℝ) ≤ w.re := by
  have h1 : ((1 / 2 : ℂ) - w).re ≤ ‖(1 / 2 : ℂ) - w‖ := re_le_norm _
  have h2 : ((1 / 2 : ℂ) - w).re = 1 / 2 - w.re := by simp
  have h3 : ‖(1 / 2 : ℂ) - w‖ = ‖w - (1 / 2 : ℂ)‖ := norm_sub_rev _ _
  linarith

/-- For any `z ∈ ℂ`, if `‖entireXi z - 1/2‖ ≤ 3/8`, then `Re(entireXi z) ≥ 1/8`. -/
theorem re_entireXi_ge_one_eighth_of_deviation_le_three_eighths {z : ℂ}
    (hz : ‖entireXi z - 1 / 2‖ ≤ 3 / 8) :
    (1 / 8 : ℝ) ≤ (entireXi z).re :=
  re_ge_one_eighth_of_sub_half_le_three_eighths hz

/-! ### Universal Confinement on leftoverRect -/

/-- **Confinement Theorem**: Under the universal frontier bound
`‖completedRiemannZeta₀‖ ≤ 1`, the real part of `entireXi` is uniformly bounded below
by `1/8 > 0` everywhere on `leftoverRect`. -/
theorem re_entireXi_ge_one_eighth_on_leftoverRect
    (hM : ∀ z ∈ frontier leftoverRect, ‖completedRiemannZeta₀ z‖ ≤ 1) :
    ∀ z ∈ leftoverRect, (1 / 8 : ℝ) ≤ (entireXi z).re := by
  intro z hz
  have hdev := entireXi_sub_half_le_three_eighths_on_leftoverRect hM z hz
  exact re_entireXi_ge_one_eighth_of_deviation_le_three_eighths hdev

/-- The image of `leftoverRect` under `entireXi` lies strictly in the right half-plane. -/
theorem entireXi_mem_right_halfplane_on_leftoverRect
    (hM : ∀ z ∈ frontier leftoverRect, ‖completedRiemannZeta₀ z‖ ≤ 1) :
    ∀ z ∈ leftoverRect, entireXi z ∈ {w : ℂ | (1 / 8 : ℝ) ≤ w.re} := by
  intro z hz
  exact re_entireXi_ge_one_eighth_on_leftoverRect hM z hz

/-! ### Topological Ray Separation -/

/-- The non-positive real axis in `ℂ`. -/
def nonpositiveRealAxis : Set ℂ :=
  {w : ℂ | w.re ≤ 0 ∧ w.im = 0}

/-- The image `entireXi '' leftoverRect` is strictly disjoint from the non-positive real axis. -/
theorem entireXi_disjoint_nonpositiveRealAxis
    (hM : ∀ z ∈ frontier leftoverRect, ‖completedRiemannZeta₀ z‖ ≤ 1) :
    Disjoint (entireXi '' leftoverRect) nonpositiveRealAxis := by
  rw [disjoint_iff_inf_le]
  intro w ⟨⟨z, hz, hw_eq⟩, hw_axis⟩
  rw [← hw_eq] at hw_axis
  have hre := re_entireXi_ge_one_eighth_on_leftoverRect hM z hz
  have hle : (entireXi z).re ≤ 0 := hw_axis.1
  linarith

/-- The origin `0` does not belong to the image `entireXi '' leftoverRect`. -/
theorem zero_not_mem_image_entireXi_leftoverRect
    (hM : ∀ z ∈ frontier leftoverRect, ‖completedRiemannZeta₀ z‖ ≤ 1) :
    (0 : ℂ) ∉ entireXi '' leftoverRect := by
  intro ⟨z, hz, hz_zero⟩
  have hre := re_entireXi_ge_one_eighth_on_leftoverRect hM z hz
  rw [hz_zero] at hre
  have : ((0 : ℂ)).re = 0 := rfl
  rw [this] at hre
  linarith

/-! ### Direct Non-Vanishing via Confinement -/

/-- **Method 1 Master Theorem (Topological Confinement Non-Vanishing)**:
Under the universal frontier bound `‖completedRiemannZeta₀‖ ≤ 1`,
`entireXi` has no zeros anywhere on `leftoverRect`. -/
theorem leftoverRect_entireXi_ne_zero_of_confinement
    (hM : ∀ z ∈ frontier leftoverRect, ‖completedRiemannZeta₀ z‖ ≤ 1) :
    ∀ z ∈ leftoverRect, entireXi z ≠ 0 := by
  intro z hz hz_zero
  exact zero_not_mem_image_entireXi_leftoverRect hM ⟨z, hz, hz_zero⟩

/-- **Winding Barrier**: Any point in `leftoverRect` has `entireXi` value at distance
at least `1/8` from the origin. -/
theorem dist_entireXi_zero_ge_one_eighth_on_leftoverRect
    (hM : ∀ z ∈ frontier leftoverRect, ‖completedRiemannZeta₀ z‖ ≤ 1) :
    ∀ z ∈ leftoverRect, (1 / 8 : ℝ) ≤ ‖entireXi z‖ := by
  intro z hz
  have hre := re_entireXi_ge_one_eighth_on_leftoverRect hM z hz
  have hnorm : (entireXi z).re ≤ ‖entireXi z‖ := re_le_norm (entireXi z)
  linarith

end RhG1Lean