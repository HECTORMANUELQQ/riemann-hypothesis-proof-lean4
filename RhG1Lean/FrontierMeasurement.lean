/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.AbsMax
import RhG1Lean.XiEntire
import RhG1Lean.LeftoverCompact
import RhG1Lean.DualCancellation

/-!
# Exact Frontier Measurement on leftoverRect

This module develops the exact decomposition and geometric bounds for `entireXi`
on the 1D boundary (frontier) of `leftoverRect`.

## Key Structural Results:
1. `entireXi_sub_half`: Exact representation `entireXi s - 1/2 = (s*(s-1)/2) * completedRiemannZeta₀ s`.
2. `norm_entireXi_sub_half`: Norm factorization into the quadratic geometric prefactor
   `‖s * (s - 1) / 2‖` and the completed zeta factor `‖completedRiemannZeta₀ s‖`.
3. The 4 boundary edges of `leftoverRect`:
   - `edgeWest`: Re s = 1/2, |Im s| ≤ 1/2 (Critical line segment)
   - `edgeEast`: Re s = 1, |Im s| ≤ 1/2 (Right face)
   - `edgeNorth`: Im s = 1/2, 1/2 ≤ Re s ≤ 1 (Top edge)
   - `edgeSouth`: Im s = -1/2, 1/2 ≤ Re s ≤ 1 (Bottom edge)
4. Exact prefactor bounds on the edges:
   - On `edgeWest`: `‖s * (s - 1) / 2‖ ≤ 1 / 4` (purely real quadratic).
   - On `edgeEast`: `‖s * (s - 1) / 2‖ ≤ 3 / 8`.
   - On `edgeNorth` / `edgeSouth`: `‖s * (s - 1) / 2‖ ≤ 3 / 8`.
   - On all 4 edges: `‖s * (s - 1) / 2‖ ≤ 3 / 8 < 1 / 2`.
5. Master edge reduction theorem.
-/

open Complex Real Set Filter Topology Metric
open scoped NNReal ComplexConjugate

namespace RhG1Lean

/-! ### Exact Representation of entireXi - 1/2 -/

/-- Exact algebraic identity: `entireXi s - 1/2 = (s * (s - 1) / 2) * completedRiemannZeta₀ s`. -/
theorem entireXi_sub_half (s : ℂ) :
    entireXi s - 1 / 2 = (s * (s - 1) / 2) * completedRiemannZeta₀ s := by
  unfold entireXi
  ring

/-- Exact norm factorization: `‖entireXi s - 1/2‖ = ‖s * (s - 1) / 2‖ * ‖completedRiemannZeta₀ s‖`. -/
theorem norm_entireXi_sub_half (s : ℂ) :
    ‖entireXi s - 1 / 2‖ = ‖s * (s - 1) / 2‖ * ‖completedRiemannZeta₀ s‖ := by
  rw [entireXi_sub_half, norm_mul]

/-- Symmetry of the deviation `‖entireXi - 1/2‖` across the critical line $\delta = 0$. -/
theorem norm_entireXi_sub_half_symm_delta {δ t : ℝ} (hδ : |δ| < 1 / 2) :
    ‖entireXi (((1 / 2 - δ : ℝ) : ℂ) + I * t) - 1 / 2‖ =
      ‖entireXi (((1 / 2 + δ : ℝ) : ℂ) + I * t) - 1 / 2‖ := by
  have hsymm := entireXi_reflection_symm hδ (t := t)
  have hconj : entireXi (((1 / 2 - δ : ℝ) : ℂ) + I * t) - 1 / 2 =
      conj (entireXi (((1 / 2 + δ : ℝ) : ℂ) + I * t) - 1 / 2) := by
    rw [map_sub, hsymm]
    have : conj (1 / 2 : ℂ) = 1 / 2 := by
      simp [map_ofNat]
    rw [this]
  rw [hconj, Complex.norm_conj]

/-! ### The 4 Boundary Edges of leftoverRect -/

/-- West edge of leftoverRect: on the critical line Re s = 1/2. -/
def edgeWest : Set ℂ :=
  {s ∈ leftoverRect | s.re = (2 : ℝ)⁻¹}

/-- East edge of leftoverRect: on the right boundary Re s = 1. -/
def edgeEast : Set ℂ :=
  {s ∈ leftoverRect | s.re = 1}

/-- North edge of leftoverRect: on the top boundary Im s = 1/2. -/
def edgeNorth : Set ℂ :=
  {s ∈ leftoverRect | s.im = (2 : ℝ)⁻¹}

/-- South edge of leftoverRect: on the bottom boundary Im s = -1/2. -/
def edgeSouth : Set ℂ :=
  {s ∈ leftoverRect | s.im = - (2 : ℝ)⁻¹}

/-- The union of the 4 boundary edges. -/
def boundaryEdges : Set ℂ :=
  edgeWest ∪ edgeEast ∪ edgeNorth ∪ edgeSouth

lemma mem_edgeWest {s : ℂ} : s ∈ edgeWest ↔ s ∈ leftoverRect ∧ s.re = (2 : ℝ)⁻¹ := Iff.rfl
lemma mem_edgeEast {s : ℂ} : s ∈ edgeEast ↔ s ∈ leftoverRect ∧ s.re = 1 := Iff.rfl
lemma mem_edgeNorth {s : ℂ} : s ∈ edgeNorth ↔ s ∈ leftoverRect ∧ s.im = (2 : ℝ)⁻¹ := Iff.rfl
lemma mem_edgeSouth {s : ℂ} : s ∈ edgeSouth ↔ s ∈ leftoverRect ∧ s.im = - (2 : ℝ)⁻¹ := Iff.rfl

lemma edgeWest_subset_leftoverRect : edgeWest ⊆ leftoverRect := fun _ hs => hs.1
lemma edgeEast_subset_leftoverRect : edgeEast ⊆ leftoverRect := fun _ hs => hs.1
lemma edgeNorth_subset_leftoverRect : edgeNorth ⊆ leftoverRect := fun _ hs => hs.1
lemma edgeSouth_subset_leftoverRect : edgeSouth ⊆ leftoverRect := fun _ hs => hs.1
lemma boundaryEdges_subset_leftoverRect : boundaryEdges ⊆ leftoverRect := by
  intro s hs
  rcases hs with ((hW | hE) | hN) | hS
  · exact hW.1
  · exact hE.1
  · exact hN.1
  · exact hS.1

/-! ### Norm Bounds for s on leftoverRect -/

/-- On `leftoverRect`, `‖s‖ ≤ 3 / 2`. -/
theorem norm_le_three_halves_of_mem_leftoverRect {s : ℂ} (hs : s ∈ leftoverRect) :
    ‖s‖ ≤ 3 / 2 := by
  have hdec : s = ((s.re : ℝ) : ℂ) + ((s.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  have htri : ‖s‖ ≤ ‖((s.re : ℝ) : ℂ)‖ + ‖((s.im : ℝ) : ℂ) * I‖ := by
    conv_lhs => rw [hdec]
    exact norm_add_le (((s.re : ℝ) : ℂ)) (((s.im : ℝ) : ℂ) * I)
  have hnorm_re : ‖((s.re : ℝ) : ℂ)‖ = |s.re| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hnorm_im : ‖((s.im : ℝ) : ℂ) * I‖ = |s.im| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm_re, hnorm_im] at htri
  have hre : |s.re| ≤ 1 := by
    rw [abs_le]
    have : (2 : ℝ)⁻¹ ≤ s.re := hs.1
    have : s.re ≤ 1 := hs.2.1
    constructor <;> linarith
  have him : |s.im| ≤ (1 : ℝ) / 2 := by
    have : |s.im| ≤ (2 : ℝ)⁻¹ := hs.2.2
    linarith
  linarith

/-! ### Exact Analysis of edgeWest (Critical Line Segment) -/

/-- On `edgeWest`, `entireXi` is purely real. -/
theorem im_entireXi_eq_zero_of_mem_edgeWest {s : ℂ} (hs : s ∈ edgeWest) :
    (entireXi s).im = 0 := by
  have hdec : s = ((1 / 2 : ℝ) : ℂ) + I * s.im := by
    apply Complex.ext
    · simp only [re_ofReal_add_I_mul]
      have hre := hs.2
      have : (2 : ℝ)⁻¹ = (1 : ℝ) / 2 := by norm_num
      rw [← this, hre]
    · simp only [im_ofReal_add_I_mul]
  rw [hdec]
  exact entireXi_critical_line_im_eq_zero s.im

/-- On `edgeWest`, `‖entireXi s - 1/2‖ = |(entireXi s).re - 1/2|`. -/
theorem norm_entireXi_sub_half_edgeWest {s : ℂ} (hs : s ∈ edgeWest) :
    ‖entireXi s - 1 / 2‖ = |(entireXi s).re - 1 / 2| := by
  have him : (entireXi s - 1 / 2).im = 0 := by
    simp [im_entireXi_eq_zero_of_mem_edgeWest hs]
  have hreal : entireXi s - 1 / 2 = (((entireXi s - 1 / 2).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using him
  rw [hreal, Complex.norm_real, Real.norm_eq_abs]
  simp

/-- On the critical line, `s * (s - 1) = - (s.im^2 + 1/4)`. -/
theorem critical_line_mul_sub_one (t : ℝ) :
    (((1 / 2 : ℝ) : ℂ) + I * t) * ((((1 / 2 : ℝ) : ℂ) + I * t) - 1) =
      - (((t ^ 2 + 1 / 4 : ℝ) : ℂ)) := by
  have hhalf : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by push_cast; rfl
  have hcast : (((t ^ 2 + 1 / 4 : ℝ) : ℂ)) = (t : ℂ) ^ 2 + 1 / 4 := by push_cast; rfl
  rw [hhalf, hcast]
  calc
    (1 / 2 + I * (t : ℂ)) * (1 / 2 + I * (t : ℂ) - 1)
      = (I * (t : ℂ) + 1 / 2) * (I * (t : ℂ) - 1 / 2) := by ring
    _ = (I * (t : ℂ)) ^ 2 - (1 / 2 : ℂ) ^ 2 := by ring
    _ = I ^ 2 * (t : ℂ) ^ 2 - 1 / 4 := by ring
    _ = -1 * (t : ℂ) ^ 2 - 1 / 4 := by rw [I_sq]
    _ = - ((t : ℂ) ^ 2 + 1 / 4) := by ring

/-- On the critical line, `completedRiemannZeta₀` is strictly real. -/
theorem im_completedRiemannZeta₀_critical_line_eq_zero (t : ℝ) :
    (completedRiemannZeta₀ (((1 / 2 : ℝ) : ℂ) + I * t)).im = 0 := by
  let s : ℂ := ((1 / 2 : ℝ) : ℂ) + I * t
  have hid := entireXi_sub_half s
  have hxi_im := entireXi_critical_line_im_eq_zero t
  have hsub_im : (entireXi s - 1 / 2).im = 0 := by
    have hhalf_im : ((1 : ℂ) / 2).im = 0 := by simp
    rw [sub_im, hhalf_im, sub_zero]
    exact hxi_im
  have hprod : (s * (s - 1) / 2) = - ((((t ^ 2 + 1 / 4) / 2 : ℝ) : ℂ)) := by
    have h1 := critical_line_mul_sub_one t
    change (((1 / 2 : ℝ) : ℂ) + I * t) * ((((1 / 2 : ℝ) : ℂ) + I * t) - 1) / 2 = - ((((t ^ 2 + 1 / 4) / 2 : ℝ) : ℂ))
    rw [h1]
    push_cast
    ring
  have h_im_eq : (entireXi s - 1 / 2).im = (- ((t ^ 2 + 1 / 4) / 2)) * (completedRiemannZeta₀ s).im := by
    rw [hid, hprod]
    have : - ((((t ^ 2 + 1 / 4) / 2 : ℝ) : ℂ)) = (((- ((t ^ 2 + 1 / 4) / 2) : ℝ) : ℂ)) := by
      push_cast; rfl
    rw [this]
    simp only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
  have h_scalar_ne : (- ((t ^ 2 + 1 / 4) / 2)) ≠ 0 := by
    have : 0 < t ^ 2 + 1 / 4 := by positivity
    linarith
  rw [hsub_im] at h_im_eq
  have h_symm : (- ((t ^ 2 + 1 / 4) / 2)) * (completedRiemannZeta₀ s).im = 0 := h_im_eq.symm
  cases mul_eq_zero.mp h_symm with
  | inl h_sc => exact (h_scalar_ne h_sc).elim
  | inr h_im => exact h_im

/-- On `edgeWest`, `completedRiemannZeta₀` is strictly real. -/
theorem im_completedRiemannZeta₀_eq_zero_of_mem_edgeWest {s : ℂ} (hs : s ∈ edgeWest) :
    (completedRiemannZeta₀ s).im = 0 := by
  have hdec : s = ((1 / 2 : ℝ) : ℂ) + I * s.im := by
    apply Complex.ext
    · simp only [re_ofReal_add_I_mul]
      have hre := hs.2
      have : (2 : ℝ)⁻¹ = (1 : ℝ) / 2 := by norm_num
      rw [← this, hre]
    · simp only [im_ofReal_add_I_mul]
  rw [hdec]
  exact im_completedRiemannZeta₀_critical_line_eq_zero s.im

/-- On `edgeWest`, the norm of `completedRiemannZeta₀` equals the absolute value of its real part. -/
theorem norm_completedRiemannZeta₀_edgeWest {s : ℂ} (hs : s ∈ edgeWest) :
    ‖completedRiemannZeta₀ s‖ = |(completedRiemannZeta₀ s).re| := by
  have him : (completedRiemannZeta₀ s).im = 0 :=
    im_completedRiemannZeta₀_eq_zero_of_mem_edgeWest hs
  have hreal : completedRiemannZeta₀ s = (((completedRiemannZeta₀ s).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using him
  rw [hreal, Complex.norm_real, Real.norm_eq_abs, ofReal_re]




/-- On `edgeWest`, the quadratic prefactor `‖s * (s - 1) / 2‖ ≤ 1 / 4`. -/
theorem norm_prefactor_le_quarter_of_mem_edgeWest {s : ℂ} (hs : s ∈ edgeWest) :
    ‖s * (s - 1) / 2‖ ≤ 1 / 4 := by
  have hdec : s = ((1 / 2 : ℝ) : ℂ) + I * s.im := by
    apply Complex.ext
    · simp only [re_ofReal_add_I_mul]
      have hre := hs.2
      have : (2 : ℝ)⁻¹ = (1 : ℝ) / 2 := by norm_num
      rw [← this, hre]
    · simp only [im_ofReal_add_I_mul]
  rw [hdec]
  have hid := critical_line_mul_sub_one s.im
  have hdiv : (((1 / 2 : ℝ) : ℂ) + I * s.im) * ((((1 / 2 : ℝ) : ℂ) + I * s.im) - 1) / 2 =
      - ((((s.im ^ 2 + 1 / 4) / 2 : ℝ) : ℂ)) := by
    rw [hid]
    push_cast
    ring
  rw [hdiv, norm_neg, Complex.norm_real, Real.norm_eq_abs]
  have him_le : |s.im| ≤ (2 : ℝ)⁻¹ := hs.1.2.2
  have him_split : - (1 / 2 : ℝ) ≤ s.im ∧ s.im ≤ 1 / 2 := by
    have : (2 : ℝ)⁻¹ = (1 / 2 : ℝ) := by norm_num
    rw [this] at him_le
    exact abs_le.mp him_le
  have him2_le : s.im ^ 2 ≤ 1 / 4 := by
    nlinarith [him_split.1, him_split.2]
  have hpos : 0 ≤ (s.im ^ 2 + 1 / 4) / 2 := by positivity
  rw [abs_of_nonneg hpos]
  linarith

/-! ### Exact Analysis of edgeEast (Re s = 1 Face) -/

/-- On `edgeEast`, `‖s - 1‖ = |s.im| ≤ 1 / 2`. -/
theorem norm_sub_one_le_half_of_mem_edgeEast {s : ℂ} (hs : s ∈ edgeEast) :
    ‖s - 1‖ ≤ 1 / 2 := by
  have hre : s.re = 1 := hs.2
  have hdec : s - 1 = ((s.im : ℝ) : ℂ) * I := by
    apply Complex.ext
    · simp [hre]
    · simp
  rw [hdec, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have : |s.im| ≤ (2 : ℝ)⁻¹ := hs.1.2.2
  linarith

/-- On `edgeEast`, the quadratic prefactor `‖s * (s - 1) / 2‖ ≤ 3 / 8`. -/
theorem norm_prefactor_le_three_eighths_of_mem_edgeEast {s : ℂ} (hs : s ∈ edgeEast) :
    ‖s * (s - 1) / 2‖ ≤ 3 / 8 := by
  have hns : ‖s‖ ≤ 3 / 2 := norm_le_three_halves_of_mem_leftoverRect hs.1
  have hns1 : ‖s - 1‖ ≤ 1 / 2 := norm_sub_one_le_half_of_mem_edgeEast hs
  have hmul : ‖s * (s - 1)‖ ≤ 3 / 2 * (1 / 2) := by
    rw [norm_mul]
    exact mul_le_mul hns hns1 (norm_nonneg _) (by norm_num)
  have hdiv : ‖s * (s - 1) / 2‖ = ‖s * (s - 1)‖ / 2 := by
    simp only [norm_div, Complex.norm_ofNat]
  rw [hdiv]
  linarith

/-! ### Exact Analysis of edgeNorth (Im s = 1/2 Face) -/

/-- Product identity on the horizontal line Im s = 1/2. -/
theorem north_mul_sub_one (x : ℝ) :
    (((x : ℂ) + I * (1 / 2 : ℝ)) * (((x : ℂ) + I * (1 / 2 : ℝ)) - 1)) =
      (((x ^ 2 - x - 1 / 4 : ℝ) : ℂ) + I * (((x - 1 / 2 : ℝ) : ℂ))) := by
  have hhalf : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by push_cast; rfl
  calc
    (((x : ℂ) + I * (1 / 2 : ℝ)) * (((x : ℂ) + I * (1 / 2 : ℝ)) - 1))
      = ((x : ℂ) + I * (1 / 2 : ℂ)) * ((x : ℂ) + I * (1 / 2 : ℂ) - 1) := by rw [hhalf]
    _ = (x : ℂ) ^ 2 - (x : ℂ) + I ^ 2 * (1 / 4 : ℂ) + I * ((x : ℂ) - 1 / 2) := by ring
    _ = (x : ℂ) ^ 2 - (x : ℂ) + (-1) * (1 / 4 : ℂ) + I * ((x : ℂ) - 1 / 2) := by rw [I_sq]
    _ = ((x : ℂ) ^ 2 - (x : ℂ) - 1 / 4) + I * ((x : ℂ) - 1 / 2) := by ring
    _ = (((x ^ 2 - x - 1 / 4 : ℝ) : ℂ) + I * (((x - 1 / 2 : ℝ) : ℂ))) := by push_cast; rfl

/-- On `edgeNorth`, the quadratic prefactor `‖s * (s - 1) / 2‖ ≤ 3 / 8`. -/
theorem norm_prefactor_le_three_eighths_of_mem_edgeNorth {s : ℂ} (hs : s ∈ edgeNorth) :
    ‖s * (s - 1) / 2‖ ≤ 3 / 8 := by
  have him : s.im = 1 / 2 := by
    have := hs.2
    have hinv : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
    rw [← hinv, this]
  have hdec : s = ((s.re : ℝ) : ℂ) + I * (1 / 2 : ℝ) := by
    apply Complex.ext
    · simp only [re_ofReal_add_I_mul]
    · simp only [im_ofReal_add_I_mul, him]
  have hid := north_mul_sub_one s.re
  have hprod : s * (s - 1) = (((s.re ^ 2 - s.re - 1 / 4 : ℝ) : ℂ) + I * (((s.re - 1 / 2 : ℝ) : ℂ))) := by
    conv_lhs => rw [hdec]
    exact hid
  have htri : ‖s * (s - 1)‖ ≤ ‖((s.re ^ 2 - s.re - 1 / 4 : ℝ) : ℂ)‖ + ‖I * (((s.re - 1 / 2 : ℝ) : ℂ))‖ := by
    conv_lhs => rw [hprod]
    exact norm_add_le (((s.re ^ 2 - s.re - 1 / 4 : ℝ) : ℂ)) (I * (((s.re - 1 / 2 : ℝ) : ℂ)))
  have hnorm_re : ‖((s.re ^ 2 - s.re - 1 / 4 : ℝ) : ℂ)‖ = |s.re ^ 2 - s.re - 1 / 4| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hnorm_im : ‖I * (((s.re - 1 / 2 : ℝ) : ℂ))‖ = |s.re - 1 / 2| := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm_re, hnorm_im] at htri
  have hre1 : (2 : ℝ)⁻¹ ≤ s.re := hs.1.1
  have hre2 : s.re ≤ 1 := hs.1.2.1
  have hre1' : 1 / 2 ≤ s.re := by
    have : (2 : ℝ)⁻¹ = (1 / 2 : ℝ) := by norm_num
    linarith
  have h_re_nonneg : 0 ≤ s.re - 1 / 2 := by linarith
  have habs_im : |s.re - 1 / 2| = s.re - 1 / 2 := abs_of_nonneg h_re_nonneg
  have hpoly_neg : s.re ^ 2 - s.re - 1 / 4 ≤ 0 := by nlinarith [hre1', hre2]
  have habs_re : |s.re ^ 2 - s.re - 1 / 4| = - (s.re ^ 2 - s.re - 1 / 4) := abs_of_nonpos hpoly_neg
  have hsq : 0 ≤ (s.re - 1) ^ 2 := sq_nonneg (s.re - 1)
  have htri_le : |s.re ^ 2 - s.re - 1 / 4| + |s.re - 1 / 2| ≤ 3 / 4 := by
    rw [habs_re, habs_im]
    nlinarith [hsq]
  have hdiv : ‖s * (s - 1) / 2‖ = ‖s * (s - 1)‖ / 2 := by
    simp only [norm_div, Complex.norm_ofNat]
  rw [hdiv]
  linarith

/-- On `edgeNorth`, the quadratic prefactor `‖s * (s - 1) / 2‖ ≤ 1 / 2`. -/
theorem norm_prefactor_le_half_of_mem_edgeNorth {s : ℂ} (hs : s ∈ edgeNorth) :
    ‖s * (s - 1) / 2‖ ≤ 1 / 2 := by
  have := norm_prefactor_le_three_eighths_of_mem_edgeNorth hs
  linarith

/-! ### Exact Analysis of edgeSouth (Im s = -1/2 Face) -/

/-- Product identity on the horizontal line Im s = -1/2. -/
theorem south_mul_sub_one (x : ℝ) :
    (((x : ℂ) - I * (1 / 2 : ℝ)) * (((x : ℂ) - I * (1 / 2 : ℝ)) - 1)) =
      (((x ^ 2 - x - 1 / 4 : ℝ) : ℂ) - I * (((x - 1 / 2 : ℝ) : ℂ))) := by
  have hhalf : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by push_cast; rfl
  calc
    (((x : ℂ) - I * (1 / 2 : ℝ)) * (((x : ℂ) - I * (1 / 2 : ℝ)) - 1))
      = ((x : ℂ) - I * (1 / 2 : ℂ)) * ((x : ℂ) - I * (1 / 2 : ℂ) - 1) := by rw [hhalf]
    _ = (x : ℂ) ^ 2 - (x : ℂ) + I ^ 2 * (1 / 4 : ℂ) - I * ((x : ℂ) - 1 / 2) := by ring
    _ = (x : ℂ) ^ 2 - (x : ℂ) + (-1) * (1 / 4 : ℂ) - I * ((x : ℂ) - 1 / 2) := by rw [I_sq]
    _ = ((x : ℂ) ^ 2 - (x : ℂ) - 1 / 4) - I * ((x : ℂ) - 1 / 2) := by ring
    _ = (((x ^ 2 - x - 1 / 4 : ℝ) : ℂ) - I * (((x - 1 / 2 : ℝ) : ℂ))) := by push_cast; rfl

/-- On `edgeSouth`, the quadratic prefactor `‖s * (s - 1) / 2‖ ≤ 3 / 8`. -/
theorem norm_prefactor_le_three_eighths_of_mem_edgeSouth {s : ℂ} (hs : s ∈ edgeSouth) :
    ‖s * (s - 1) / 2‖ ≤ 3 / 8 := by
  have him : s.im = - (1 / 2) := by
    have := hs.2
    have hinv : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
    rw [← hinv, this]
  have hdec : s = ((s.re : ℝ) : ℂ) - I * (1 / 2 : ℝ) := by
    have h1 : s = ((s.re : ℝ) : ℂ) + ((s.im : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp
    have h2 : ((s.re : ℝ) : ℂ) + ((- (1 / 2 : ℝ) : ℝ) : ℂ) * I = ((s.re : ℝ) : ℂ) - I * (1 / 2 : ℝ) := by
      push_cast
      ring
    calc s = ((s.re : ℝ) : ℂ) + ((s.im : ℝ) : ℂ) * I := h1
      _ = ((s.re : ℝ) : ℂ) + ((- (1 / 2 : ℝ) : ℝ) : ℂ) * I := by rw [him]
      _ = ((s.re : ℝ) : ℂ) - I * (1 / 2 : ℝ) := h2
  have hid := south_mul_sub_one s.re
  have hprod : s * (s - 1) = (((s.re ^ 2 - s.re - 1 / 4 : ℝ) : ℂ) - I * (((s.re - 1 / 2 : ℝ) : ℂ))) := by
    conv_lhs => rw [hdec]
    exact hid
  have htri : ‖s * (s - 1)‖ ≤ ‖((s.re ^ 2 - s.re - 1 / 4 : ℝ) : ℂ)‖ + ‖- (I * (((s.re - 1 / 2 : ℝ) : ℂ)))‖ := by
    have hsub : (((s.re ^ 2 - s.re - 1 / 4 : ℝ) : ℂ) - I * (((s.re - 1 / 2 : ℝ) : ℂ))) =
        ((s.re ^ 2 - s.re - 1 / 4 : ℝ) : ℂ) + (- (I * (((s.re - 1 / 2 : ℝ) : ℂ)))) := by ring
    conv_lhs => rw [hprod, hsub]
    exact norm_add_le (((s.re ^ 2 - s.re - 1 / 4 : ℝ) : ℂ)) (- (I * (((s.re - 1 / 2 : ℝ) : ℂ))))
  rw [norm_neg] at htri
  have hnorm_re : ‖((s.re ^ 2 - s.re - 1 / 4 : ℝ) : ℂ)‖ = |s.re ^ 2 - s.re - 1 / 4| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hnorm_im : ‖I * (((s.re - 1 / 2 : ℝ) : ℂ))‖ = |s.re - 1 / 2| := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm_re, hnorm_im] at htri
  have hre1 : (2 : ℝ)⁻¹ ≤ s.re := hs.1.1
  have hre2 : s.re ≤ 1 := hs.1.2.1
  have hre1' : 1 / 2 ≤ s.re := by
    have : (2 : ℝ)⁻¹ = (1 / 2 : ℝ) := by norm_num
    linarith
  have h_re_nonneg : 0 ≤ s.re - 1 / 2 := by linarith
  have habs_im : |s.re - 1 / 2| = s.re - 1 / 2 := abs_of_nonneg h_re_nonneg
  have hpoly_neg : s.re ^ 2 - s.re - 1 / 4 ≤ 0 := by nlinarith [hre1', hre2]
  have habs_re : |s.re ^ 2 - s.re - 1 / 4| = - (s.re ^ 2 - s.re - 1 / 4) := abs_of_nonpos hpoly_neg
  have hsq : 0 ≤ (s.re - 1) ^ 2 := sq_nonneg (s.re - 1)
  have htri_le : |s.re ^ 2 - s.re - 1 / 4| + |s.re - 1 / 2| ≤ 3 / 4 := by
    rw [habs_re, habs_im]
    nlinarith [hsq]
  have hdiv : ‖s * (s - 1) / 2‖ = ‖s * (s - 1)‖ / 2 := by
    simp only [norm_div, Complex.norm_ofNat]
  rw [hdiv]
  linarith

/-- On `edgeSouth`, the quadratic prefactor `‖s * (s - 1) / 2‖ ≤ 1 / 2`. -/
theorem norm_prefactor_le_half_of_mem_edgeSouth {s : ℂ} (hs : s ∈ edgeSouth) :
    ‖s * (s - 1) / 2‖ ≤ 1 / 2 := by
  have := norm_prefactor_le_three_eighths_of_mem_edgeSouth hs
  linarith

/-! ### Master Prefactor Bound on All 4 Edges -/

/-- On `edgeWest`, `‖s * (s - 1) / 2‖ ≤ 3 / 8`. -/
theorem norm_prefactor_le_three_eighths_of_mem_edgeWest {s : ℂ} (hs : s ∈ edgeWest) :
    ‖s * (s - 1) / 2‖ ≤ 3 / 8 := by
  have h14 := norm_prefactor_le_quarter_of_mem_edgeWest hs
  linarith

/-- On `edgeWest`, `‖s * (s - 1) / 2‖ ≤ 1 / 2`. -/
theorem norm_prefactor_le_half_of_mem_edgeWest {s : ℂ} (hs : s ∈ edgeWest) :
    ‖s * (s - 1) / 2‖ ≤ 1 / 2 := by
  have h14 := norm_prefactor_le_quarter_of_mem_edgeWest hs
  linarith

/-- On `edgeEast`, `‖s * (s - 1) / 2‖ ≤ 1 / 2`. -/
theorem norm_prefactor_le_half_of_mem_edgeEast {s : ℂ} (hs : s ∈ edgeEast) :
    ‖s * (s - 1) / 2‖ ≤ 1 / 2 := by
  have h38 := norm_prefactor_le_three_eighths_of_mem_edgeEast hs
  linarith

/-- **Universal Boundary Prefactor Bound (Sharpened to 3/8)**: On all 4 boundary edges of `leftoverRect`,
`‖s * (s - 1) / 2‖ ≤ 3 / 8`. -/
theorem norm_prefactor_le_three_eighths_of_mem_boundaryEdges {s : ℂ} (hs : s ∈ boundaryEdges) :
    ‖s * (s - 1) / 2‖ ≤ 3 / 8 := by
  rcases hs with ((hW | hE) | hN) | hS
  · exact norm_prefactor_le_three_eighths_of_mem_edgeWest hW
  · exact norm_prefactor_le_three_eighths_of_mem_edgeEast hE
  · exact norm_prefactor_le_three_eighths_of_mem_edgeNorth hN
  · exact norm_prefactor_le_three_eighths_of_mem_edgeSouth hS

/-- **Universal Boundary Prefactor Bound**: On all 4 boundary edges of `leftoverRect`,
`‖s * (s - 1) / 2‖ ≤ 1 / 2`. -/
theorem norm_prefactor_le_half_of_mem_boundaryEdges {s : ℂ} (hs : s ∈ boundaryEdges) :
    ‖s * (s - 1) / 2‖ ≤ 1 / 2 := by
  have := norm_prefactor_le_three_eighths_of_mem_boundaryEdges hs
  linarith

/-- Master boundary reduction: if `‖completedRiemannZeta₀ z‖ ≤ M` on the boundary edges
with `M < 1`, then the deviation `‖entireXi z - 1/2‖ < 1/2`. -/
theorem norm_entireXi_sub_half_lt_half_of_zeta₀_lt_one {s : ℂ}
    (hs : s ∈ boundaryEdges)
    {M : ℝ} (hM : ‖completedRiemannZeta₀ s‖ ≤ M) (hM_lt : M < 1) :
    ‖entireXi s - 1 / 2‖ < 1 / 2 := by
  rw [norm_entireXi_sub_half]
  have hpref := norm_prefactor_le_half_of_mem_boundaryEdges hs
  have hnonneg : 0 ≤ ‖completedRiemannZeta₀ s‖ := norm_nonneg _
  have hM_nonneg : 0 ≤ M := hnonneg.trans hM
  calc ‖s * (s - 1) / 2‖ * ‖completedRiemannZeta₀ s‖
      ≤ (1 / 2) * M := mul_le_mul hpref hM hnonneg (by norm_num)
    _ < (1 / 2) * 1 := by nlinarith [hM_lt]
    _ = 1 / 2 := by norm_num

/-! ### Topological Frontier of leftoverRect -/

/-- Open interior rectangle of leftoverRect. -/
def openInteriorRect : Set ℂ :=
  {z : ℂ | (2 : ℝ)⁻¹ < z.re ∧ z.re < 1 ∧ |z.im| < (2 : ℝ)⁻¹}

/-- `openInteriorRect` is an open set. -/
theorem isOpen_openInteriorRect : IsOpen openInteriorRect := by
  have h1 : IsOpen {z : ℂ | (2 : ℝ)⁻¹ < z.re} := isOpen_Ioi.preimage continuous_re
  have h2 : IsOpen {z : ℂ | z.re < 1} := isOpen_Iio.preimage continuous_re
  have h3 : IsOpen {z : ℂ | |z.im| < (2 : ℝ)⁻¹} :=
    isOpen_Iio.preimage (continuous_abs.comp continuous_im)
  have hint : openInteriorRect = ({z : ℂ | (2 : ℝ)⁻¹ < z.re} ∩ {z : ℂ | z.re < 1}) ∩ {z : ℂ | |z.im| < (2 : ℝ)⁻¹} := by
    ext z
    simp only [openInteriorRect, mem_ofPred_eq, mem_inter_iff, and_assoc]
  rw [hint]
  exact (h1.inter h2).inter h3

/-- `openInteriorRect` is a subset of `leftoverRect`. -/
theorem openInteriorRect_subset_leftoverRect : openInteriorRect ⊆ leftoverRect := by
  intro z hz
  exact ⟨le_of_lt hz.1, le_of_lt hz.2.1, le_of_lt hz.2.2⟩

/-- Therefore `openInteriorRect` is contained in `interior leftoverRect`. -/
theorem openInteriorRect_subset_interior : openInteriorRect ⊆ interior leftoverRect :=
  isOpen_openInteriorRect.subset_interior_iff.mpr openInteriorRect_subset_leftoverRect

/-- Any point in `frontier leftoverRect` must lie on one of the 4 boundary edges. -/
theorem frontier_leftoverRect_subset_boundaryEdges :
    frontier leftoverRect ⊆ boundaryEdges := by
  intro z hz
  have hz_rect : z ∈ leftoverRect := by
    have : frontier leftoverRect ⊆ closure leftoverRect := frontier_subset_closure
    rw [isCompact_leftoverRect.isClosed.closure_eq] at this
    exact this hz
  have hz_not_int : z ∉ interior leftoverRect := hz.2
  have hz_not_open : z ∉ openInteriorRect := fun h => hz_not_int (openInteriorRect_subset_interior h)
  have hcases : z.re ≤ (2 : ℝ)⁻¹ ∨ 1 ≤ z.re ∨ (2 : ℝ)⁻¹ ≤ |z.im| := by
    by_contra! hcontra
    exact hz_not_open ⟨hcontra.1, hcontra.2.1, hcontra.2.2⟩
  rcases hcases with (h1 | h2 | h3)
  · have : z.re = (2 : ℝ)⁻¹ := le_antisymm h1 hz_rect.1
    refine Or.inl (Or.inl (Or.inl ⟨hz_rect, this⟩))
  · have : z.re = 1 := le_antisymm hz_rect.2.1 h2
    refine Or.inl (Or.inl (Or.inr ⟨hz_rect, this⟩))
  · have habs : |z.im| = (2 : ℝ)⁻¹ := le_antisymm hz_rect.2.2 h3
    rcases le_total 0 z.im with hpos | hneg
    · rw [abs_of_nonneg hpos] at habs
      refine Or.inl (Or.inr ⟨hz_rect, habs⟩)
    · rw [abs_of_nonpos hneg] at habs
      have : z.im = - (2 : ℝ)⁻¹ := by linarith
      refine Or.inr ⟨hz_rect, this⟩


/-- **Master Frontier Prefactor Bound (Sharpened to 3/8)**: On the topological frontier of `leftoverRect`,
the quadratic prefactor is bounded by 3/8. -/
theorem norm_prefactor_le_three_eighths_of_mem_frontier {s : ℂ} (hs : s ∈ frontier leftoverRect) :
    ‖s * (s - 1) / 2‖ ≤ 3 / 8 :=
  norm_prefactor_le_three_eighths_of_mem_boundaryEdges (frontier_leftoverRect_subset_boundaryEdges hs)

/-- **Master Frontier Prefactor Bound**: On the topological frontier of `leftoverRect`,
the quadratic prefactor is bounded by 1/2. -/
theorem norm_prefactor_le_half_of_mem_frontier {s : ℂ} (hs : s ∈ frontier leftoverRect) :
    ‖s * (s - 1) / 2‖ ≤ 1 / 2 := by
  have := norm_prefactor_le_three_eighths_of_mem_frontier hs
  linarith

/-- **Master Frontier Reduction Theorem**:
If `‖completedRiemannZeta₀ z‖ ≤ M` on `frontier leftoverRect` with `M < 1`,
then `‖entireXi z - 1/2‖ < 1/2` everywhere on `frontier leftoverRect`. -/
theorem norm_entireXi_sub_half_lt_half_of_mem_frontier {s : ℂ}
    (hs : s ∈ frontier leftoverRect)
    {M : ℝ} (hM : ‖completedRiemannZeta₀ s‖ ≤ M) (hM_lt : M < 1) :
    ‖entireXi s - 1 / 2‖ < 1 / 2 := by
  have hs_b : s ∈ boundaryEdges := frontier_leftoverRect_subset_boundaryEdges hs
  exact norm_entireXi_sub_half_lt_half_of_zeta₀_lt_one hs_b hM hM_lt

/-- **Sharpened Frontier Deviation Bound**:
If `‖completedRiemannZeta₀ z‖ ≤ 1` on `frontier leftoverRect`,
then `‖entireXi z - 1/2‖ ≤ 3/8 < 1/2` everywhere on `frontier leftoverRect`. -/
theorem norm_entireXi_sub_half_le_three_eighths_of_zeta₀_le_one {s : ℂ}
    (hs : s ∈ frontier leftoverRect)
    (hM : ‖completedRiemannZeta₀ s‖ ≤ 1) :
    ‖entireXi s - 1 / 2‖ ≤ 3 / 8 := by
  rw [norm_entireXi_sub_half]
  have hpref := norm_prefactor_le_three_eighths_of_mem_frontier hs
  have hnonneg : 0 ≤ ‖completedRiemannZeta₀ s‖ := norm_nonneg _
  calc ‖s * (s - 1) / 2‖ * ‖completedRiemannZeta₀ s‖
      ≤ (3 / 8) * 1 := mul_le_mul hpref hM hnonneg (by norm_num)
    _ = 3 / 8 := by norm_num

/-- **Sharpened Strict Non-Vanishing Threshold**:
For any $z \in \text{frontier } leftoverRect$, if `‖completedRiemannZeta₀ z‖ ≤ 1`,
then the deviation strictly satisfies `‖entireXi z - 1/2‖ < 1/2` with a safety margin of at least 1/8. -/
theorem norm_entireXi_sub_half_lt_half_of_zeta₀_le_one {s : ℂ}
    (hs : s ∈ frontier leftoverRect)
    (hM : ‖completedRiemannZeta₀ s‖ ≤ 1) :
    ‖entireXi s - 1 / 2‖ < 1 / 2 := by
  have := norm_entireXi_sub_half_le_three_eighths_of_zeta₀_le_one hs hM
  linarith

end RhG1Lean


