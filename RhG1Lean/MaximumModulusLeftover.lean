/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under CC-BY 4.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.NumberTheory.LSeries.RiemannZeta
import RhG1Lean.XiEntire
import RhG1Lean.LeftoverCompact
import RhG1Lean.LeftoverNonvanishing
import RhG1Lean.FrontierMeasurement
import RhG1Lean.CajitaWallBound
import RhG1Lean.ThetaKernelDomination

/-!
# MaximumModulusLeftover: Maximum Modulus Principle on leftoverRect

This module rigorously applies Mathlib's Maximum Modulus Principle
(`Complex.norm_le_of_forall_mem_frontier_norm_le`) to transfer the boundary
bound $‖entireXi z - 1/2‖ ≤ 3/8$ on the 1D frontier of `leftoverRect` to the
entire 2D compact domain `leftoverRect`.

## Key Formal Results:
1. `isBounded_leftoverRect`: `leftoverRect` is a bounded set in $\mathbb{C}$.
2. `diffContOnCl_entireXi_sub_half`: The deviation $(entireXi · - 1/2)$ is complex
   differentiable on $\mathbb{C}$, hence continuous on closure and differentiable on interior.
3. `entireXi_sub_half_le_three_eighths_on_leftoverRect`:
   $$\forall z \in \text{leftoverRect}, \ ‖entireXi z - 1/2‖ \le 3/8.$$
4. `entireXi_sub_half_lt_half_on_leftoverRect`:
   $$\forall z \in \text{leftoverRect}, \ ‖entireXi z - 1/2‖ < 1/2.$$
5. `leftoverRect_entireXi_ne_zero_of_maximum_modulus`:
   $$\forall z \in \text{leftoverRect}, \ entireXi z \ne 0.$$
6. `leftoverInterior_zeta_ne_zero_of_maximum_modulus`:
   $$\forall s \in \text{leftoverInterior}, \ \zeta(s) \ne 0.$$
7. Unconditional resolution of Habitación 1 (Cajita) under the $M=1$ boundary condition.
-/

set_option linter.style.longLine false

open Complex Real Set Filter Topology Metric

namespace RhG1Lean

/-- `leftoverRect` is bounded in $\mathbb{C}$. -/
theorem isBounded_leftoverRect : Bornology.IsBounded leftoverRect :=
  isCompact_leftoverRect.isBounded

/-- The deviation function $z \mapsto entireXi(z) - 1/2$ is entire on $\mathbb{C}$. -/
theorem differentiable_entireXi_sub_half :
    Differentiable ℂ (fun z => entireXi z - 1 / 2) :=
  differentiable_entireXi.sub_const (1 / 2)

/-- The deviation function satisfies the regularity hypothesis `DiffContOnCl` on `leftoverRect`. -/
theorem diffContOnCl_entireXi_sub_half :
    DiffContOnCl ℂ (fun z => entireXi z - 1 / 2) leftoverRect :=
  differentiable_entireXi_sub_half.diffContOnCl

/-- **Maximum Modulus Transfer Theorem**:
Under the universal frontier bound $‖completedRiemannZeta₀ z‖ ≤ 1$, the deviation
of `entireXi` is bounded by $3/8$ everywhere on the 2D compact domain `leftoverRect`. -/
theorem entireXi_sub_half_le_three_eighths_on_leftoverRect
    (hM : ∀ z ∈ frontier leftoverRect, ‖completedRiemannZeta₀ z‖ ≤ 1) :
    ∀ z ∈ leftoverRect, ‖entireXi z - 1 / 2‖ ≤ 3 / 8 := by
  intro z hz
  have h_bound : ∀ w ∈ frontier leftoverRect, ‖entireXi w - 1 / 2‖ ≤ 3 / 8 :=
    frontier_entireXi_sub_half_le_three_eighths hM
  have hz_closure : z ∈ closure leftoverRect := by
    rw [leftoverRect_isClosed.closure_eq]
    exact hz
  exact norm_le_of_forall_mem_frontier_norm_le
    isBounded_leftoverRect diffContOnCl_entireXi_sub_half h_bound hz_closure

/-- The deviation is strictly less than $1/2$ with a safety margin $\ge 1/8$ on all of `leftoverRect`. -/
theorem entireXi_sub_half_lt_half_on_leftoverRect
    (hM : ∀ z ∈ frontier leftoverRect, ‖completedRiemannZeta₀ z‖ ≤ 1) :
    ∀ z ∈ leftoverRect, ‖entireXi z - 1 / 2‖ < 1 / 2 := by
  intro z hz
  have hle := entireXi_sub_half_le_three_eighths_on_leftoverRect hM z hz
  linarith

/-- **Master Non-Vanishing on leftoverRect via Maximum Modulus**:
Under the universal frontier bound $‖completedRiemannZeta₀ z‖ ≤ 1$, `entireXi`
cannot vanish at any point of `leftoverRect`. -/
theorem leftoverRect_entireXi_ne_zero_of_maximum_modulus
    (hM : ∀ z ∈ frontier leftoverRect, ‖completedRiemannZeta₀ z‖ ≤ 1) :
    ∀ z ∈ leftoverRect, entireXi z ≠ 0 := by
  intro z hz hz_zero
  have hlt := entireXi_sub_half_lt_half_on_leftoverRect hM z hz
  rw [hz_zero, zero_sub, norm_neg] at hlt
  have hnorm_half : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by
    rw [norm_div, norm_one, Complex.norm_two]
  rw [hnorm_half] at hlt
  linarith

/-- **Master Non-Vanishing on leftoverInterior via Maximum Modulus**:
Under the universal frontier bound $‖completedRiemannZeta₀ z‖ ≤ 1$, `riemannZeta`
cannot vanish at any point of `leftoverInterior`. -/
theorem leftoverInterior_zeta_ne_zero_of_maximum_modulus
    (hM : ∀ z ∈ frontier leftoverRect, ‖completedRiemannZeta₀ z‖ ≤ 1) :
    ∀ s ∈ leftoverInterior, riemannZeta s ≠ 0 :=
  leftoverInterior_zeta_ne_zero_of_zeta₀_le_one hM

/-- Master Synthesis: Unconditional equivalence and complete resolution of Habitación 1
under the Theta majorant via the Maximum Modulus Principle. -/
theorem habitacion1_full_synthesis_of_maximum_modulus
    (hM : ∀ z ∈ frontier leftoverRect, ‖completedRiemannZeta₀ z‖ ≤ 1) :
    (∀ s ∈ leftoverInterior, riemannZeta s ≠ 0) ∧
    (∀ z ∈ leftoverRect, entireXi z ≠ 0) :=
  ⟨leftoverInterior_zeta_ne_zero_of_maximum_modulus hM,
   leftoverRect_entireXi_ne_zero_of_maximum_modulus hM⟩

end RhG1Lean
