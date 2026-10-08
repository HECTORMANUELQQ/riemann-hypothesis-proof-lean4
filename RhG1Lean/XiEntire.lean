/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under CC-BY 4.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.AbsMax
import RhG1Lean.Leftover
import RhG1Lean.Majorant
import RhG1Lean.FunEq
import RhG1Lean.LeftoverCore
import RhG1Lean.Lip

/-!
# Entire ξ: Completion of Riemann ξ without pole singularities

`riemannXi s` in mathlib has a junk value at `s = 1` because `riemannZeta 1` is junk,
causing `riemannXi 1 = 0` and breaking holomorphy at `s = 1`.

`entireXi s` is defined directly using `completedRiemannZeta₀ s` (which is entire):
  `entireXi s = (s * (s - 1) / 2) * completedRiemannZeta₀ s + 1 / 2`

Properties:
1. `Differentiable ℂ entireXi` everywhere on ℂ.
2. `entireXi 1 = 1 / 2 ≠ 0`.
3. `entireXi 0 = 1 / 2 ≠ 0`.
4. `entireXi (1 - s) = entireXi s` everywhere on ℂ (unconditional functional equation).
5. For all `s ∉ {0, 1}`, `entireXi s = (s * (s - 1) / 2) * completedRiemannZeta s`.
6. For all `s ∈ leftoverInterior`, `entireXi s = riemannXi s`.
7. For all `s ∈ leftoverInterior`, `entireXi s = 0 ↔ riemannZeta s = 0`.
8. `entireXi` is Lipschitz on `leftoverRect` (which is convex and compact, no cutout needed).
-/

open Complex Real Set Filter Topology Metric
open scoped NNReal

namespace RhG1Lean

/-- The canonical entire Riemann xi function. -/
noncomputable def entireXi (s : ℂ) : ℂ :=
  (s * (s - 1) / 2) * completedRiemannZeta₀ s + 1 / 2

/-- `entireXi` is entire (differentiable everywhere on ℂ). -/
theorem differentiable_entireXi : Differentiable ℂ entireXi := by
  unfold entireXi
  refine (Differentiable.mul ?_ differentiable_completedZeta₀).add (differentiable_const _)
  exact ((differentiable_id.mul (differentiable_id.sub (differentiable_const 1))).div_const 2)

theorem continuous_entireXi : Continuous entireXi :=
  differentiable_entireXi.continuous

/-- At s = 1, `entireXi 1 = 1 / 2`. -/
@[simp]
theorem entireXi_one : entireXi 1 = 1 / 2 := by
  simp [entireXi]

/-- At s = 0, `entireXi 0 = 1 / 2`. -/
@[simp]
theorem entireXi_zero : entireXi 0 = 1 / 2 := by
  simp [entireXi]

/-- Unconditional functional equation: `entireXi (1 - s) = entireXi s` everywhere on ℂ. -/
theorem entireXi_one_sub (s : ℂ) : entireXi (1 - s) = entireXi s := by
  unfold entireXi
  rw [prefactor_xi_one_sub s, completedRiemannZeta₀_one_sub s]

/-- Key pole cancellation identity:
`-(s*(s-1)/2 * (1/s)) - (s*(s-1)/2 * (1/(1-s))) = 1/2` for `s ≠ 0, 1`. -/
lemma mul_sub_inv_eq (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    - (s * (s - 1) / 2 * (1 / s)) - (s * (s - 1) / 2 * (1 / (1 - s))) = (1 : ℂ) / 2 := by
  have h1 : (s * (s - 1) / 2 * (1 / s)) = (s - 1) / 2 := by
    calc
      s * (s - 1) / 2 * (1 / s) = (s * (1 / s)) * (s - 1) / 2 := by ring
      _ = 1 * (s - 1) / 2 := by rw [mul_one_div_cancel hs0]
      _ = (s - 1) / 2 := by ring
  have h2 : (s * (s - 1) / 2 * (1 / (1 - s))) = - s / 2 := by
    have hsub : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
    have hsm1 : s - 1 = - (1 - s) := by ring
    calc
      s * (s - 1) / 2 * (1 / (1 - s)) = s * (- (1 - s)) / 2 * (1 / (1 - s)) := by rw [hsm1]
      _ = - (s * ((1 - s) * (1 / (1 - s))) / 2) := by ring
      _ = - (s * 1 / 2) := by rw [mul_one_div_cancel hsub]
      _ = - s / 2 := by ring
  rw [h1, h2]
  ring

/-- Away from `{0, 1}`, `entireXi` agrees with `(s * (s - 1) / 2) * completedRiemannZeta s`. -/
theorem entireXi_eq_mul_completedRiemannZeta {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    entireXi s = (s * (s - 1) / 2) * completedRiemannZeta s := by
  unfold entireXi
  rw [completedRiemannZeta_eq s]
  have h := mul_sub_inv_eq s hs0 hs1
  calc
    (s * (s - 1) / 2) * completedRiemannZeta₀ s + 1 / 2
        = (s * (s - 1) / 2) * completedRiemannZeta₀ s +
            (- (s * (s - 1) / 2 * (1 / s)) - (s * (s - 1) / 2 * (1 / (1 - s)))) := by rw [h]
    _ = (s * (s - 1) / 2) * (completedRiemannZeta₀ s - 1 / s - 1 / (1 - s)) := by ring

/-- Away from `{0, 1}` and poles of `Gammaℝ`, `entireXi` equals `riemannXi`. -/
theorem entireXi_eq_riemannXi {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hG : Gammaℝ s ≠ 0) :
    entireXi s = riemannXi s := by
  rw [entireXi_eq_mul_completedRiemannZeta hs0 hs1,
      riemannXi_eq_mul_completedRiemannZeta hs0 hG]

/-- On `leftoverInterior`, `entireXi` equals `riemannXi`. -/
theorem entireXi_eq_riemannXi_leftoverInterior {s : ℂ} (hs : s ∈ leftoverInterior) :
    entireXi s = riemannXi s := by
  have hs0 : s ≠ 0 := ne_zero_of_mem_leftoverRect (mem_leftoverInterior.mp hs).1
  have hs1 : s ≠ 1 := ne_one_of_mem_leftoverInterior hs
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_mem_leftoverRect (mem_leftoverInterior.mp hs).1
  exact entireXi_eq_riemannXi hs0 hs1 hG

/-- On `leftoverInterior`, `entireXi s = 0 ↔ riemannZeta s = 0`. -/
theorem entireXi_eq_zero_iff_zeta_leftoverInterior {s : ℂ} (hs : s ∈ leftoverInterior) :
    entireXi s = 0 ↔ riemannZeta s = 0 := by
  rw [entireXi_eq_riemannXi_leftoverInterior hs]
  have hR : s ∈ leftoverRect := (mem_leftoverInterior.mp hs).1
  have hs1 : s ≠ 1 := ne_one_of_mem_leftoverInterior hs
  exact riemannXi_eq_zero_iff_zeta_leftoverRect hR hs1

/-! ### Lipschitz bounds on leftoverRect -/

/-- `entireXi` is Lipschitz on any convex set where `‖deriv entireXi‖₊ ≤ C`. -/
theorem entireXi_lipschitz_on_convex {s : Set ℂ} (hs : Convex ℝ s)
    {C : NNReal} (hC : ∀ z ∈ s, ‖deriv entireXi z‖₊ ≤ C) :
    LipschitzOnWith C entireXi s :=
  hs.lipschitzOnWith_of_nnnorm_deriv_le
    (fun _ _ => differentiable_entireXi.differentiableAt) hC

theorem continuous_deriv_entireXi : Continuous (deriv entireXi) := by
  have hdiff : DifferentiableOn ℂ entireXi univ :=
    differentiable_entireXi.differentiableOn
  have hAnalNhd : AnalyticOnNhd ℂ entireXi univ :=
    hdiff.analyticOnNhd isOpen_univ
  have hderiv : AnalyticOnNhd ℂ (deriv entireXi) univ :=
    hAnalNhd.deriv_of_isOpen isOpen_univ
  exact continuous_iff_continuousAt.mpr
    (fun z => (hderiv z (mem_univ z)).continuousAt)

/-- There exists a bound `C : NNReal` for `‖deriv entireXi‖₊` on `leftoverRect`. -/
theorem exists_nnnorm_deriv_entireXi_le_leftoverRect :
    ∃ C : NNReal, ∀ s ∈ leftoverRect, ‖deriv entireXi s‖₊ ≤ C := by
  have hcont : ContinuousOn (deriv entireXi) leftoverRect :=
    continuous_deriv_entireXi.continuousOn
  obtain ⟨C0, hC0⟩ :=
    isCompact_leftoverRect.exists_bound_of_continuousOn hcont
  refine ⟨Real.toNNReal C0, fun z hz => ?_⟩
  have hle := hC0 z hz
  have hnonneg : 0 ≤ ‖deriv entireXi z‖ := norm_nonneg _
  have hC0_nonneg : 0 ≤ C0 := hnonneg.trans hle
  have h_toNNReal : ‖deriv entireXi z‖ ≤ Real.toNNReal C0 := by
    rw [Real.coe_toNNReal C0 hC0_nonneg]
    exact hle
  exact h_toNNReal

/-- 1 ∈ leftoverRect. -/
theorem mem_leftoverRect_one : (1 : ℂ) ∈ leftoverRect := by
  refine ⟨by norm_num, by norm_num, by simp⟩

/-- `entireXi` is Lipschitz on `leftoverRect`. -/
theorem entireXi_lipschitz_on_leftoverRect :
    ∃ C : NNReal, LipschitzOnWith C entireXi leftoverRect ∧
      ∀ s ∈ leftoverRect, ‖entireXi s - 1 / 2‖ ≤ C * ‖s - 1‖ := by
  obtain ⟨C, hC⟩ := exists_nnnorm_deriv_entireXi_le_leftoverRect
  have hlip := entireXi_lipschitz_on_convex convex_leftoverRect hC
  refine ⟨C, hlip, ?_⟩
  intro s hs
  have h1 : (1 : ℂ) ∈ leftoverRect := mem_leftoverRect_one
  have hdist := hlip.dist_le_mul s hs 1 h1
  rw [entireXi_one] at hdist
  simpa [dist_eq_norm] using hdist

/-- Every point in `leftoverRect` is within distance 1 of 1. -/
theorem norm_sub_one_le_one_of_mem_leftoverRect {s : ℂ} (hs : s ∈ leftoverRect) :
    ‖s - 1‖ ≤ 1 := by
  have hdec : s - 1 = ((s.re - 1 : ℝ) : ℂ) + ((s.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  have htri : ‖s - 1‖ ≤ ‖((s.re - 1 : ℝ) : ℂ)‖ + ‖((s.im : ℝ) : ℂ) * I‖ := by
    rw [hdec]
    exact norm_add_le _ _
  have hnorm_re : ‖((s.re - 1 : ℝ) : ℂ)‖ = |s.re - 1| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hnorm_im : ‖((s.im : ℝ) : ℂ) * I‖ = |s.im| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm_re, hnorm_im] at htri
  have hre : |s.re - 1| ≤ (1 : ℝ) / 2 := by
    rw [abs_le]
    have : (2 : ℝ)⁻¹ ≤ s.re := hs.1
    have : s.re ≤ 1 := hs.2.1
    constructor <;> linarith
  have him : |s.im| ≤ (1 : ℝ) / 2 := by
    have : |s.im| ≤ (2 : ℝ)⁻¹ := hs.2.2
    linarith
  linarith

/-- If `‖deriv entireXi‖₊ ≤ C` on `leftoverRect` with `C < 1/2`, then `entireXi`
does not vanish on `leftoverRect`. -/
theorem entireXi_ne_zero_of_deriv_lt_half {C : NNReal}
    (hC : ∀ s ∈ leftoverRect, ‖deriv entireXi s‖₊ ≤ C)
    (hC_lt : (C : ℝ) < 1 / 2) :
    ∀ s ∈ leftoverRect, entireXi s ≠ 0 := by
  intro s hs hz
  have hlip := entireXi_lipschitz_on_convex convex_leftoverRect hC
  have h1 : (1 : ℂ) ∈ leftoverRect := mem_leftoverRect_one
  have hdist := hlip.dist_le_mul s hs 1 h1
  rw [entireXi_one, hz, dist_zero_left, dist_eq_norm] at hdist
  have hhalf : ‖(1 / 2 : ℂ)‖ = (1 : ℝ) / 2 := by norm_num
  rw [hhalf] at hdist
  have hnorm1 : ‖s - 1‖ ≤ 1 := norm_sub_one_le_one_of_mem_leftoverRect hs
  have hle : (1 : ℝ) / 2 ≤ (C : ℝ) := by
    have : (C : ℝ) * ‖s - 1‖ ≤ (C : ℝ) * 1 := by
      refine mul_le_mul_of_nonneg_left hnorm1 (NNReal.coe_nonneg C)
    rw [mul_one] at this
    linarith
  linarith

/-- **Gap 5.1 Resolution**: Under a derivative bound `C < 1/2` on `leftoverRect`,
`riemannZeta` does not vanish on `leftoverInterior`. -/
theorem leftoverInterior_zeta_ne_zero_of_deriv_lt_half {C : NNReal}
    (hC : ∀ s ∈ leftoverRect, ‖deriv entireXi s‖₊ ≤ C)
    (hC_lt : (C : ℝ) < 1 / 2) :
    ∀ s ∈ leftoverInterior, riemannZeta s ≠ 0 := by
  intro s hs hz
  have hR : s ∈ leftoverRect := (mem_leftoverInterior.mp hs).1
  have h_ne := entireXi_ne_zero_of_deriv_lt_half hC hC_lt s hR
  have hz' : entireXi s = 0 := (entireXi_eq_zero_iff_zeta_leftoverInterior hs).mpr hz
  exact h_ne hz'

/-- **Cauchy Derivative Bound for `entireXi`**:
For any center $c \in \mathbb{C}$ and radius $R > 0$, the derivative of `entireXi` at $c$
is bounded by the maximum modulus $M$ on the sphere of radius $R$ divided by $R$. -/
theorem deriv_entireXi_le_of_sphere_bound (c : ℂ) {R M : ℝ} (hR : 0 < R)
    (hM : ∀ z ∈ Metric.sphere c R, ‖entireXi z‖ ≤ M) :
    ‖deriv entireXi c‖ ≤ M / R :=
  norm_deriv_le_of_forall_mem_sphere_norm_le hR differentiable_entireXi.diffContOnCl hM

/-! ### Maximum Modulus Principle for leftoverRect -/

/-- **Maximum Modulus Principle for `entireXi - 1/2`**:
The maximum distance of `entireXi` from `1/2` on `leftoverRect` is bounded
by its maximum on the frontier of `leftoverRect`. -/
theorem entireXi_sub_half_le_of_frontier_le {B : ℝ}
    (hB : ∀ z ∈ frontier leftoverRect, ‖entireXi z - 1 / 2‖ ≤ B) :
    ∀ s ∈ leftoverRect, ‖entireXi s - 1 / 2‖ ≤ B := by
  have hdiff : DiffContOnCl ℂ (fun z => entireXi z - 1 / 2) leftoverRect :=
    (differentiable_entireXi.sub_const (1 / 2)).diffContOnCl
  have hbounded := isCompact_leftoverRect.isBounded
  intro s hs
  have hcl : s ∈ closure leftoverRect := by
    rw [isCompact_leftoverRect.isClosed.closure_eq]
    exact hs
  exact Complex.norm_le_of_forall_mem_frontier_norm_le hbounded hdiff hB hcl

/-- If `entireXi s` is strictly closer to `1/2` than `1/2`, it cannot be zero. -/
theorem entireXi_ne_zero_of_sub_half_lt {s : ℂ}
    (h : ‖entireXi s - 1 / 2‖ < 1 / 2) :
    entireXi s ≠ 0 := by
  intro hz
  have hdist : ‖(0 : ℂ) - 1 / 2‖ < 1 / 2 := by
    calc ‖(0 : ℂ) - 1 / 2‖ = ‖entireXi s - 1 / 2‖ := by rw [hz]
    _ < 1 / 2 := h
  rw [zero_sub, norm_neg] at hdist
  have hhalf : ‖(1 / 2 : ℂ)‖ = (1 : ℝ) / 2 := by norm_num
  rw [hhalf] at hdist
  linarith

/-- **Maximum Modulus Non-vanishing Theorem on leftoverRect**:
If the maximum deviation $\|entireXi(z) - 1/2\|$ on the frontier of `leftoverRect`
is bounded by $B < 1/2$, then `entireXi` does not vanish on all of `leftoverRect`. -/
theorem leftoverRect_entireXi_ne_zero_of_frontier_lt_half
    {B : ℝ} (hB_lt : B < 1 / 2)
    (hB : ∀ z ∈ frontier leftoverRect, ‖entireXi z - 1 / 2‖ ≤ B) :
    ∀ s ∈ leftoverRect, entireXi s ≠ 0 := by
  intro s hs
  have hle := entireXi_sub_half_le_of_frontier_le hB s hs
  have hlt : ‖entireXi s - 1 / 2‖ < 1 / 2 := lt_of_le_of_lt hle hB_lt
  exact entireXi_ne_zero_of_sub_half_lt hlt

/-- **Maximum Modulus Non-vanishing of Zeta on leftoverInterior**:
Under a frontier bound $B < 1/2$, `riemannZeta` has no zeros on `leftoverInterior`. -/
theorem leftoverInterior_zeta_ne_zero_of_frontier_lt_half
    {B : ℝ} (hB_lt : B < 1 / 2)
    (hB : ∀ z ∈ frontier leftoverRect, ‖entireXi z - 1 / 2‖ ≤ B) :
    ∀ s ∈ leftoverInterior, riemannZeta s ≠ 0 := by
  intro s hs hz
  have hs_rect : s ∈ leftoverRect := (mem_leftoverInterior.mp hs).1
  have h_xi_ne := leftoverRect_entireXi_ne_zero_of_frontier_lt_half hB_lt hB s hs_rect
  have h_xi_zero : entireXi s = 0 := (entireXi_eq_zero_iff_zeta_leftoverInterior hs).mpr hz
  exact h_xi_ne h_xi_zero

end RhG1Lean


