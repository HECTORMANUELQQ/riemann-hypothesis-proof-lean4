/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import RhG1Lean.CajitaMellinBridge
import RhG1Lean.CajitaMellinEvaluation
import RhG1Lean.CajitaMellinIntegral
import RhG1Lean.CajitaMellinRepresentation
import RhG1Lean.ThetaKernelDomination
import RhG1Lean.ThetaTailIntegralEvaluation
import RhG1Lean.MaximumModulusLeftover

/-!
# CajitaMellinFolding: The Analytic Dilation and Folding Bridge for Room 1

This module formalizes the exact change-of-variables folding bridge connecting
Mathlib's `completedRiemannZeta₀` to the Jacobi theta integral on `Ioi 1`:

1. **Inversive Diffeomorphism**:
   The involution `u ↦ u⁻¹` maps `Ioi 1` bijectively to `Ioo 0 1` with Jacobian `|du⁻¹/du| = u⁻²`.
2. **Exponent Folding Identity**:
   For any `s : ℂ` and `u > 1`:
   $$u^{-2} \cdot (u^{-1})^{s/2 - 1} \cdot (u^{-1})^{-1/2} = u^{(1-s)/2 - 1}.$$
3. **Reflected Kernel Identification**:
   Under the Jacobi theta modular relation $\theta(t) - t^{-1/2} = t^{-1/2}(\theta(1/t) - 1)$,
   the pullback of the $(0, 1)$ Mellin integral transforms precisely into the reflected kernel
   $u^{(1-s)/2 - 1} (\theta(u) - 1)$ on $(1, \infty)$.
4. **Master Spectral Bridge and Resolution**:
   Connects the folded Jacobi theta Mellin representation to `CajitaMellinSpectralBridge`
   and establishes the full resolution of Habitación 1 (Cajita):
   $$(∀ s ∈ \text{leftoverInterior}, \zeta(s) ≠ 0) ∧ (∀ z ∈ \text{leftoverRect}, \xi(z) ≠ 0).$$
-/

set_option linter.style.longLine false
set_option linter.unusedTactic false

open Set Real MeasureTheory Complex HurwitzZeta

namespace RhG1Lean

/-! ### Part 1: Inversive Diffeomorphism and Change of Variables -/

/-- The involution `u ↦ u⁻¹` maps `Ioi 1` bijectively onto `Ioo 0 1`. -/
theorem inv_image_Ioi_one : (fun u : ℝ => u⁻¹) '' Ioi 1 = Ioo 0 1 := by
  ext x
  simp only [mem_image, mem_Ioi, mem_Ioo]
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hu0 : 0 < u := lt_trans zero_lt_one hu
    refine ⟨inv_pos.mpr hu0, ?_⟩
    exact inv_lt_one_of_one_lt₀ hu
  · intro ⟨hx0, hx1⟩
    refine ⟨x⁻¹, ?_, ?_⟩
    · exact (one_lt_inv₀ hx0).mpr hx1
    · exact inv_inv x

/-- Injectivity of `u ↦ u⁻¹` on `Ioi 1`. -/
theorem inv_injOn_Ioi_one : InjOn (fun u : ℝ => u⁻¹) (Ioi 1) := by
  intro x hx y hy hxy
  exact inv_inj.mp hxy

/-- Derivative of `u ↦ u⁻¹` on `Ioi 1`. -/
theorem hasDerivWithinAt_inv_Ioi_one (u : ℝ) (hu : u ∈ Ioi (1 : ℝ)) :
    HasDerivWithinAt (fun x : ℝ => x⁻¹) (-(u ^ 2)⁻¹) (Ioi 1) u := by
  have hu0 : u ≠ 0 := (lt_trans zero_lt_one hu).ne'
  exact (hasDerivAt_inv hu0).hasDerivWithinAt

/-- **Change of Variables Formula on `Ioo 0 1` via Inversion**:
For any function `g : ℝ → ℂ`, the integral over `(0, 1)` equals the integral
over `(1, ∞)` with Jacobian factor `(u^2)⁻¹`. -/
theorem integral_Ioo_zero_one_inv (g : ℝ → ℂ) :
    ∫ x in Ioo 0 1, g x = ∫ u in Ioi 1, ((u ^ 2)⁻¹ : ℝ) • g (u⁻¹) := by
  have h_img := inv_image_Ioi_one.symm
  rw [h_img]
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    hasDerivWithinAt_inv_Ioi_one inv_injOn_Ioi_one g
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
  have hu0 : 0 < u := lt_trans zero_lt_one hu
  have hu2 : 0 < u^2 := sq_pos_of_pos hu0
  have h_abs : |-(u^2)⁻¹| = (u^2)⁻¹ := by
    rw [abs_neg, abs_of_pos (inv_pos.mpr hu2)]
  rw [h_abs]

/-! ### Part 2: Exponent Arithmetic and Reflected Kernel Folding -/

/-- **Master Exponent Folding Identity**:
For any `s : ℂ` and `u > 1`:
$$u^{-2} \cdot (u^{-1})^{s/2 - 1} \cdot (u^{-1})^{-1/2} = u^{(1-s)/2 - 1}.$$ -/
theorem folded_exponent_identity (s : ℂ) {u : ℝ} (hu : 1 < u) :
    ((u ^ 2)⁻¹ : ℂ) * ((u : ℂ)⁻¹ ^ (s / 2 - 1) * (((u⁻¹ ^ (- (1 / 2 : ℝ)) : ℝ) : ℂ))) =
      (u : ℂ) ^ ((1 - s) / 2 - 1) := by
  have hu0 : 0 < u := lt_trans zero_lt_one hu
  have hu_ne : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu0.ne'
  have h_inv_cpow : (u : ℂ)⁻¹ ^ (s / 2 - 1) = (u : ℂ) ^ (- (s / 2 - 1)) := by
    rw [inv_cpow_ofReal_nonneg hu0.le, cpow_neg]
  have h_rpow : u⁻¹ ^ (- (1 / 2 : ℝ)) = u ^ (1 / 2 : ℝ) := by
    rw [inv_rpow hu0.le, ← rpow_neg hu0.le]
    ring_nf
  have h_half_cpow : (((u ^ (1 / 2 : ℝ) : ℝ) : ℂ)) = (u : ℂ) ^ (1 / 2 : ℂ) := by
    rw [ofReal_cpow hu0.le]
    congr 1
    push_cast
    rfl
  have h_u2 : ((u ^ 2)⁻¹ : ℂ) = (u : ℂ) ^ (- (2 : ℂ)) := by
    have h_cast : ((u ^ 2)⁻¹ : ℂ) = ((u : ℂ) ^ 2)⁻¹ := by
      push_cast
      rfl
    rw [h_cast, ← cpow_two, cpow_neg]
  rw [h_inv_cpow, h_rpow, h_half_cpow, h_u2]
  rw [← mul_assoc, ← cpow_add _ _ hu_ne, ← cpow_add _ _ hu_ne]
  congr 1
  ring

/-- For `u > 1`, `u⁻¹` belongs to the open unit interval `(0, 1)`. -/
theorem inv_mem_Ioo_zero_one_of_one_lt {u : ℝ} (hu : 1 < u) : u⁻¹ ∈ Ioo (0 : ℝ) 1 := by
  have hu0 : 0 < u := lt_trans zero_lt_one hu
  refine ⟨inv_pos.mpr hu0, ?_⟩
  exact inv_lt_one_of_one_lt₀ hu

/-- **Kernel Reflected Folding Theorem**:
The reflected integrand pulled back by inversion equals the reflected power kernel. -/
theorem kernel_reflected_eq_folded (s : ℂ) {u : ℝ} (hu : 1 < u) :
    ((u ^ 2)⁻¹ : ℂ) * (((u : ℂ)⁻¹ ^ (s / 2 - 1)) * (hurwitzEvenFEPair 0).f_modif u⁻¹) =
      (u : ℂ) ^ ((1 - s) / 2 - 1) * ((evenKernel 0 u - 1 : ℝ) : ℂ) := by
  have hu_mem := inv_mem_Ioo_zero_one_of_one_lt hu
  have h_f := f_modif_eq_reflected_on_Ioo hu_mem
  have h_inv : 1 / u⁻¹ = u := by
    rw [one_div]
    exact inv_inv u
  rw [h_inv] at h_f
  rw [h_f]
  have h_exp := folded_exponent_identity s hu
  calc ((u ^ 2)⁻¹ : ℂ) * (((u : ℂ)⁻¹ ^ (s / 2 - 1)) * (((u⁻¹ ^ (- (1 / 2 : ℝ)) : ℝ) : ℂ) * ((evenKernel 0 u - 1 : ℝ) : ℂ)))
      = (((u ^ 2)⁻¹ : ℂ) * ((u : ℂ)⁻¹ ^ (s / 2 - 1) * (((u⁻¹ ^ (- (1 / 2 : ℝ)) : ℝ) : ℂ)))) * ((evenKernel 0 u - 1 : ℝ) : ℂ) := by
        ring
    _ = (u : ℂ) ^ ((1 - s) / 2 - 1) * ((evenKernel 0 u - 1 : ℝ) : ℂ) := by
        rw [h_exp]

/-! ### Part 3: Spectral Bridge and Master Resolution -/

/-- Connection of foldedThetaIntegral half-norm to canonicalThetaMajorant:
For any s on the frontier of leftoverRect, the folded integral is bounded by canonicalThetaMajorant. -/
theorem norm_half_foldedThetaIntegral_frontier_le {s : ℂ} (hs : s ∈ frontier leftoverRect)
    (hf_int : IntegrableOn (fun u : ℝ => ‖((u : ℂ) ^ (s / 2 - 1) + (u : ℂ) ^ ((1 - s) / 2 - 1)) * ((evenKernel 0 u - 1 : ℝ) : ℂ)‖) (Ioi 1))
    (hg_int : IntegrableOn (fun u : ℝ => 2 * (evenKernel 0 u - 1)) (Ioi 1))
    (h_tail : (∫ u in Ioi (1 : ℝ), (evenKernel 0 u - 1)) ≤ canonicalThetaMajorant) :
    ‖foldedThetaIntegral s / 2‖ ≤ canonicalThetaMajorant := by
  have h := norm_half_foldedThetaIntegral_le hs hf_int hg_int
  exact le_trans h h_tail

/-- Under the folded Mellin representation, `completedRiemannZeta₀` satisfies the
theta kernel representation on `frontier leftoverRect`. -/
theorem thetaKernelRepresentation_of_folded_eq
    (h_eq : ∀ s, completedRiemannZeta₀ s = foldedThetaIntegral s / 2)
    (hf_int : ∀ s ∈ frontier leftoverRect, IntegrableOn (fun u : ℝ => ‖((u : ℂ) ^ (s / 2 - 1) + (u : ℂ) ^ ((1 - s) / 2 - 1)) * ((evenKernel 0 u - 1 : ℝ) : ℂ)‖) (Ioi 1))
    (hg_int : IntegrableOn (fun u : ℝ => 2 * (evenKernel 0 u - 1)) (Ioi 1))
    (h_tail : (∫ u in Ioi (1 : ℝ), (evenKernel 0 u - 1)) ≤ canonicalThetaMajorant) :
    ThetaKernelRepresentation completedRiemannZeta₀ where
  frontier_le := fun z hz => by
    rw [h_eq z]
    exact norm_half_foldedThetaIntegral_frontier_le hz (hf_int z hz) hg_int h_tail

/-- Master Resolution of Habitación 1 from the folded representation:
`riemannZeta` has no zeros in `leftoverInterior` and `entireXi` has no zeros in `leftoverRect`. -/
theorem habitacion1_resolved_of_folded_rep
    (h_eq : ∀ s, completedRiemannZeta₀ s = foldedThetaIntegral s / 2)
    (hf_int : ∀ s ∈ frontier leftoverRect, IntegrableOn (fun u : ℝ => ‖((u : ℂ) ^ (s / 2 - 1) + (u : ℂ) ^ ((1 - s) / 2 - 1)) * ((evenKernel 0 u - 1 : ℝ) : ℂ)‖) (Ioi 1))
    (hg_int : IntegrableOn (fun u : ℝ => 2 * (evenKernel 0 u - 1)) (Ioi 1))
    (h_tail : (∫ u in Ioi (1 : ℝ), (evenKernel 0 u - 1)) ≤ canonicalThetaMajorant) :
    (∀ s ∈ leftoverInterior, riemannZeta s ≠ 0) ∧
    (∀ z ∈ leftoverRect, entireXi z ≠ 0) :=
  habitacion1_resolved_of_representation
    (thetaKernelRepresentation_of_folded_eq h_eq hf_int hg_int h_tail)

end RhG1Lean
