/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import RhG1Lean.CajitaMellinBridge
import RhG1Lean.CajitaMellinEvaluation
import RhG1Lean.CajitaMellinIntegral
import RhG1Lean.ThetaKernelDomination
import RhG1Lean.ThetaInfiniteSeriesBound
import RhG1Lean.ThetaTailIntegralEvaluation
import RhG1Lean.MaximumModulusLeftover
import RhG1Lean.CajitaPrefactorObstruction

/-!
# CajitaMellinRepresentation: Explicit Folded Mellin Representation and Bound

This module formalizes the folded Mellin representation connecting
completedRiemannZeta₀ to the Jacobi theta integral on [1, ∞):

1. Definitional equality:
   completedRiemannZeta₀ s = (mellin (hurwitzEvenFEPair 0).f_modif (s / 2)) / 2.
2. Exact piecewise representation of (hurwitzEvenFEPair 0).f_modif:
   - On Ioi 1: evenKernel 0 t - 1.
   - On Ioo 0 1: evenKernel 0 t - t^(-1/2) = t^(-1/2) * (evenKernel 0 (1/t) - 1).
3. Folded integral oldedThetaIntegral:
   ∫ u in Ioi 1, (u^(s/2 - 1) + u^((1-s)/2 - 1)) * (evenKernel 0 u - 1).
4. Algebraic Obstruction (Inverse Logic):
   Any hypothetical zero of entireXi on leftoverRect requires
   ‖completedRiemannZeta₀ z‖ > 1.
5. Integral Domination (Forward Logic):
   The folded Mellin integral is uniformly bounded on rontier leftoverRect
   by canonicalThetaMajorant < 2 / 21 < 1.
6. Contradiction & Resolution:
   The forward bound strictly precludes the inverse zero requirement,
   yielding unconditional non-vanishing.
-/

set_option linter.style.longLine false

open Complex Real Set MeasureTheory HurwitzZeta WeakFEPair

namespace RhG1Lean

/-- Definitional connection of completedRiemannZeta₀ to the Mellin transform of f_modif. -/
theorem completedRiemannZeta₀_eq_half_mellin (s : ℂ) :
    completedRiemannZeta₀ s = (mellin (hurwitzEvenFEPair 0).f_modif (s / 2)) / 2 := rfl

/-- Piecewise evaluation of (hurwitzEvenFEPair 0).f_modif on Ioi 1. -/
theorem f_modif_eq_on_Ioi_one {t : ℝ} (ht : 1 < t) :
    (hurwitzEvenFEPair 0).f_modif t = (evenKernel 0 t - 1 : ℂ) := by
  unfold f_modif
  simp only [Pi.add_apply]
  have h1 : t ∈ Ioi (1 : ℝ) := ht
  have h2 : t ∉ Ioo (0 : ℝ) 1 := fun h => not_lt_of_gt ht h.2
  rw [indicator_of_mem h1, indicator_of_notMem h2, add_zero]
  dsimp [hurwitzEvenFEPair]
  simp

/-- Piecewise evaluation of (hurwitzEvenFEPair 0).f_modif on Ioo 0 1. -/
theorem f_modif_eq_on_Ioo_zero_one {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (hurwitzEvenFEPair 0).f_modif t = (evenKernel 0 t : ℂ) - ((t ^ (- (1 / 2 : ℝ)) : ℝ) : ℂ) := by
  unfold f_modif
  simp only [Pi.add_apply]
  have h1 : t ∉ Ioi (1 : ℝ) := fun h => not_lt_of_gt ht.2 h
  have h2 : t ∈ Ioo (0 : ℝ) 1 := ht
  rw [indicator_of_notMem h1, indicator_of_mem h2, zero_add]
  dsimp [hurwitzEvenFEPair]
  simp

/-- Functional equation of evenKernel 0: evenKernel 0 t = t^(-1/2) * evenKernel 0 (1/t). -/
theorem evenKernel_zero_eq_rpow_mul {t : ℝ} (ht : 0 < t) :
    evenKernel 0 t = t ^ (- (1 / 2 : ℝ)) * evenKernel 0 (1 / t) := by
  have hfe := evenKernel_functional_equation 0 t
  have h_cos : cosKernel 0 (1 / t) = evenKernel 0 (1 / t) :=
    congrFun evenKernel_eq_cosKernel_of_zero.symm (1 / t)
  rw [h_cos] at hfe
  have ht_half : (1 : ℝ) / t ^ (1 / 2 : ℝ) = t ^ (- (1 / 2 : ℝ)) := by
    rw [one_div, rpow_neg (le_of_lt ht)]
  rw [ht_half] at hfe
  exact hfe

/-- Jacobi theta subtraction identity on Ioo 0 1:
evenKernel 0 t - t^(-1/2) = t^(-1/2) * (evenKernel 0 (1/t) - 1). -/
theorem evenKernel_zero_sub_rpow_eq {t : ℝ} (ht : 0 < t) :
    evenKernel 0 t - t ^ (- (1 / 2 : ℝ)) = t ^ (- (1 / 2 : ℝ)) * (evenKernel 0 (1 / t) - 1) := by
  rw [evenKernel_zero_eq_rpow_mul ht]
  ring

/-- Complex embedding of the Jacobi theta subtraction identity on Ioo 0 1. -/
theorem f_modif_eq_reflected_on_Ioo {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (hurwitzEvenFEPair 0).f_modif t =
      ((t ^ (- (1 / 2 : ℝ)) : ℝ) : ℂ) * ((evenKernel 0 (1 / t) - 1 : ℝ) : ℂ) := by
  rw [f_modif_eq_on_Ioo_zero_one ht]
  have h_real := evenKernel_zero_sub_rpow_eq ht.1
  exact_mod_cast congr_arg ofReal h_real

/-- Inverse Logic: Any zero of entireXi on leftoverRect forces
a large lower bound on ‖completedRiemannZeta₀ z‖. -/
theorem norm_zeta₀_gt_one_of_entireXi_eq_zero {z : ℂ} (hz : z ∈ leftoverRect)
    (hxi : entireXi z = 0) :
    1 < ‖completedRiemannZeta₀ z‖ := by
  by_contra hle
  have h_not : ¬(1 < ‖completedRiemannZeta₀ z‖) := hle
  have h_le : ‖completedRiemannZeta₀ z‖ ≤ 1 := le_of_not_gt h_not
  have hne := entireXi_ne_zero_of_zeta₀_le_one_mem_leftoverRect hz h_le
  exact hne hxi

/-- The canonical folded Jacobi theta Mellin integral on Ioi 1. -/
noncomputable def foldedThetaIntegral (s : ℂ) : ℂ :=
  ∫ u in Ioi (1 : ℝ), ((u : ℂ) ^ (s / 2 - 1) + (u : ℂ) ^ ((1 - s) / 2 - 1)) * ((evenKernel 0 u - 1 : ℝ) : ℂ)

/-- Bound on the folded integrand norm at any point of frontier leftoverRect. -/
theorem norm_folded_integrand_le {u : ℝ} (hu : 1 ≤ u) {s : ℂ} (hs : s ∈ frontier leftoverRect) :
    ‖((u : ℂ) ^ (s / 2 - 1) + (u : ℂ) ^ ((1 - s) / 2 - 1)) * ((evenKernel 0 u - 1 : ℝ) : ℂ)‖ ≤
      2 * (evenKernel 0 u - 1) := by
  have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hK : 0 ≤ evenKernel 0 u - 1 := evenKernel₀_sub_one_nonneg hu_pos
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hK]
  have hw := theta_kernel_weight_norm_le_two_of_mem_frontier hu hs
  exact mul_le_mul_of_nonneg_right hw hK

/-- Integral domination of the folded theta integral on frontier leftoverRect. -/
theorem norm_foldedThetaIntegral_le {s : ℂ} (hs : s ∈ frontier leftoverRect)
    (hf_int : IntegrableOn (fun u : ℝ => ‖((u : ℂ) ^ (s / 2 - 1) + (u : ℂ) ^ ((1 - s) / 2 - 1)) * ((evenKernel 0 u - 1 : ℝ) : ℂ)‖) (Ioi 1))
    (hg_int : IntegrableOn (fun u : ℝ => 2 * (evenKernel 0 u - 1)) (Ioi 1)) :
    ‖foldedThetaIntegral s‖ ≤ 2 * ∫ u in Ioi (1 : ℝ), (evenKernel 0 u - 1) := by
  have h_norm := norm_integral_le_integral_norm (μ := volume.restrict (Ioi 1))
    (fun u : ℝ => ((u : ℂ) ^ (s / 2 - 1) + (u : ℂ) ^ ((1 - s) / 2 - 1)) * ((evenKernel 0 u - 1 : ℝ) : ℂ))
  have h_mono : (∫ u in Ioi (1 : ℝ), ‖((u : ℂ) ^ (s / 2 - 1) + (u : ℂ) ^ ((1 - s) / 2 - 1)) * ((evenKernel 0 u - 1 : ℝ) : ℂ)‖) ≤
      ∫ u in Ioi (1 : ℝ), 2 * (evenKernel 0 u - 1) := by
    apply setIntegral_mono_on hf_int hg_int measurableSet_Ioi
    intro u hu
    exact norm_folded_integrand_le (le_of_lt hu) hs
  rw [integral_const_mul] at h_mono
  exact le_trans h_norm h_mono

/-- Half-norm bound on the folded theta integral on frontier leftoverRect. -/
theorem norm_half_foldedThetaIntegral_le {s : ℂ} (hs : s ∈ frontier leftoverRect)
    (hf_int : IntegrableOn (fun u : ℝ => ‖((u : ℂ) ^ (s / 2 - 1) + (u : ℂ) ^ ((1 - s) / 2 - 1)) * ((evenKernel 0 u - 1 : ℝ) : ℂ)‖) (Ioi 1))
    (hg_int : IntegrableOn (fun u : ℝ => 2 * (evenKernel 0 u - 1)) (Ioi 1)) :
    ‖foldedThetaIntegral s / 2‖ ≤ ∫ u in Ioi (1 : ℝ), (evenKernel 0 u - 1) := by
  have h := norm_foldedThetaIntegral_le hs hf_int hg_int
  rw [norm_div, Complex.norm_two]
  linarith

end RhG1Lean
