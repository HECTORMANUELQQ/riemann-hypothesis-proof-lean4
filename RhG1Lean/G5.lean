/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under CC-BY 4.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.NumberTheory.LSeries.RiemannZeta
import RhG1Lean.Majorant
import RhG1Lean.Diameter
import RhG1Lean.Nonvanishing
import RhG1Lean.G4Match

/-!
# G5 · contar ceros *dentro* = un giro, no una lista

Mapa: N = (1/2πi) ∮ (ξ'/ξ)  (principio del argumento).
Un entero por contorno. **No** es γ=14, γ=21, γ=25, …

Pieza Lean de este paso: ξ es holomorfa en {Re s > 1}
(hipótesis del AP). N=0 sigue OPEN.

Otras lógicas: las rosas y Pick miran ceros ya hallados (muestra).
G5 no las usa como censo; si ξ=0 en la recta, es el mismo objeto.
-/

open Complex Real

namespace RhG1Lean

lemma differentiableAt_pi_cpow_neg_half {s : ℂ} :
    DifferentiableAt ℂ (fun z : ℂ => (π : ℂ) ^ (-z / 2)) s := by
  refine DifferentiableAt.const_cpow ?_ (Or.inl (ofReal_ne_zero.mpr pi_ne_zero))
  exact differentiableAt_id.neg.div_const 2

lemma differentiableAt_Gamma_half {s : ℂ} (hG : 0 < (s / 2).re) :
    DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z / 2)) s := by
  have hcomp : DifferentiableAt ℂ (fun z : ℂ => z / 2) s :=
    differentiableAt_id.div_const 2
  refine (Complex.differentiableAt_Gamma (s / 2) ?_).comp s hcomp
  intro m hm
  have hle : (s / 2).re ≤ 0 := by
    have := congrArg Complex.re hm
    have hneg : (-(m : ℂ)).re = - (m : ℝ) := by simp
    rw [this, hneg]
    exact neg_nonpos.mpr (Nat.cast_nonneg m)
  exact (not_le_of_gt hG) hle

lemma differentiableAt_prefactor {s : ℂ} :
    DifferentiableAt ℂ (fun z : ℂ => z * (z - 1) / 2) s := by
  simp_rw [div_eq_mul_inv]
  exact ((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul
    (differentiableAt_const _))

/-- ξ holomorfa si s ≠ 1 y Re(s/2) > 0 (cubre todo L_R, no solo Re s>1). -/
theorem differentiableAt_riemannXi_of {s : ℂ} (h1 : s ≠ 1) (hG : 0 < (s / 2).re) :
    DifferentiableAt ℂ riemannXi s := by
  unfold riemannXi
  refine (((differentiableAt_prefactor.mul differentiableAt_pi_cpow_neg_half).mul
        (differentiableAt_Gamma_half hG)).mul
      (differentiableAt_riemannZeta h1))

/-- ξ es holomorfa en Re s > 1 (hipótesis de G5 / AP). -/
theorem differentiableAt_riemannXi {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ riemannXi s :=
  differentiableAt_riemannXi_of (ne_one_of_one_lt_re hs) (re_half_pos_of_one_lt_re hs)

/-- ξ no es idénticamente 0: en s=2, Re=2>1 y G3. -/
theorem riemannXi_two_ne_zero : riemannXi 2 ≠ 0 :=
  riemannXi_ne_zero_of_one_lt_re (by norm_num : (1 : ℝ) < (2 : ℂ).re)

/-- G5 no afirma N=0. Afirma: el objeto del AP (f holomorfa, no ≡ 0) está listo
    en {Re s > 1}. El giro N=0 es OPEN. -/
theorem G5_hypotheses_on_re_gt_one {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ riemannXi s ∧ riemannXi s ≠ 0 :=
  ⟨differentiableAt_riemannXi hs, riemannXi_ne_zero_of_one_lt_re hs⟩

theorem isOpen_re_gt_one : IsOpen {s : ℂ | 1 < s.re} :=
  isOpen_lt continuous_const Complex.continuous_re

/-- En todo el diámetro L_R, ξ es holomorfa. -/
theorem differentiableAt_riemannXi_sOnDiameter (y : ℝ) :
    DifferentiableAt ℂ riemannXi (sOnDiameter y) :=
  differentiableAt_riemannXi_of (sOnDiameter_ne_one y) (re_half_pos_sOnDiameter y)

end RhG1Lean
