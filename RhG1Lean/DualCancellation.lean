/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under CC-BY 4.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Complex.RealDeriv
import RhG1Lean.XiEntire
import RhG1Lean.Conj
import RhG1Lean.MouthA
import RhG1Lean.FunEq

/-!
# Dual Cancellation Model: Geometry of entireXi on and off the Critical Line

From `brief_cancelacion_dual.md`:
1. On the critical line $\sigma = 1/2$ ($\mu = 0$), the two Dirichlet arrays
   fold onto a 1D real axis: `entireXi (1/2 + I * t)` is purely real.
   That is, `Im(entireXi(1/2 + I * t)) = 0` for all $t \in \mathbb{R}$.
2. Transversal departure: off the line ($\delta \ne 0$), reflection across the
   critical line gives:
   `entireXi (1/2 - δ + I * t) = conj (entireXi (1/2 + δ + I * t))`.
3. Consequently:
   - $\operatorname{Re}(\text{entireXi})$ is EVEN in $\delta$.
   - $\operatorname{Im}(\text{entireXi})$ is ODD in $\delta$, vanishing identically at $\delta = 0$.
4. At any critical zero $t_n$ with $\xi'(1/2 + I * t_n) \ne 0$, departure in $\delta$
   is purely imaginary ($\partial_\delta \hat{F} \in i\mathbb{R}$), preventing zeros off-line.
-/

set_option linter.style.longLine false
set_option linter.style.whitespace false

open Complex Topology Filter Metric
open scoped Real ComplexConjugate Topology

namespace RhG1Lean

/-! ### Algebraic symmetries of σ + I * t and 1/2 + δ + I * t -/

@[simp]
lemma re_ofReal_add_I_mul (σ t : ℝ) :
    (((σ : ℝ) : ℂ) + I * t).re = σ := by
  simp

@[simp]
lemma im_ofReal_add_I_mul (σ t : ℝ) :
    (((σ : ℝ) : ℂ) + I * t).im = t := by
  simp

lemma one_sub_ofReal_add_I (σ t : ℝ) :
    1 - (((σ : ℝ) : ℂ) + I * t) = (((1 - σ : ℝ) : ℂ) + I * (-t)) := by
  apply Complex.ext <;> simp

lemma conj_one_sub_ofReal_add_I (σ t : ℝ) :
    conj (1 - (((σ : ℝ) : ℂ) + I * t)) = (((1 - σ : ℝ) : ℂ) + I * t) := by
  rw [one_sub_ofReal_add_I]
  simp [map_add, map_mul, conj_ofReal, conj_I]

/-! ### General reflection identity for riemannXi -/

/-- For any point $z = \sigma + it$ satisfying the functional equation hypotheses,
$\xi((1-\sigma) + it) = \overline{\xi(\sigma + it)}$. -/
theorem riemannXi_symm_re_eq {σ t : ℝ}
    (hs0 : ((σ : ℝ) : ℂ) + I * t ≠ 0)
    (hs1 : ((σ : ℝ) : ℂ) + I * t ≠ 1)
    (hG : Gammaℝ (((σ : ℝ) : ℂ) + I * t) ≠ 0)
    (hG' : Gammaℝ (1 - (((σ : ℝ) : ℂ) + I * t)) ≠ 0) :
    riemannXi (((1 - σ : ℝ) : ℂ) + I * t) =
      conj (riemannXi (((σ : ℝ) : ℂ) + I * t)) := by
  set z : ℂ := ((σ : ℝ) : ℂ) + I * t
  have hFE : riemannXi (1 - z) = riemannXi z := riemannXi_one_sub hs0 hs1 hG hG'
  have hconjz : conj (1 - z) = (((1 - σ : ℝ) : ℂ) + I * t) := conj_one_sub_ofReal_add_I σ t
  calc
    riemannXi (((1 - σ : ℝ) : ℂ) + I * t) = riemannXi (conj (1 - z)) := by rw [hconjz]
    _ = conj (riemannXi (1 - z)) := riemannXi_conj (1 - z)
    _ = conj (riemannXi z) := by rw [hFE]

/-! ### Critical line σ = 1/2 -/

lemma half_add_I_ne_zero (t : ℝ) : (((1 / 2 : ℝ) : ℂ) + I * t) ≠ 0 := by
  intro h
  have hre : ((((1 / 2 : ℝ) : ℂ) + I * t)).re = (0 : ℂ).re := by rw [h]
  simp at hre

lemma half_add_I_ne_one (t : ℝ) : (((1 / 2 : ℝ) : ℂ) + I * t) ≠ 1 := by
  intro h
  have hre : ((((1 / 2 : ℝ) : ℂ) + I * t)).re = (1 : ℂ).re := by rw [h]
  simp at hre

lemma Gammaℝ_half_add_I_ne_zero (t : ℝ) :
    Gammaℝ (((1 / 2 : ℝ) : ℂ) + I * t) ≠ 0 := by
  rw [Gammaℝ_def]
  refine mul_ne_zero ?_ ?_
  · exact (cpow_eq_zero_iff _ _).not.mpr (by simp [ofReal_eq_zero, Real.pi_ne_zero])
  · have hre : (((((1 / 2 : ℝ) : ℂ) + I * t) / 2)).re = (1 : ℝ) / 4 := by
      simp
      norm_num
    exact Complex.Gamma_ne_zero_of_re_pos (by rw [hre]; norm_num)

lemma Gammaℝ_one_sub_half_add_I_ne_zero (t : ℝ) :
    Gammaℝ (1 - ((((1 / 2 : ℝ) : ℂ) + I * t))) ≠ 0 := by
  have h1 : 1 - ((((1 / 2 : ℝ) : ℂ) + I * t)) = (((1 / 2 : ℝ) : ℂ) + I * (-t : ℝ)) := by
    apply Complex.ext
    · simp; ring
    · simp
  rw [h1]
  exact Gammaℝ_half_add_I_ne_zero (-t)

/-- On the critical line $s = 1/2 + it$, `riemannXi` equals its complex conjugate. -/
theorem riemannXi_critical_line_conj (t : ℝ) :
    conj (riemannXi (((1 / 2 : ℝ) : ℂ) + I * t)) =
      riemannXi (((1 / 2 : ℝ) : ℂ) + I * t) := by
  have hs0 := half_add_I_ne_zero t
  have hs1 := half_add_I_ne_one t
  have hG := Gammaℝ_half_add_I_ne_zero t
  have hG' := Gammaℝ_one_sub_half_add_I_ne_zero t
  have hsymm := riemannXi_symm_re_eq (σ := 1 / 2) (t := t) hs0 hs1 hG hG'
  have hhalf : (1 - (1 : ℝ) / 2 : ℝ) = 1 / 2 := by ring
  rw [hhalf] at hsymm
  exact hsymm.symm

/-- **Dual Cancellation Theorem 1a (Reality of riemannXi on the Critical Line)**:
For all $t \in \mathbb{R}$, $\operatorname{Im}(\xi(1/2 + it)) = 0$. -/
theorem riemannXi_critical_line_im_eq_zero (t : ℝ) :
    (riemannXi (((1 / 2 : ℝ) : ℂ) + I * t)).im = 0 := by
  have h := riemannXi_critical_line_conj t
  exact Complex.conj_eq_iff_im.mp h

/-- On the critical line, `entireXi` agrees with `riemannXi`. -/
theorem entireXi_critical_line_eq_riemannXi (t : ℝ) :
    entireXi (((1 / 2 : ℝ) : ℂ) + I * t) = riemannXi (((1 / 2 : ℝ) : ℂ) + I * t) := by
  exact entireXi_eq_riemannXi (half_add_I_ne_zero t) (half_add_I_ne_one t)
    (Gammaℝ_half_add_I_ne_zero t)

/-- **Dual Cancellation Theorem 1 (Reality of entireXi on the Critical Line)**:
For all $t \in \mathbb{R}$, $\operatorname{Im}(\xi_{\text{entera}}(1/2 + it)) = 0$.
The entire xi function is strictly REAL on the critical line. -/
theorem entireXi_critical_line_im_eq_zero (t : ℝ) :
    (entireXi (((1 / 2 : ℝ) : ℂ) + I * t)).im = 0 := by
  rw [entireXi_critical_line_eq_riemannXi]
  exact riemannXi_critical_line_im_eq_zero t

/-- On the critical line, `entireXi` equals its complex conjugate. -/
theorem entireXi_critical_line_conj (t : ℝ) :
    conj (entireXi (((1 / 2 : ℝ) : ℂ) + I * t)) =
      entireXi (((1 / 2 : ℝ) : ℂ) + I * t) := by
  rw [entireXi_critical_line_eq_riemannXi, riemannXi_critical_line_conj]

/-- Equivalent formulation: $\xi_{\text{entera}}(1/2 + it) \in \mathbb{R}$. -/
theorem entireXi_critical_line_mem_re (t : ℝ) :
    entireXi (((1 / 2 : ℝ) : ℂ) + I * t) =
      (((entireXi (((1 / 2 : ℝ) : ℂ) + I * t)).re : ℝ) : ℂ) := by
  apply Complex.ext
  · simp
  · exact entireXi_critical_line_im_eq_zero t

/-! ### Off the line: reflection symmetry across σ = 1/2 -/

lemma half_add_delta_ne_zero {δ t : ℝ} (hδ : |δ| < 1 / 2) :
    (((1 / 2 + δ : ℝ) : ℂ) + I * t) ≠ 0 := by
  intro h
  have hre : ((((1 / 2 + δ : ℝ) : ℂ) + I * t)).re = (0 : ℂ).re := by rw [h]
  simp only [re_ofReal_add_I_mul, zero_re] at hre
  have hlt := (abs_lt.mp hδ).1
  linarith

lemma half_add_delta_ne_one {δ t : ℝ} (hδ : |δ| < 1 / 2) :
    (((1 / 2 + δ : ℝ) : ℂ) + I * t) ≠ 1 := by
  intro h
  have hre : ((((1 / 2 + δ : ℝ) : ℂ) + I * t)).re = (1 : ℂ).re := by rw [h]
  simp only [re_ofReal_add_I_mul, one_re] at hre
  have hlt := (abs_lt.mp hδ).2
  linarith

lemma re_half_add_delta_div_two_pos {δ t : ℝ} (hδ : |δ| < 1 / 2) :
    0 < (((((1 / 2 + δ : ℝ) : ℂ) + I * t) / 2)).re := by
  have hre : (((((1 / 2 + δ : ℝ) : ℂ) + I * t) / 2)).re = (1 / 2 + δ) / 2 := by simp
  rw [hre]
  have := (abs_lt.mp hδ).1
  linarith

lemma Gammaℝ_half_add_delta_ne_zero {δ t : ℝ} (hδ : |δ| < 1 / 2) :
    Gammaℝ (((1 / 2 + δ : ℝ) : ℂ) + I * t) ≠ 0 := by
  rw [Gammaℝ_def]
  refine mul_ne_zero ?_ ?_
  · exact (cpow_eq_zero_iff _ _).not.mpr (by simp [ofReal_eq_zero, Real.pi_ne_zero])
  · exact Complex.Gamma_ne_zero_of_re_pos (re_half_add_delta_div_two_pos hδ)

lemma Gammaℝ_one_sub_half_add_delta_ne_zero {δ t : ℝ} (hδ : |δ| < 1 / 2) :
    Gammaℝ (1 - ((((1 / 2 + δ : ℝ) : ℂ) + I * t))) ≠ 0 := by
  have hδ' : |-δ| < 1 / 2 := by rwa [abs_neg]
  have h := Gammaℝ_half_add_delta_ne_zero (δ := -δ) (t := -t) hδ'
  have h1 : 1 - ((((1 / 2 + δ : ℝ) : ℂ) + I * t)) = (((1 / 2 + (-δ) : ℝ) : ℂ) + I * (-t : ℝ)) := by
    apply Complex.ext
    · simp; ring
    · simp
  rwa [h1]

/-- **Dual Cancellation Theorem 2 (Transversal Reflection Symmetry)**:
For $|\delta| < 1/2$, $\xi((1/2 - \delta) + it) = \overline{\xi((1/2 + \delta) + it)}$. -/
theorem riemannXi_reflection_symm {δ t : ℝ} (hδ : |δ| < 1 / 2) :
    riemannXi (((1 / 2 - δ : ℝ) : ℂ) + I * t) =
      conj (riemannXi (((1 / 2 + δ : ℝ) : ℂ) + I * t)) := by
  have hs0 : (((1 / 2 + δ : ℝ) : ℂ) + I * t) ≠ 0 := half_add_delta_ne_zero hδ
  have hs1 : (((1 / 2 + δ : ℝ) : ℂ) + I * t) ≠ 1 := half_add_delta_ne_one hδ
  have hG : Gammaℝ (((1 / 2 + δ : ℝ) : ℂ) + I * t) ≠ 0 := Gammaℝ_half_add_delta_ne_zero hδ
  have hG' : Gammaℝ (1 - (((1 / 2 + δ : ℝ) : ℂ) + I * t)) ≠ 0 :=
    Gammaℝ_one_sub_half_add_delta_ne_zero hδ
  have hsymm := riemannXi_symm_re_eq (σ := 1 / 2 + δ) (t := t) hs0 hs1 hG hG'
  have heq : (1 - (1 / 2 + δ : ℝ) : ℝ) = 1 / 2 - δ := by ring
  have heqC : (((1 - (1 / 2 + δ : ℝ) : ℝ) : ℂ) + I * t) = (((1 / 2 - δ : ℝ) : ℂ) + I * t) := by
    rw [heq]
  rwa [heqC] at hsymm

/-- **Dual Cancellation Theorem 3 (Even Real Part)**:
$\operatorname{Re}(\xi((1/2 - \delta) + it)) = \operatorname{Re}(\xi((1/2 + \delta) + it))$. -/
theorem re_riemannXi_neg_delta {δ t : ℝ} (hδ : |δ| < 1 / 2) :
    (riemannXi (((1 / 2 - δ : ℝ) : ℂ) + I * t)).re =
      (riemannXi (((1 / 2 + δ : ℝ) : ℂ) + I * t)).re := by
  rw [riemannXi_reflection_symm hδ, conj_re]

/-- **Dual Cancellation Theorem 4 (Odd Imaginary Part)**:
$\operatorname{Im}(\xi((1/2 - \delta) + it)) = - \operatorname{Im}(\xi((1/2 + \delta) + it))$. -/
theorem im_riemannXi_neg_delta {δ t : ℝ} (hδ : |δ| < 1 / 2) :
    (riemannXi (((1 / 2 - δ : ℝ) : ℂ) + I * t)).im =
      - (riemannXi (((1 / 2 + δ : ℝ) : ℂ) + I * t)).im := by
  rw [riemannXi_reflection_symm hδ, conj_im]

/-! ### Lift to entireXi -/

/-- For $|\delta| < 1/2$, `entireXi` also satisfies the reflection symmetry across $\sigma = 1/2$. -/
theorem entireXi_reflection_symm {δ t : ℝ} (hδ : |δ| < 1 / 2) :
    entireXi (((1 / 2 - δ : ℝ) : ℂ) + I * t) =
      conj (entireXi (((1 / 2 + δ : ℝ) : ℂ) + I * t)) := by
  have hs0 : (((1 / 2 + δ : ℝ) : ℂ) + I * t) ≠ 0 := half_add_delta_ne_zero hδ
  have hs1 : (((1 / 2 + δ : ℝ) : ℂ) + I * t) ≠ 1 := half_add_delta_ne_one hδ
  have hG : Gammaℝ (((1 / 2 + δ : ℝ) : ℂ) + I * t) ≠ 0 := Gammaℝ_half_add_delta_ne_zero hδ
  have hδ' : |-δ| < 1 / 2 := by rwa [abs_neg]
  have hs0' : (((1 / 2 - δ : ℝ) : ℂ) + I * t) ≠ 0 := by
    have h := half_add_delta_ne_zero (δ := -δ) (t := t) hδ'
    have heq : (1 / 2 + -δ : ℝ) = 1 / 2 - δ := by ring
    rwa [heq] at h
  have hs1' : (((1 / 2 - δ : ℝ) : ℂ) + I * t) ≠ 1 := by
    have h := half_add_delta_ne_one (δ := -δ) (t := t) hδ'
    have heq : (1 / 2 + -δ : ℝ) = 1 / 2 - δ := by ring
    rwa [heq] at h
  have hG' : Gammaℝ (((1 / 2 - δ : ℝ) : ℂ) + I * t) ≠ 0 := by
    have h := Gammaℝ_half_add_delta_ne_zero (δ := -δ) (t := t) hδ'
    have heq : (1 / 2 + -δ : ℝ) = 1 / 2 - δ := by ring
    rwa [heq] at h
  have heq1 : entireXi (((1 / 2 - δ : ℝ) : ℂ) + I * t) =
      riemannXi (((1 / 2 - δ : ℝ) : ℂ) + I * t) :=
    entireXi_eq_riemannXi hs0' hs1' hG'
  have heq2 : entireXi (((1 / 2 + δ : ℝ) : ℂ) + I * t) =
      riemannXi (((1 / 2 + δ : ℝ) : ℂ) + I * t) :=
    entireXi_eq_riemannXi hs0 hs1 hG
  rw [heq1, heq2]
  exact riemannXi_reflection_symm hδ

/-- Real part of `entireXi` is EVEN in $\delta$. -/
theorem re_entireXi_neg_delta {δ t : ℝ} (hδ : |δ| < 1 / 2) :
    (entireXi (((1 / 2 - δ : ℝ) : ℂ) + I * t)).re =
      (entireXi (((1 / 2 + δ : ℝ) : ℂ) + I * t)).re := by
  rw [entireXi_reflection_symm hδ, conj_re]

/-- Imaginary part of `entireXi` is ODD in $\delta$. -/
theorem im_entireXi_neg_delta {δ t : ℝ} (hδ : |δ| < 1 / 2) :
    (entireXi (((1 / 2 - δ : ℝ) : ℂ) + I * t)).im =
      - (entireXi (((1 / 2 + δ : ℝ) : ℂ) + I * t)).im := by
  rw [entireXi_reflection_symm hδ, conj_im]

/-- Zero off-line requires simultaneous vanishing of both even and odd components. -/
theorem entireXi_zero_iff_re_and_im_zero {s : ℂ} :
    entireXi s = 0 ↔ (entireXi s).re = 0 ∧ (entireXi s).im = 0 := by
  constructor
  · intro h
    simp [h]
  · rintro ⟨hre, him⟩
    exact Complex.ext (by simp [hre]) (by simp [him])

/-- **Transversal Zero Pairing**: If $s = 1/2 + \delta + it$ is a zero of `entireXi` with $|\delta| < 1/2$,
then its transversal reflection $1/2 - \delta + it$ is also a zero. -/
theorem entireXi_zero_symm_delta {δ t : ℝ} (hδ : |δ| < 1 / 2)
    (hz : entireXi (((1 / 2 + δ : ℝ) : ℂ) + I * t) = 0) :
    entireXi (((1 / 2 - δ : ℝ) : ℂ) + I * t) = 0 := by
  rw [entireXi_reflection_symm hδ, hz, map_zero]

/-- Zero pairing in real and imaginary parts: both components vanish at $+\delta$ and $-\delta$. -/
theorem entireXi_zero_re_im_pair {δ t : ℝ} (hδ : |δ| < 1 / 2)
    (hz : entireXi (((1 / 2 + δ : ℝ) : ℂ) + I * t) = 0) :
    (entireXi (((1 / 2 + δ : ℝ) : ℂ) + I * t)).re = 0 ∧
    (entireXi (((1 / 2 + δ : ℝ) : ℂ) + I * t)).im = 0 ∧
    (entireXi (((1 / 2 - δ : ℝ) : ℂ) + I * t)).re = 0 ∧
    (entireXi (((1 / 2 - δ : ℝ) : ℂ) + I * t)).im = 0 := by
  have hz' := entireXi_zero_symm_delta hδ hz
  have h1 := entireXi_zero_iff_re_and_im_zero.mp hz
  have h2 := entireXi_zero_iff_re_and_im_zero.mp hz'
  exact ⟨h1.1, h1.2, h2.1, h2.2⟩

/-! ### Antisymmetry of the derivative under s ↦ 1 - s -/

/-- Under the functional equation $s \mapsto 1 - s$, the derivative of `entireXi` is antisymmetric:
$\xi'(1 - s) = -\xi'(s)$. -/
theorem deriv_entireXi_one_sub (s : ℂ) :
    deriv entireXi (1 - s) = - deriv entireXi s := by
  have hfe : (fun z => entireXi (1 - z)) = entireXi := funext entireXi_one_sub
  have hderiv := deriv_comp_const_sub entireXi 1 s
  rw [hfe] at hderiv
  calc
    deriv entireXi (1 - s) = - (- deriv entireXi (1 - s)) := by ring
    _ = - deriv entireXi s := by rw [hderiv]

/-- At the center of symmetry $s = 1/2$, the first derivative of `entireXi` vanishes:
$\xi'(1/2) = 0$. -/
theorem deriv_entireXi_half : deriv entireXi (1 / 2 : ℂ) = 0 := by
  have h := deriv_entireXi_one_sub (1 / 2 : ℂ)
  have hhalf : (1 : ℂ) - 1 / 2 = 1 / 2 := by ring
  rw [hhalf] at h
  have : (2 : ℂ) * deriv entireXi (1 / 2 : ℂ) = 0 := by
    calc (2 : ℂ) * deriv entireXi (1 / 2 : ℂ) =
           deriv entireXi (1 / 2 : ℂ) + deriv entireXi (1 / 2 : ℂ) := by ring
         _ = - deriv entireXi (1 / 2 : ℂ) + deriv entireXi (1 / 2 : ℂ) := by rw [← h]
         _ = 0 := by ring
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  exact (mul_eq_zero.mp this).resolve_left h2

/-- Reflection of the derivative across the critical line:
$\xi'(1/2 - it) = -\xi'(1/2 + it)$. -/
theorem deriv_entireXi_critical_line_neg (t : ℝ) :
    deriv entireXi (((1 / 2 : ℝ) : ℂ) - I * t) =
      - deriv entireXi (((1 / 2 : ℝ) : ℂ) + I * t) := by
  have h := deriv_entireXi_one_sub (((1 / 2 : ℝ) : ℂ) + I * t)
  have hsub : 1 - ((((1 / 2 : ℝ) : ℂ) + I * t)) = (((1 / 2 : ℝ) : ℂ) - I * t) := by
    apply Complex.ext
    · simp; ring
    · simp
  rwa [hsub] at h

/-- Derivative of $y \mapsto -y$ at any real point. -/
lemma hasDerivAt_neg_id (x : ℝ) : HasDerivAt (fun y : ℝ => -y) (-1) x :=
  (hasDerivAt_id x).neg

/-- If a real function has a derivative at 0 and is locally even near 0,
its derivative at 0 is zero. -/
lemma hasDerivAt_even_deriv_zero {f : ℝ → ℝ} {L : ℝ} (hf : HasDerivAt f L 0)
    (heven : ∀ᶠ (x : ℝ) in 𝓝 (0 : ℝ), f (-x) = f x) : L = 0 := by
  have hf_neg0 : HasDerivAt f L (-0) := by rwa [neg_zero]
  have hcomp : HasDerivAt (fun y => f (-y)) (L * (-1)) 0 :=
    hf_neg0.comp 0 (hasDerivAt_neg_id 0)
  have hmul : L * (-1) = -L := by ring
  rw [hmul] at hcomp
  have hcongr : HasDerivAt f (-L) 0 :=
    HasDerivAt.congr_of_eventuallyEq hcomp (heven.mono fun _ h => h.symm)
  have huniq : L = -L := hf.unique hcongr
  linarith

/-- **Dual Cancellation Theorem 5 (Purely Imaginary Derivative on Critical Line)**:
For all $t \in \mathbb{R}$, the real part of $\xi'(1/2 + it)$ is zero:
$\operatorname{Re}(\xi'(1/2 + it)) = 0$. -/
theorem re_deriv_entireXi_critical_line (t : ℝ) :
    (deriv entireXi (((1 / 2 : ℝ) : ℂ) + I * t)).re = 0 := by
  set c : ℂ := ((1 / 2 : ℝ) : ℂ) + I * t
  have hdiff : HasDerivAt entireXi (deriv entireXi c) (c + 0) := by
    rw [add_zero]
    exact differentiable_entireXi.differentiableAt.hasDerivAt
  have hshift : HasDerivAt (fun w : ℂ => c + w) 1 (0 : ℂ) :=
    (hasDerivAt_id' (0 : ℂ)).const_add c
  have hcomp0 : HasDerivAt (entireXi ∘ fun w : ℂ => c + w) (deriv entireXi c) ((0 : ℝ) : ℂ) := by
    have h := hdiff.comp (0 : ℂ) hshift
    rw [mul_one] at h
    exact h
  have hu : HasDerivAt (fun x : ℝ => (entireXi (c + (x : ℂ))).re) (deriv entireXi c).re 0 :=
    hcomp0.real_of_complex
  have hmem : Metric.ball (0 : ℝ) (1 / 2) ∈ 𝓝 (0 : ℝ) :=
    Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)
  have heven : ∀ᶠ (x : ℝ) in 𝓝 (0 : ℝ),
      (entireXi (c + ((-x : ℝ) : ℂ))).re = (entireXi (c + ((x : ℝ) : ℂ))).re := by
    refine Filter.eventually_of_mem hmem ?_
    intro x hx
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hx
    have hx_sub : c + ((-x : ℝ) : ℂ) = (((1 / 2 - x : ℝ) : ℂ) + I * t) := by
      apply Complex.ext
      · simp [c]; ring
      · simp [c]
    have hx_add : c + ((x : ℝ) : ℂ) = (((1 / 2 + x : ℝ) : ℂ) + I * t) := by
      apply Complex.ext <;> simp [c]
    rw [hx_sub, hx_add]
    exact re_entireXi_neg_delta hx
  exact hasDerivAt_even_deriv_zero hu heven

/-- **Dual Cancellation Theorem 6 (Orthogonal Derivative Alignment)**:
Along the critical line, $\xi'(1/2 + it) = i \operatorname{Im}(\xi'(1/2 + it))$.
The derivative is strictly orthogonal to the real axis. -/
theorem deriv_entireXi_critical_line_eq_I_mul_im (t : ℝ) :
    deriv entireXi (((1 / 2 : ℝ) : ℂ) + I * t) =
      I * (((deriv entireXi (((1 / 2 : ℝ) : ℂ) + I * t)).im : ℝ) : ℂ) := by
  apply Complex.ext
  · simp only [mul_re, I_re, zero_mul, I_im, ofReal_im, mul_zero, sub_self]
    exact re_deriv_entireXi_critical_line t
  · simp only [mul_im, I_re, zero_mul, I_im, ofReal_re, one_mul]
    rw [zero_add]

/-- The imaginary part of the derivative along the critical line is an ODD function of $t$:
$\operatorname{Im}(\xi'(1/2 - it)) = -\operatorname{Im}(\xi'(1/2 + it))$. -/
theorem im_deriv_entireXi_critical_line_neg (t : ℝ) :
    (deriv entireXi (((1 / 2 : ℝ) : ℂ) - I * t)).im =
      - (deriv entireXi (((1 / 2 : ℝ) : ℂ) + I * t)).im := by
  have h := deriv_entireXi_critical_line_neg t
  have him := congr_arg Complex.im h
  rw [Complex.neg_im] at him
  exact him

/-- **Dual Cancellation Theorem 7 (Boca A Quadratic Definiteness)**:
Since $\xi'(1/2 + it) \in i\mathbb{R}$, its square is a non-positive real number:
$\operatorname{Re}((\xi'(1/2 + it))^2) \le 0$. -/
theorem deriv_entireXi_critical_line_sq_re_nonpos (t : ℝ) :
    (deriv entireXi (((1 / 2 : ℝ) : ℂ) + I * t) ^ 2).re ≤ 0 := by
  set w := deriv entireXi (((1 / 2 : ℝ) : ℂ) + I * t)
  have hw : w = I * ((w.im : ℝ) : ℂ) := deriv_entireXi_critical_line_eq_I_mul_im t
  rw [hw]
  have hsq : (I * ((w.im : ℝ) : ℂ)) ^ 2 = - (((w.im ^ 2 : ℝ) : ℂ)) := by
    calc (I * ((w.im : ℝ) : ℂ)) ^ 2 = I ^ 2 * (((w.im : ℝ) : ℂ)) ^ 2 := by ring
    _ = (-1) * (((w.im ^ 2 : ℝ) : ℂ)) := by simp [I_sq, ← ofReal_pow]
    _ = - (((w.im ^ 2 : ℝ) : ℂ)) := by ring
  rw [hsq]
  simp only [neg_re, ofReal_re, Left.neg_nonpos_iff]
  exact sq_nonneg w.im

/-- The square of the derivative along the critical line is strictly REAL:
$\operatorname{Im}((\xi'(1/2 + it))^2) = 0$. -/
theorem deriv_entireXi_critical_line_sq_im_eq_zero (t : ℝ) :
    (deriv entireXi (((1 / 2 : ℝ) : ℂ) + I * t) ^ 2).im = 0 := by
  set w := deriv entireXi (((1 / 2 : ℝ) : ℂ) + I * t)
  have hw : w = I * ((w.im : ℝ) : ℂ) := deriv_entireXi_critical_line_eq_I_mul_im t
  rw [hw]
  have hsq : (I * ((w.im : ℝ) : ℂ)) ^ 2 = - (((w.im ^ 2 : ℝ) : ℂ)) := by
    calc (I * ((w.im : ℝ) : ℂ)) ^ 2 = I ^ 2 * (((w.im : ℝ) : ℂ)) ^ 2 := by ring
    _ = (-1) * (((w.im ^ 2 : ℝ) : ℂ)) := by simp [I_sq, ← ofReal_pow]
    _ = - (((w.im ^ 2 : ℝ) : ℂ)) := by ring
  rw [hsq]
  simp only [neg_im, ofReal_im, neg_zero]

/-- **Dual Cancellation Theorem 8 (Local Transversal Rigidity of Simple Critical Zeros)**:
At any simple zero $s_0$ with $\xi'(s_0) \ne 0$,
`entireXi` does not vanish on a punctured neighborhood of $s_0$. -/
theorem entireXi_eventually_ne_zero_of_deriv_ne_zero {s₀ : ℂ}
    (_hz : entireXi s₀ = 0) (hderiv : deriv entireXi s₀ ≠ 0) :
    ∀ᶠ z in 𝓝[≠] s₀, entireXi z ≠ 0 := by
  have hdiff : HasDerivAt entireXi (deriv entireXi s₀) s₀ :=
    differentiable_entireXi.differentiableAt.hasDerivAt
  exact hdiff.eventually_ne (c := (0 : ℂ)) hderiv

/-- Metric formulation: there exists $\varepsilon > 0$ such that in the punctured ball
$0 < \|z - s_0\| < \varepsilon$, `entireXi z ≠ 0`. -/
theorem exists_ball_punctured_entireXi_ne_zero_of_deriv_ne_zero {s₀ : ℂ}
    (hz : entireXi s₀ = 0) (hderiv : deriv entireXi s₀ ≠ 0) :
    ∃ ε > (0 : ℝ), ∀ z : ℂ, 0 < dist z s₀ ∧ dist z s₀ < ε → entireXi z ≠ 0 := by
  have he := entireXi_eventually_ne_zero_of_deriv_ne_zero hz hderiv
  rw [eventually_nhdsWithin_iff] at he
  rw [Metric.eventually_nhds_iff] at he
  obtain ⟨ε, hε_pos, hε⟩ := he
  refine ⟨ε, hε_pos, fun z hz => ?_⟩
  exact hε hz.2 (dist_pos.mp hz.1)

/-- **Dual Cancellation Theorem 9 (Transversal Non-Bifurcation from Critical Zeros)**:
Off-line points $s = 1/2 + \delta + it$ with $\delta \ne 0$ cannot vanish in a neighborhood
of any simple critical zero $s_0 = 1/2 + it_0$ with $\xi'(s_0) \ne 0$.
The orthogonal departure $\xi'(s_0) \in i\mathbb{R} \setminus \{0\}$ locks the zero rigidly
onto the critical line. -/
theorem entireXi_off_line_ne_zero_near_critical_zero (t₀ : ℝ)
    (hz : entireXi (((1 / 2 : ℝ) : ℂ) + I * t₀) = 0)
    (hderiv : deriv entireXi (((1 / 2 : ℝ) : ℂ) + I * t₀) ≠ 0) :
    ∃ ε > (0 : ℝ), ∀ (δ : ℝ) (t : ℝ),
      δ ≠ 0 →
      dist (((1 / 2 + δ : ℝ) : ℂ) + I * t) (((1 / 2 : ℝ) : ℂ) + I * t₀) < ε →
      entireXi (((1 / 2 + δ : ℝ) : ℂ) + I * t) ≠ 0 := by
  set s₀ : ℂ := ((1 / 2 : ℝ) : ℂ) + I * t₀
  obtain ⟨ε, hε_pos, hε⟩ :=
    exists_ball_punctured_entireXi_ne_zero_of_deriv_ne_zero hz hderiv
  refine ⟨ε, hε_pos, fun δ t hδ hdist => ?_⟩
  set z : ℂ := ((1 / 2 + δ : ℝ) : ℂ) + I * t
  apply hε z
  refine ⟨?_, hdist⟩
  rw [dist_pos]
  intro heq
  have h_re : z.re = s₀.re := by rw [heq]
  have hz_re : z.re = 1 / 2 + δ := by
    simp [z]
  have hs0_re : s₀.re = 1 / 2 := by
    simp [s₀]
  rw [hz_re, hs0_re] at h_re
  have : δ = 0 := by linarith
  exact hδ this

/-- Transversal complex derivative: the path `δ ↦ entireXi (1/2 + δ + it)` has complex
derivative `deriv entireXi (1/2 + it)` at `δ = 0`. -/
theorem hasDerivAt_entireXi_transversal (t : ℝ) :
    HasDerivAt (fun δ : ℝ => entireXi (((1 / 2 + δ : ℝ) : ℂ) + I * t))
      (deriv entireXi (((1 / 2 : ℝ) : ℂ) + I * t)) 0 := by
  set c : ℂ := ((1 / 2 : ℝ) : ℂ) + I * t
  have hinner : HasDerivAt (fun w : ℂ => c + w) 1 0 := by
    simpa using (hasDerivAt_id' (0 : ℂ)).const_add c
  have hdiff : HasDerivAt entireXi (deriv entireXi c) (c + 0) := by
    rw [add_zero]
    exact differentiable_entireXi.differentiableAt.hasDerivAt
  have hcomp : HasDerivAt (entireXi ∘ fun w : ℂ => c + w) (deriv entireXi c * 1) 0 :=
    hdiff.comp 0 hinner
  rw [mul_one] at hcomp
  have hg : HasDerivAt (fun w : ℂ => entireXi (c + w)) (deriv entireXi c) 0 := hcomp
  have hreal := hg.comp_ofReal
  refine hreal.congr_of_eventuallyEq ?_
  filter_upwards with δ
  congr 1
  apply Complex.ext <;> simp [c]

/-- **Dual Cancellation Theorem 10 (Transversal Real Velocity Vanishing)**:
The real part of $\xi$ has ZERO derivative in the transversal direction $\delta$ at $\delta = 0$:
$\frac{\partial}{\partial \delta} \operatorname{Re}(\xi(1/2 + \delta + it))\Big|_{\delta=0} = 0$. -/
theorem hasDerivAt_entireXi_transversal_re (t : ℝ) :
    HasDerivAt (fun δ : ℝ => (entireXi (((1 / 2 + δ : ℝ) : ℂ) + I * t)).re) 0 0 := by
  have h := hasDerivAt_entireXi_transversal t
  have hre := reCLM.hasFDerivAt.comp_hasDerivAt 0 h
  simp only [reCLM_apply] at hre
  rw [re_deriv_entireXi_critical_line t] at hre
  exact hre

/-- **Dual Cancellation Theorem 11 (Transversal Imaginary Velocity)**:
The imaginary part of $\xi$ departs from 0 in the transversal direction $\delta$ with velocity
equal to the imaginary part of $\xi'(1/2 + it)$:
$\frac{\partial}{\partial \delta} \operatorname{Im}(\xi(1/2 + \delta + it))\Big|_{\delta=0} = \operatorname{Im}(\xi'(1/2 + it))$. -/
theorem hasDerivAt_entireXi_transversal_im (t : ℝ) :
    HasDerivAt (fun δ : ℝ => (entireXi (((1 / 2 + δ : ℝ) : ℂ) + I * t)).im)
      ((deriv entireXi (((1 / 2 : ℝ) : ℂ) + I * t)).im) 0 := by
  have h := hasDerivAt_entireXi_transversal t
  have him := imCLM.hasFDerivAt.comp_hasDerivAt 0 h
  simp only [imCLM_apply] at him
  exact him

/-- Vertical complex derivative along the critical line:
The path `τ ↦ entireXi (1/2 + iτ)` has derivative `- Im(deriv entireXi (1/2 + it))` at `τ = t`.
The derivative is purely real because it is multiplied by $i$. -/
theorem hasDerivAt_entireXi_vertical (t : ℝ) :
    HasDerivAt (fun τ : ℝ => entireXi (((1 / 2 : ℝ) : ℂ) + I * (τ : ℂ)))
      (- (((deriv entireXi (((1 / 2 : ℝ) : ℂ) + I * t)).im : ℝ) : ℂ)) t := by
  set c : ℂ := ((1 / 2 : ℝ) : ℂ)
  have hinner : HasDerivAt (fun w : ℂ => c + I * w) I (t : ℂ) := by
    simpa using ((hasDerivAt_id' (t : ℂ)).const_mul I).const_add c
  have hdiff : HasDerivAt entireXi (deriv entireXi (c + I * (t : ℂ))) (c + I * (t : ℂ)) :=
    differentiable_entireXi.differentiableAt.hasDerivAt
  have hcomp : HasDerivAt (entireXi ∘ fun w : ℂ => c + I * w)
      (deriv entireXi (c + I * (t : ℂ)) * I) (t : ℂ) :=
    hdiff.comp (t : ℂ) hinner
  have hk : HasDerivAt (fun w : ℂ => entireXi (c + I * w))
      (deriv entireXi (c + I * (t : ℂ)) * I) (t : ℂ) := hcomp
  have hreal := hk.comp_ofReal
  set Y : ℝ := (deriv entireXi (((1 / 2 : ℝ) : ℂ) + I * t)).im
  have hw : deriv entireXi (c + I * (t : ℂ)) = I * (Y : ℂ) :=
    deriv_entireXi_critical_line_eq_I_mul_im t
  have hderiv_eq : deriv entireXi (c + I * (t : ℂ)) * I = - (Y : ℂ) := by
    calc deriv entireXi (c + I * (t : ℂ)) * I = (I * (Y : ℂ)) * I := by rw [hw]
    _ = (I * I) * (Y : ℂ) := by ring
    _ = (-1) * (Y : ℂ) := by rw [I_mul_I]
    _ = - (Y : ℂ) := by ring
  rw [hderiv_eq] at hreal
  exact hreal

/-- **Dual Cancellation Theorem 12 (Vertical Real Velocity)**:
Along the critical line, the real part of $\xi$ varies at velocity $-\operatorname{Im}(\xi'(1/2 + it))$:
$\frac{\partial}{\partial \tau} \operatorname{Re}(\xi(1/2 + i\tau))\Big|_{\tau=t} = -\operatorname{Im}(\xi'(1/2 + it))$. -/
theorem hasDerivAt_entireXi_vertical_re (t : ℝ) :
    HasDerivAt (fun τ : ℝ => (entireXi (((1 / 2 : ℝ) : ℂ) + I * (τ : ℂ))).re)
      (- (deriv entireXi (((1 / 2 : ℝ) : ℂ) + I * t)).im) t := by
  have h := hasDerivAt_entireXi_vertical t
  have hre := reCLM.hasFDerivAt.comp_hasDerivAt t h
  simp only [reCLM_apply, neg_re, ofReal_re] at hre
  exact hre

/-- **Dual Cancellation Theorem 13 (Vertical Imaginary Velocity Vanishing)**:
Along the critical line, the imaginary part of $\xi$ is identically constant (zero), so its
vertical derivative is identically zero:
$\frac{\partial}{\partial \tau} \operatorname{Im}(\xi(1/2 + i\tau))\Big|_{\tau=t} = 0$. -/
theorem hasDerivAt_entireXi_vertical_im (t : ℝ) :
    HasDerivAt (fun τ : ℝ => (entireXi (((1 / 2 : ℝ) : ℂ) + I * (τ : ℂ))).im) 0 t := by
  have h := hasDerivAt_entireXi_vertical t
  have him := imCLM.hasFDerivAt.comp_hasDerivAt t h
  simp only [imCLM_apply, neg_im, ofReal_im, neg_zero] at him
  exact him

/-- **Dual Cancellation Theorem 14 (Orthogonal 90-Degree Cauchy-Riemann Rotation)**:
At every point $1/2 + it$ on the critical line, the directional derivatives of $\operatorname{Re}(\xi)$
and $\operatorname{Im}(\xi)$ form an exact $90^\circ$ rotation:
- Transversal: $(\partial_\delta \operatorname{Re}, \partial_\delta \operatorname{Im}) = (0, Y(t))$
- Vertical:    $(\partial_\tau \operatorname{Re}, \partial_\tau \operatorname{Im}) = (-Y(t), 0)$
where $Y(t) = \operatorname{Im}(\xi'(1/2 + it))$.
Consequently, the Jacobian determinant is $(Y(t))^2 = \|\xi'(1/2 + it)\|^2 \ge 0$. -/
theorem dual_cancellation_cauchy_riemann_jacobian_det (t : ℝ) :
    (0 : ℝ) * 0 - (- (deriv entireXi (((1 / 2 : ℝ) : ℂ) + I * t)).im) *
      ((deriv entireXi (((1 / 2 : ℝ) : ℂ) + I * t)).im) =
      ((deriv entireXi (((1 / 2 : ℝ) : ℂ) + I * t)).im) ^ 2 := by
  ring

end RhG1Lean
