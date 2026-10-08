/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.

# El semiplano O₁ = {Re u ≥ 0} es libre de ceros (incondicional)

En el mapa mental (prospectos 36–51, RASTRO §§62–82) RH se reescribe con el
pliegue cuadrático u = w², w = s - 1/2, ξ(1/2 + w) = g(w²):

    RH  ⇔  g(u) ≠ 0 fuera del rayo (-∞, 0].

El complemento del rayo se partía en O₁ = {Re u > 0} y el sector {Im u ≠ 0}
(Cβ21, Cβ19, Cβ22). Para O₁ se eligió el contorno Γ½ (semidisco) con huecos
G1–G5 (cotas en arco y diámetro, pareja de Rouché, ...), todos abiertos.

Observación: Re u = δ² - t² con w = δ + i t. Así Re u ≥ 0 ⇔ |t| ≤ |δ|.
Dentro de la franja |δ| < 1/2 eso fuerza |t| < 1/2: el cono O₁ cae dentro de la
Cajita (y su espejo por la ecuación funcional). Fuera de la franja, ζ ≠ 0
(Mathlib, Re s ≥ 1). Por lo tanto g ≠ 0 en todo el semiplano cerrado Re u ≥ 0,
SIN Rouché y SIN cotas de Stirling: basta la Cajita incondicional.

Lo que queda de RH es exactamente el sector Re u < 0, Im u ≠ 0 (la Boca A).
-/
import Mathlib.NumberTheory.LSeries.Nonvanishing
import RhG1Lean.CajitaUnconditional
import RhG1Lean.XiEntire
import RhG1Lean.StripReduction

open Complex

namespace RhG1Lean

/-- ξ no se anula en Re s ≥ 1 (Mathlib: ζ ≠ 0 en Re s ≥ 1). -/
theorem entireXi_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : entireXi s ≠ 0 := by
  by_cases h1 : s = 1
  · subst h1
    rw [entireXi_one]
    norm_num
  have h0 : s ≠ 0 := by
    intro h
    subst h
    simp at hs
    linarith
  rw [entireXi_eq_mul_completedRiemannZeta h0 h1]
  have hz := riemannZeta_ne_zero_of_one_le_re hs
  have hpre : s * (s - 1) / 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1)) two_ne_zero
  refine mul_ne_zero hpre ?_
  intro hc
  apply hz
  rw [riemannZeta_def_of_ne_zero h0, hc, zero_div]

/-- Mitad derecha del cono: 1/2 ≤ Re s y |Im s| ≤ Re s - 1/2. -/
theorem entireXi_ne_zero_of_cone_right {s : ℂ} (hre : 1 / 2 ≤ s.re)
    (him : |s.im| ≤ s.re - 1 / 2) : entireXi s ≠ 0 := by
  by_cases h1' : 1 ≤ s.re
  · exact entireXi_ne_zero_of_one_le_re h1'
  have h1 : s.re < 1 := not_le.mp h1'
  have hmem : s ∈ leftoverRect := by
    refine ⟨by linarith, h1.le, ?_⟩
    linarith
  exact cajita_entireXi_ne_zero_unconditional s hmem

/-- **Cono O₁ libre de ceros**: si |Im s| ≤ |Re s - 1/2| entonces ξ(s) ≠ 0. -/
theorem entireXi_ne_zero_of_cone {s : ℂ} (h : |s.im| ≤ |s.re - 1 / 2|) :
    entireXi s ≠ 0 := by
  by_cases hre : 1 / 2 ≤ s.re
  · have h' : |s.im| ≤ s.re - 1 / 2 := by
      rwa [abs_of_nonneg (show (0 : ℝ) ≤ s.re - 1 / 2 by linarith)] at h
    exact entireXi_ne_zero_of_cone_right hre h'
  · have hre' : s.re < 1 / 2 := not_le.mp hre
    have h' : |s.im| ≤ 1 / 2 - s.re := by
      rw [abs_of_neg (show s.re - 1 / 2 < 0 by linarith)] at h
      linarith
    rw [← entireXi_one_sub]
    apply entireXi_ne_zero_of_cone_right
    · simp only [Complex.sub_re, Complex.one_re]
      linarith
    · simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, zero_sub,
        abs_neg]
      linarith

/-- **Versión en el plano u = w²** (lenguaje del mapa): g ≠ 0 en Re u ≥ 0.
Es decir, para todo w con Re(w²) ≥ 0, ξ(1/2 + w) ≠ 0. -/
theorem entireXi_ne_zero_of_re_sq_nonneg {w : ℂ} (hw : 0 ≤ (w ^ 2).re) :
    entireXi (1 / 2 + w) ≠ 0 := by
  apply entireXi_ne_zero_of_cone
  have hsq : (w ^ 2).re = w.re ^ 2 - w.im ^ 2 := by
    simp [sq, Complex.mul_re]
  have hle : w.im ^ 2 ≤ w.re ^ 2 := by linarith
  have habs : |w.im| ≤ |w.re| := sq_le_sq.mp hle
  simpa using habs

/-- Corolario en ζ: ningún cero de ζ en la franja con |Im s| ≤ |Re s - 1/2|. -/
theorem riemannZeta_ne_zero_of_cone {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (h : |s.im| ≤ |s.re - 1 / 2|) : riemannZeta s ≠ 0 := fun hz =>
  entireXi_ne_zero_of_cone h ((entireXi_eq_zero_iff_zeta_of_mem_strip h0 h1).mpr hz)

end RhG1Lean
