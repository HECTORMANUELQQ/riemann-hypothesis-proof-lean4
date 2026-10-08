/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import RhG1Lean.Arc

/-!
# Cota |Γ(z)| ≤ Γ(Re z) si Re z > 0

Esto llena el hueco 65.4 del prospecto 65 / átomo 60.

No es el resto de Stirling (Bernoulli). Es la cota que sale de la
integral de Euler, que es cómo mathlib *define* Γ (y es AX-C4 del mapa:
π^{-s/2} Γ(s/2) ζ). En el arco Re(s/2) > 1/2 > 0, así que aplica.

Python midió |z μ(z)| ≤ 1/12 (Stirling); eso no cuenta como prueba.
Esta cota sí, si `lake build` pasa.
-/

open Complex Real MeasureTheory Set

namespace RhG1Lean

/-- Integrando: `‖e^{-x} x^{z-1}‖ = e^{-x} x^{σ-1}` para x > 0. -/
lemma norm_Gamma_integrand {z : ℂ} {x : ℝ} (hx : 0 < x) :
    ‖(↑(Real.exp (-x)) * (x : ℂ) ^ (z - 1) : ℂ)‖ =
      Real.exp (-x) * x ^ (z.re - 1) := by
  rw [norm_mul, Complex.norm_of_nonneg (le_of_lt (Real.exp_pos _)),
    norm_cpow_eq_rpow_re_of_pos hx]
  simp [sub_re]

/-- **Lema 65.4 (Euler).** Si `0 < Re z` entonces `‖Γ(z)‖ ≤ Γ(Re z)`. -/
theorem norm_Gamma_le_Gamma_re {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  have hzR : 0 < z.re := hz
  rw [Complex.Gamma_eq_integral hz, Real.Gamma_eq_integral hzR]
  -- ‖∫ f‖ ≤ ∫ ‖f‖
  have hf : IntegrableOn (fun x : ℝ => (↑(Real.exp (-x)) * (x : ℂ) ^ (z - 1) : ℂ))
      (Ioi 0) := Complex.GammaIntegral_convergent hz
  have hle :
      ‖∫ x in Ioi (0 : ℝ), (↑(Real.exp (-x)) * (x : ℂ) ^ (z - 1) : ℂ)‖ ≤
        ∫ x in Ioi (0 : ℝ),
          ‖(↑(Real.exp (-x)) * (x : ℂ) ^ (z - 1) : ℂ)‖ :=
    norm_integral_le_integral_norm _
  refine hle.trans ?_
  have hcongr :
      (fun x : ℝ => ‖(↑(Real.exp (-x)) * (x : ℂ) ^ (z - 1) : ℂ)‖) =ᵐ[volume.restrict (Ioi 0)]
        fun x : ℝ => Real.exp (-x) * x ^ (z.re - 1) := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
    filter_upwards with x hx
    exact norm_Gamma_integrand (mem_Ioi.mp hx)
  rw [integral_congr_ae hcongr]

/-- (s/2).re = s.re / 2. -/
theorem re_div_two (s : ℂ) : (s / 2).re = s.re / 2 := by
  rw [div_re]
  simp
  ring

/-- En el arco, Re(s/2) = σ/2 > 1/2 > 0. -/
theorem re_div_two_pos_of_reSR {R φ : ℝ} (hR : 1 / 2 < R) (hφ : |φ| ≤ π / 4)
    {s : ℂ} (hs : s.re = reSR R φ) : 0 < (s / 2).re := by
  have h1 : 1 < s.re := hs ▸ reSR_gt_one hR hφ
  rw [re_div_two]
  linarith

/-- 65.4 en el arco: `‖Γ(s/2)‖ ≤ Γ(σ/2)`. -/
theorem norm_Gamma_half_le_on_arc {R φ : ℝ} (hR : 1 / 2 < R) (hφ : |φ| ≤ π / 4)
    {s : ℂ} (hs : s.re = reSR R φ) :
    ‖Complex.Gamma (s / 2)‖ ≤ Real.Gamma ((s / 2).re) :=
  norm_Gamma_le_Gamma_re (re_div_two_pos_of_reSR hR hφ hs)

end RhG1Lean
