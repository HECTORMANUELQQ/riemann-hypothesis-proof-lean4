/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.

# La Cajita deformada, tercer escalón: mayorante simétrica bajo el pliegue x ↦ 1/x

La mayorante del integrando de Mellin se toma ella misma plegada:

    G = g + g^♭,   g(y) = 3e^{-πy}·𝟙_(1,∞)(y),   g^♭(t) = t^{-2}·g(1/t)

(g^♭ es la imagen de g por el pliegue x ↦ 1/x con su jacobiano). Por el cambio de variable
x ↦ x^{-1} de Mathlib (`integral_comp_rpow_Ioi`), ∫ g^♭ = ∫ g, así que

    ∫ G = 2 ∫₁^∞ 3e^{-πy} dy = 6e^{-π}/π < 1/10      ⇒      ‖Λ₀(z)‖ ≤ 1/20

en la franja -1 ≤ Re z ≤ 2 (numéricamente sup ‖Λ₀‖ ≈ 0.0236: la cota está a ×2.1).
Consecuencia: el óvalo de Cassini ‖z(z-1)‖ < 20 es libre de ceros de ξ; el rectángulo
[0,1] × [-43/10, 43/10] entero, y la recta crítica hasta |t| ≤ 22/5.
-/
import RhG1Lean.CajitaCassiniFina

open Complex Real Set MeasureTheory HurwitzZeta WeakFEPair

namespace RhG1Lean

/-- La cola: g(y) = 3e^{-πy} en (1, ∞), 0 fuera. -/
noncomputable def gCola (y : ℝ) : ℝ := (Ioi (1 : ℝ)).indicator (fun x => 3 * Real.exp (-π * x)) y

/-- Su pliegue por x ↦ 1/x con jacobiano: g^♭(t) = |−1| t^{−2} g(t^{−1}). -/
noncomputable def gPliegue (t : ℝ) : ℝ :=
  (|(-1 : ℝ)| * t ^ ((-1 : ℝ) - 1)) • gCola (t ^ (-1 : ℝ))

theorem gCola_nonneg (y : ℝ) : 0 ≤ gCola y :=
  indicator_nonneg (fun _ _ => by positivity) _

theorem gPliegue_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ gPliegue t := by
  unfold gPliegue
  rw [smul_eq_mul]
  exact mul_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg ht.le _)) (gCola_nonneg _)

theorem gCola_integrableOn : IntegrableOn gCola (Ioi 0) := by
  have hexp1 : IntegrableOn (fun x : ℝ => 3 * Real.exp (-π * x)) (Ioi 1) :=
    (exp_neg_integrableOn_Ioi 1 Real.pi_pos).const_mul 3
  exact (hexp1.integrable_indicator measurableSet_Ioi).integrableOn

theorem gPliegue_integrableOn : IntegrableOn gPliegue (Ioi 0) :=
  (integrableOn_Ioi_comp_rpow_iff gCola (by norm_num : (-1 : ℝ) ≠ 0)).mpr gCola_integrableOn

theorem integral_gCola : ∫ t in Ioi (0 : ℝ), gCola t = 3 * Real.exp (-π) / π := by
  unfold gCola
  rw [setIntegral_indicator measurableSet_Ioi,
    inter_eq_right.mpr (Ioi_subset_Ioi zero_le_one), integral_const_mul,
    integral_exp_mul_Ioi (neg_lt_zero.mpr Real.pi_pos) 1]
  rw [mul_one, neg_div_neg_eq]
  ring

/-- El pliegue conserva la integral (cambio de variable x ↦ x⁻¹). -/
theorem integral_gPliegue : ∫ t in Ioi (0 : ℝ), gPliegue t = 3 * Real.exp (-π) / π := by
  unfold gPliegue
  rw [integral_comp_rpow_Ioi gCola (by norm_num : (-1 : ℝ) ≠ 0)]
  exact integral_gCola

/-- Valores del pliegue: para 0 < t < 1, g^♭(t) = t^{-2}·3e^{-π/t}. -/
theorem gPliegue_of_lt_one {t : ℝ} (ht : 0 < t) (h1 : t < 1) :
    gPliegue t = t ^ (-(2 : ℝ)) * (3 * Real.exp (-π * (1 / t))) := by
  have hinv : t ^ (-1 : ℝ) = 1 / t := by rw [Real.rpow_neg_one, one_div]
  have hmem : (1 / t) ∈ Ioi (1 : ℝ) := by
    show 1 < 1 / t
    rw [lt_div_iff₀ ht]; linarith
  unfold gPliegue gCola
  rw [hinv, indicator_of_mem hmem, smul_eq_mul]
  norm_num

theorem gPliegue_of_one_lt {t : ℝ} (ht : 1 < t) : gPliegue t = 0 := by
  have ht0 : 0 < t := by linarith
  have hinv : t ^ (-1 : ℝ) = 1 / t := by rw [Real.rpow_neg_one, one_div]
  have hnmem : (1 / t) ∉ Ioi (1 : ℝ) := by
    intro h
    have h' : 1 < 1 / t := h
    rw [lt_div_iff₀ ht0] at h'
    linarith
  unfold gPliegue gCola
  rw [hinv, indicator_of_notMem hnmem, smul_zero]

/-- Mayorante plegada del integrando de Mellin. -/
theorem norm_mellin_integrand_le_pliegue {w : ℂ} (hw1 : -1 / 2 ≤ w.re) (hw2 : w.re ≤ 1)
    {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ (w - 1) • (hurwitzEvenFEPair 0).f_modif t‖ ≤ gPliegue t + gCola t := by
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
  have hsub : (w - 1).re = w.re - 1 := by simp
  rw [hsub]
  rcases lt_trichotomy t 1 with hlt | heq | hgt
  · have hmem : t ∈ Ioo (0 : ℝ) 1 := ⟨ht, hlt⟩
    have hnIoi : t ∉ Ioi (1 : ℝ) := fun h => absurd (h : 1 < t) (not_lt.mpr hlt.le)
    have hc0 : gCola t = 0 := by unfold gCola; rw [indicator_of_notMem hnIoi]
    rw [hc0, add_zero, gPliegue_of_lt_one ht hlt]
    rw [f_modif_eq_reflected_on_Ioo hmem]
    have hy : 1 ≤ 1 / t := by rw [le_div_iff₀ ht]; linarith
    have hK0 : 0 ≤ evenKernel 0 (1 / t) - 1 := evenKernel₀_sub_one_nonneg (by positivity)
    have hK := evenKernel₀_sub_one_le_three_exp hy
    have hpow0 : 0 ≤ t ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg ht.le _
    rw [norm_mul, Complex.norm_of_nonneg hpow0, Complex.norm_of_nonneg hK0]
    have hcomb : t ^ (w.re - 1) * t ^ (-(1 / 2 : ℝ)) = t ^ (w.re - 1 + -(1 / 2 : ℝ)) :=
      (Real.rpow_add ht _ _).symm
    have hmono : t ^ (w.re - 1 + -(1 / 2 : ℝ)) ≤ t ^ (-(2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge ht hlt.le (by linarith)
    calc t ^ (w.re - 1) * (t ^ (-(1 / 2 : ℝ)) * (evenKernel 0 (1 / t) - 1))
        = t ^ (w.re - 1 + -(1 / 2 : ℝ)) * (evenKernel 0 (1 / t) - 1) := by
          rw [← mul_assoc, hcomb]
      _ ≤ t ^ (-(2 : ℝ)) * (3 * Real.exp (-π * (1 / t))) :=
          mul_le_mul hmono hK hK0 (Real.rpow_nonneg ht.le _)
  · subst heq
    have h0 : (hurwitzEvenFEPair 0).f_modif 1 = 0 := by
      unfold f_modif
      simp
    rw [h0, norm_zero, mul_zero]
    exact add_nonneg (gPliegue_nonneg one_pos) (gCola_nonneg 1)
  · have hIoi : t ∈ Ioi (1 : ℝ) := hgt
    have hc : gCola t = 3 * Real.exp (-π * t) := by unfold gCola; rw [indicator_of_mem hIoi]
    rw [gPliegue_of_one_lt hgt, zero_add, hc]
    rw [f_modif_eq_on_Ioi_one hgt]
    have hK0 : 0 ≤ evenKernel 0 t - 1 := evenKernel₀_sub_one_nonneg ht
    have hK := evenKernel₀_sub_one_le_three_exp hgt.le
    have hcast : ((evenKernel 0 t : ℂ) - 1) = ((evenKernel 0 t - 1 : ℝ) : ℂ) := by push_cast; rfl
    rw [hcast, Complex.norm_of_nonneg hK0]
    have hp : t ^ (w.re - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hgt.le (by linarith)
    calc t ^ (w.re - 1) * (evenKernel 0 t - 1) ≤ 1 * (3 * Real.exp (-π * t)) :=
          mul_le_mul hp hK hK0 zero_le_one
      _ = 3 * Real.exp (-π * t) := one_mul _

/-- ‖mellin f_modif w‖ ≤ 6e^{-π}/π. -/
theorem norm_mellin_f_modif_le_pliegue {w : ℂ} (hw1 : -1 / 2 ≤ w.re) (hw2 : w.re ≤ 1) :
    ‖mellin (hurwitzEvenFEPair 0).f_modif w‖ ≤ 6 * Real.exp (-π) / π := by
  have hG_int : IntegrableOn (fun t : ℝ => gPliegue t + gCola t) (Ioi 0) :=
    gPliegue_integrableOn.add gCola_integrableOn
  have hbound : ∀ᵐ t : ℝ ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖(t : ℂ) ^ (w - 1) • (hurwitzEvenFEPair 0).f_modif t‖ ≤ gPliegue t + gCola t :=
    ae_restrict_of_forall_mem measurableSet_Ioi
      (fun t ht => norm_mellin_integrand_le_pliegue hw1 hw2 ht)
  have hle := norm_integral_le_of_norm_le hG_int hbound
  have hIG : ∫ t in Ioi (0 : ℝ), (gPliegue t + gCola t) = 6 * Real.exp (-π) / π := by
    rw [integral_add gPliegue_integrableOn gCola_integrableOn, integral_gPliegue, integral_gCola]
    ring
  unfold mellin
  rw [← hIG]
  exact hle

/-- **Pliegue simétrico.** ‖Λ₀(z)‖ ≤ 1/20 en toda la franja vertical -1 ≤ Re z ≤ 2. -/
theorem zeta₀_norm_le_twentieth {z : ℂ} (h1 : -1 ≤ z.re) (h2 : z.re ≤ 2) :
    ‖completedRiemannZeta₀ z‖ ≤ 1 / 20 := by
  have hre : (z / 2).re = z.re / 2 := by simp
  have hb := norm_mellin_f_modif_le_pliegue (w := z / 2) (by rw [hre]; linarith)
    (by rw [hre]; linarith)
  have he := exp_neg_pi_lt_one_twentieth
  have he0 : 0 < Real.exp (-π) := Real.exp_pos _
  have hq : 6 * Real.exp (-π) / π ≤ 6 * Real.exp (-π) / 3 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) Real.pi_gt_three.le
  rw [completedRiemannZeta₀_eq_half_mellin, norm_div]
  have h2n : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2n, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- **Cajita de Cassini, tercer escalón.** En -1 ≤ Re z ≤ 2: ‖z(z-1)‖ < 20 ⇒ ξ(z) ≠ 0. -/
theorem entireXi_ne_zero_of_cassini_20 {z : ℂ} (h1 : -1 ≤ z.re) (h2 : z.re ≤ 2)
    (h : ‖z * (z - 1)‖ < 20) : entireXi z ≠ 0 := by
  have hL := zeta₀_norm_le_twentieth h1 h2
  apply entireXi_ne_zero_of_sub_half_lt
  have heq : entireXi z - 1 / 2 = (z * (z - 1) / 2) * completedRiemannZeta₀ z := by
    unfold entireXi; ring
  rw [heq, norm_mul, norm_div]
  have h2n : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2n]
  calc ‖z * (z - 1)‖ / 2 * ‖completedRiemannZeta₀ z‖
      ≤ ‖z * (z - 1)‖ / 2 * (1 / 20) := mul_le_mul_of_nonneg_left hL (by positivity)
    _ < 20 / 2 * (1 / 20) := by
        apply mul_lt_mul_of_pos_right _ (by norm_num); linarith
    _ = 1 / 2 := by norm_num

/-- El rectángulo [0, 1] × [-43/10, 43/10] es libre de ceros de ξ (Cajita original: altura 1/2). -/
theorem entireXi_ne_zero_box_43 {z : ℂ} (h1 : 0 ≤ z.re) (h2 : z.re ≤ 1)
    (him : |z.im| ≤ 43 / 10) : entireXi z ≠ 0 := by
  apply entireXi_ne_zero_of_cassini_20 (by linarith) (by linarith)
  have ht2 : z.im ^ 2 ≤ 1849 / 100 := by
    have := sq_abs z.im; nlinarith [abs_nonneg z.im]
  have hA : ‖z‖ ^ 2 ≤ 1949 / 100 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; nlinarith
  have hB : ‖z - 1‖ ^ 2 ≤ 1949 / 100 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; nlinarith
  rw [norm_mul]
  have hab : 0 ≤ ‖z‖ * ‖z - 1‖ := mul_nonneg (norm_nonneg z) (norm_nonneg (z - 1))
  have hsq : (‖z‖ * ‖z - 1‖) ^ 2 ≤ 1949 / 100 * (1949 / 100) := by
    calc (‖z‖ * ‖z - 1‖) ^ 2 = ‖z‖ ^ 2 * ‖z - 1‖ ^ 2 := mul_pow _ _ _
      _ ≤ 1949 / 100 * (1949 / 100) := mul_le_mul hA hB (sq_nonneg _) (by norm_num)
  nlinarith

/-- En la recta crítica: |t| ≤ 22/5 ⇒ ξ(1/2 + it) ≠ 0. -/
theorem entireXi_ne_zero_critical_44 {z : ℂ} (hre : z.re = 1 / 2) (him : |z.im| ≤ 22 / 5) :
    entireXi z ≠ 0 := by
  apply entireXi_ne_zero_of_cassini_20 (by rw [hre]; norm_num) (by rw [hre]; norm_num)
  have hprod : z * (z - 1) = ((-(1 / 4 + z.im ^ 2) : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [Complex.mul_re, hre, sq]; ring
    · simp [Complex.mul_im, hre, sq]; ring
  rw [hprod, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
  have := sq_abs z.im; nlinarith [abs_nonneg z.im]

/-- ζ ≠ 0 en (0,1) × [-43/10, 43/10]. -/
theorem riemannZeta_ne_zero_box_43 {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (him : |s.im| ≤ 43 / 10) : riemannZeta s ≠ 0 := fun hz =>
  entireXi_ne_zero_box_43 h0.le h1.le him ((entireXi_eq_zero_iff_zeta_of_mem_strip h0 h1).mpr hz)

end RhG1Lean
