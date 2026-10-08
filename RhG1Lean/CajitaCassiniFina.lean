/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.

# La Cajita deformada, pliegue afinado: ‖Λ₀‖ ≤ 1/10 en la franja -1 ≤ Re z ≤ 2

En `CajitaUnconditional` el integrando de Mellin en (0,1) (lado reflejado por x ↦ 1/x)
se acotó por 3·y²e^{-πy} ≤ 3/4. Pero para y ≥ 1 el máximo de y²e^{-πy} está en y = 1:
y²e^{-πy} ≤ e^{-π} ≈ 0.0432. Y la cola en (1,∞) sólo aporta ∫₁^∞ 3e^{-πt} = 3e^{-π}/π.
Con la mayorante  G = 3e^{-π}·𝟙_(0,1] + 3e^{-πt}·𝟙_(1,∞):

    ∫ G = 3e^{-π}(1 + 1/π) < 1/5      ⇒      ‖Λ₀(z)‖ ≤ 1/10.

(Numéricamente sup ‖Λ₀‖ ≈ 0.0236, alcanzado en t = 0: la cota sigue ~4× floja.)
Consecuencia: el óvalo de Cassini ‖z(z-1)‖ < 10 (en la franja) es libre de ceros de ξ;
en la recta crítica |t| ≤ 3, y el rectángulo [0,1] × [-29/10, 29/10] entero.
-/
import RhG1Lean.CajitaUnconditional
import RhG1Lean.XiEntire
import RhG1Lean.StripReduction
import Mathlib.Analysis.Complex.ExponentialBounds

open Complex Real Set MeasureTheory HurwitzZeta WeakFEPair

namespace RhG1Lean

/-- Para y ≥ 1: y² e^{-πy} ≤ e^{-π} (el máximo está en el borde y = 1). -/
theorem sq_mul_exp_neg_pi_le_exp_neg_pi {y : ℝ} (hy : 1 ≤ y) :
    y ^ 2 * Real.exp (-π * y) ≤ Real.exp (-π) := by
  have hx : 0 ≤ π * (y - 1) := mul_nonneg Real.pi_pos.le (by linarith)
  have hq := Real.quadratic_le_exp_of_nonneg hx
  have hpi2 : 4 ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
  have hy1 : 0 ≤ y - 1 := by linarith
  -- y² ≤ e^{π(y-1)}
  have hsq : y ^ 2 ≤ Real.exp (π * (y - 1)) := by
    have h1 : 2 * (y - 1) ≤ π * (y - 1) := mul_le_mul_of_nonneg_right (by linarith [Real.pi_gt_three]) hy1
    have h2 : (y - 1) ^ 2 ≤ (π * (y - 1)) ^ 2 / 2 := by
      rw [mul_pow]; nlinarith [sq_nonneg (y - 1)]
    nlinarith
  have hsplit : Real.exp (-π * y) = Real.exp (-π) * (Real.exp (π * (y - 1)))⁻¹ := by
    rw [← Real.exp_neg, ← Real.exp_add]; ring_nf
  rw [hsplit]
  have hE : 0 < Real.exp (π * (y - 1)) := Real.exp_pos _
  have he0 : 0 < Real.exp (-π) := Real.exp_pos _
  calc y ^ 2 * (Real.exp (-π) * (Real.exp (π * (y - 1)))⁻¹)
      = Real.exp (-π) * (y ^ 2 / Real.exp (π * (y - 1))) := by ring
    _ ≤ Real.exp (-π) * 1 := by
        apply mul_le_mul_of_nonneg_left _ he0.le
        rw [div_le_one hE]; exact hsq
    _ = Real.exp (-π) := mul_one _

/-- e^{-π} < 1/20. -/
theorem exp_neg_pi_lt_one_twentieth : Real.exp (-π) < 1 / 20 := by
  have he := Real.exp_one_gt_d9
  have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  have he' : (2.718 : ℝ) < Real.exp 1 := by linarith
  have hc : (2.718 : ℝ) ^ 3 < Real.exp 1 ^ 3 := pow_lt_pow_left₀ he' (by norm_num) (by norm_num)
  have h20 : 20 < Real.exp 3 := by rw [h3]; norm_num at hc; linarith
  have hlt : Real.exp 3 < Real.exp π := Real.exp_lt_exp.mpr Real.pi_gt_three
  rw [Real.exp_neg, inv_eq_one_div, div_lt_div_iff₀ (Real.exp_pos _) (by norm_num)]
  linarith

/-- Mayorante afinada del integrando de Mellin. -/
theorem norm_mellin_integrand_le_fina {w : ℂ} (hw1 : -1 / 2 ≤ w.re) (hw2 : w.re ≤ 1)
    {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ (w - 1) • (hurwitzEvenFEPair 0).f_modif t‖ ≤
      (Ioc (0 : ℝ) 1).indicator (fun _ => 3 * Real.exp (-π)) t +
        (Ioi (1 : ℝ)).indicator (fun x => 3 * Real.exp (-π * x)) t := by
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
  have hsub : (w - 1).re = w.re - 1 := by simp
  rw [hsub]
  rcases lt_trichotomy t 1 with hlt | heq | hgt
  · have hmem : t ∈ Ioo (0 : ℝ) 1 := ⟨ht, hlt⟩
    have hIoc : t ∈ Ioc (0 : ℝ) 1 := ⟨ht, hlt.le⟩
    have hnIoi : t ∉ Ioi (1 : ℝ) := fun h => absurd (h : 1 < t) (not_lt.mpr hlt.le)
    rw [indicator_of_mem hIoc, indicator_of_notMem hnIoi, add_zero]
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
    have hm2 : t ^ (-(2 : ℝ)) = (1 / t) ^ 2 := by
      rw [Real.rpow_neg ht.le, Real.rpow_two, one_div, inv_pow]
    have hfin := sq_mul_exp_neg_pi_le_exp_neg_pi hy
    calc t ^ (w.re - 1) * (t ^ (-(1 / 2 : ℝ)) * (evenKernel 0 (1 / t) - 1))
        = t ^ (w.re - 1 + -(1 / 2 : ℝ)) * (evenKernel 0 (1 / t) - 1) := by
          rw [← mul_assoc, hcomb]
      _ ≤ (1 / t) ^ 2 * (3 * Real.exp (-π * (1 / t))) := by
          rw [← hm2]
          exact mul_le_mul hmono hK hK0 (Real.rpow_nonneg ht.le _)
      _ = 3 * ((1 / t) ^ 2 * Real.exp (-π * (1 / t))) := by ring
      _ ≤ 3 * Real.exp (-π) := by linarith
  · subst heq
    have h0 : (hurwitzEvenFEPair 0).f_modif 1 = 0 := by
      unfold f_modif
      simp
    rw [h0, norm_zero, mul_zero]
    have hA : 0 ≤ (Ioc (0 : ℝ) 1).indicator (fun _ => 3 * Real.exp (-π)) 1 :=
      indicator_nonneg (fun _ _ => by positivity) _
    have hB : 0 ≤ (Ioi (1 : ℝ)).indicator (fun x => 3 * Real.exp (-π * x)) 1 :=
      indicator_nonneg (fun _ _ => by positivity) _
    linarith
  · have hnIoc : t ∉ Ioc (0 : ℝ) 1 := fun h => absurd h.2 (not_le.mpr hgt)
    have hIoi : t ∈ Ioi (1 : ℝ) := hgt
    rw [indicator_of_notMem hnIoc, indicator_of_mem hIoi, zero_add]
    rw [f_modif_eq_on_Ioi_one hgt]
    have hK0 : 0 ≤ evenKernel 0 t - 1 := evenKernel₀_sub_one_nonneg ht
    have hK := evenKernel₀_sub_one_le_three_exp hgt.le
    have hcast : ((evenKernel 0 t : ℂ) - 1) = ((evenKernel 0 t - 1 : ℝ) : ℂ) := by push_cast; rfl
    rw [hcast, Complex.norm_of_nonneg hK0]
    have hp : t ^ (w.re - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hgt.le (by linarith)
    calc t ^ (w.re - 1) * (evenKernel 0 t - 1) ≤ 1 * (3 * Real.exp (-π * t)) :=
          mul_le_mul hp hK hK0 zero_le_one
      _ = 3 * Real.exp (-π * t) := one_mul _

/-- ‖mellin f_modif w‖ ≤ 3e^{-π}(1 + 1/π). -/
theorem norm_mellin_f_modif_le_fina {w : ℂ} (hw1 : -1 / 2 ≤ w.re) (hw2 : w.re ≤ 1) :
    ‖mellin (hurwitzEvenFEPair 0).f_modif w‖ ≤ 3 * Real.exp (-π) + 3 * Real.exp (-π) / π := by
  have hA_int : Integrable ((Ioc (0 : ℝ) 1).indicator (fun _ => 3 * Real.exp (-π))) :=
    (integrableOn_const (by simp)).integrable_indicator measurableSet_Ioc
  have hexp1 : IntegrableOn (fun x : ℝ => 3 * Real.exp (-π * x)) (Ioi 1) :=
    (exp_neg_integrableOn_Ioi 1 Real.pi_pos).const_mul 3
  have hB_int : Integrable ((Ioi (1 : ℝ)).indicator (fun x => 3 * Real.exp (-π * x))) :=
    hexp1.integrable_indicator measurableSet_Ioi
  have hG_int : IntegrableOn (fun t : ℝ =>
      (Ioc (0 : ℝ) 1).indicator (fun _ => 3 * Real.exp (-π)) t +
        (Ioi (1 : ℝ)).indicator (fun x => 3 * Real.exp (-π * x)) t) (Ioi 0) :=
    (hA_int.add hB_int).integrableOn
  have hbound : ∀ᵐ t : ℝ ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖(t : ℂ) ^ (w - 1) • (hurwitzEvenFEPair 0).f_modif t‖ ≤
        (Ioc (0 : ℝ) 1).indicator (fun _ => 3 * Real.exp (-π)) t +
          (Ioi (1 : ℝ)).indicator (fun x => 3 * Real.exp (-π * x)) t :=
    ae_restrict_of_forall_mem measurableSet_Ioi
      (fun t ht => norm_mellin_integrand_le_fina hw1 hw2 ht)
  have hle := norm_integral_le_of_norm_le hG_int hbound
  have hI1 : ∫ t in Ioi (0 : ℝ), (Ioc (0 : ℝ) 1).indicator (fun _ => 3 * Real.exp (-π)) t =
      3 * Real.exp (-π) := by
    rw [setIntegral_indicator measurableSet_Ioc,
      inter_eq_right.mpr Ioc_subset_Ioi_self, setIntegral_const,
      Real.volume_real_Ioc_of_le zero_le_one]
    simp
  have hI2 : ∫ t in Ioi (0 : ℝ), (Ioi (1 : ℝ)).indicator (fun x => 3 * Real.exp (-π * x)) t =
      3 * Real.exp (-π) / π := by
    rw [setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.mpr (Ioi_subset_Ioi zero_le_one), integral_const_mul,
      integral_exp_mul_Ioi (neg_lt_zero.mpr Real.pi_pos) 1]
    rw [mul_one, neg_div_neg_eq]
    ring
  have hIG : ∫ t in Ioi (0 : ℝ),
      ((Ioc (0 : ℝ) 1).indicator (fun _ => 3 * Real.exp (-π)) t +
        (Ioi (1 : ℝ)).indicator (fun x => 3 * Real.exp (-π * x)) t) =
        3 * Real.exp (-π) + 3 * Real.exp (-π) / π := by
    rw [integral_add hA_int.integrableOn hB_int.integrableOn, hI1, hI2]
  unfold mellin
  rw [← hIG]
  exact hle

/-- **Pliegue afinado.** ‖Λ₀(z)‖ ≤ 1/10 en toda la franja vertical -1 ≤ Re z ≤ 2. -/
theorem zeta₀_norm_le_tenth {z : ℂ} (h1 : -1 ≤ z.re) (h2 : z.re ≤ 2) :
    ‖completedRiemannZeta₀ z‖ ≤ 1 / 10 := by
  have hre : (z / 2).re = z.re / 2 := by simp
  have hb := norm_mellin_f_modif_le_fina (w := z / 2) (by rw [hre]; linarith) (by rw [hre]; linarith)
  have he := exp_neg_pi_lt_one_twentieth
  have he0 : 0 < Real.exp (-π) := Real.exp_pos _
  have hpi : Real.exp (-π) / π ≤ Real.exp (-π) / 3 :=
    div_le_div_of_nonneg_left he0.le (by norm_num) Real.pi_gt_three.le
  rw [completedRiemannZeta₀_eq_half_mellin, norm_div]
  have h2n : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2n, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  have : 3 * Real.exp (-π) / π = 3 * (Real.exp (-π) / π) := by ring
  rw [this] at hb
  nlinarith

/-- **Cajita de Cassini afinada.** En la franja -1 ≤ Re z ≤ 2: ‖z(z-1)‖ < 10 ⇒ ξ(z) ≠ 0. -/
theorem entireXi_ne_zero_of_cassini_fina {z : ℂ} (h1 : -1 ≤ z.re) (h2 : z.re ≤ 2)
    (h : ‖z * (z - 1)‖ < 10) : entireXi z ≠ 0 := by
  have hL := zeta₀_norm_le_tenth h1 h2
  apply entireXi_ne_zero_of_sub_half_lt
  have heq : entireXi z - 1 / 2 = (z * (z - 1) / 2) * completedRiemannZeta₀ z := by
    unfold entireXi; ring
  rw [heq, norm_mul, norm_div]
  have h2n : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2n]
  calc ‖z * (z - 1)‖ / 2 * ‖completedRiemannZeta₀ z‖
      ≤ ‖z * (z - 1)‖ / 2 * (1 / 10) := mul_le_mul_of_nonneg_left hL (by positivity)
    _ < 10 / 2 * (1 / 10) := by
        apply mul_lt_mul_of_pos_right _ (by norm_num); linarith
    _ = 1 / 2 := by norm_num

/-- El rectángulo [0, 1] × [-29/10, 29/10] (toda la franja crítica hasta altura 2.9) es libre
de ceros de ξ. La Cajita original llegaba a altura 1/2. -/
theorem entireXi_ne_zero_box_fina {z : ℂ} (h1 : 0 ≤ z.re) (h2 : z.re ≤ 1)
    (him : |z.im| ≤ 29 / 10) : entireXi z ≠ 0 := by
  apply entireXi_ne_zero_of_cassini_fina (by linarith) (by linarith)
  have ht2 : z.im ^ 2 ≤ 841 / 100 := by
    have := sq_abs z.im; nlinarith [abs_nonneg z.im]
  have hA : ‖z‖ ^ 2 ≤ 941 / 100 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; nlinarith
  have hB : ‖z - 1‖ ^ 2 ≤ 941 / 100 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; nlinarith
  rw [norm_mul]
  have hab : 0 ≤ ‖z‖ * ‖z - 1‖ := mul_nonneg (norm_nonneg z) (norm_nonneg (z - 1))
  have hsq : (‖z‖ * ‖z - 1‖) ^ 2 ≤ 941 / 100 * (941 / 100) := by
    calc (‖z‖ * ‖z - 1‖) ^ 2 = ‖z‖ ^ 2 * ‖z - 1‖ ^ 2 := mul_pow _ _ _
      _ ≤ 941 / 100 * (941 / 100) := mul_le_mul hA hB (sq_nonneg _) (by norm_num)
  nlinarith

/-- En la recta crítica: |t| ≤ 3 ⇒ ξ(1/2 + it) ≠ 0. -/
theorem entireXi_ne_zero_critical_fina {z : ℂ} (hre : z.re = 1 / 2) (him : |z.im| ≤ 3) :
    entireXi z ≠ 0 := by
  apply entireXi_ne_zero_of_cassini_fina (by rw [hre]; norm_num) (by rw [hre]; norm_num)
  have hprod : z * (z - 1) = ((-(1 / 4 + z.im ^ 2) : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [Complex.mul_re, hre, sq]; ring
    · simp [Complex.mul_im, hre, sq]; ring
  rw [hprod, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
  have := sq_abs z.im; nlinarith [abs_nonneg z.im]

/-- ζ ≠ 0 en [0,1) × [-29/10, 29/10] ∩ {Re > 0}. -/
theorem riemannZeta_ne_zero_box_fina {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (him : |s.im| ≤ 29 / 10) : riemannZeta s ≠ 0 := fun hz =>
  entireXi_ne_zero_box_fina h0.le h1.le him ((entireXi_eq_zero_iff_zeta_of_mem_strip h0 h1).mpr hz)

end RhG1Lean
