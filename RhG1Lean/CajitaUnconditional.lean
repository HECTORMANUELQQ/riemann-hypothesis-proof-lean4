/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.

# Cajita incondicional

Cierre SIN hipótesis de la "Habitación 1" (la Cajita):

  ∀ z ∈ leftoverRect, ‖completedRiemannZeta₀ z‖ ≤ 1

y, por `habitacion1_resolved_of_zeta₀_bound`, ζ(s) ≠ 0 en `leftoverInterior`.

Estrategia (sin cambio de variable y sin probar integrabilidad del integrando):
  * Λ₀(z) = (1/2) · mellin f_modif (z/2), con Re(z/2) ∈ [1/4, 1/2].
  * Cota puntual ‖t^(w-1) • f_modif t‖ ≤ G t, donde
      G t = (3/4)·𝟙_(0,1](t) + 3·e^{-π t}.
    - t > 1: f_modif t = θ(t) - 1 ≤ 3 e^{-π t} y ‖t^(w-1)‖ ≤ 1.
    - 0 < t < 1: f_modif t = t^{-1/2}(θ(1/t) - 1) (ecuación funcional),
      y con y = 1/t ≥ 1: integrando ≤ 3 y² e^{-π y} ≤ 3/4.
  * `norm_integral_le_of_norm_le` sólo exige que G sea integrable.
  * ∫ G = 3/4 + 3/π < 2, luego ‖Λ₀(z)‖ ≤ (3/4 + 3/π)/2 < 1.
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.ExpDecay
import RhG1Lean.CajitaMellinRepresentation
import RhG1Lean.CajitaMellinEvaluation
import RhG1Lean.CajitaDischarge
import RhG1Lean.LambdaZeroRealBound

open Complex Real Set MeasureTheory HurwitzZeta WeakFEPair

namespace RhG1Lean

/-- Paso 1. Cola theta: para u ≥ 1, θ(u) - 1 ≤ 3 e^{-π u}. -/
theorem evenKernel₀_sub_one_le_three_exp {u : ℝ} (hu : 1 ≤ u) :
    evenKernel 0 u - 1 ≤ 3 * Real.exp (-π * u) := by
  have hu0 : 0 < u := lt_of_lt_of_le one_pos hu
  have hr0 : 0 ≤ Real.exp (-π * u) := (Real.exp_pos _).le
  have hr_le : Real.exp (-π * u) ≤ Real.exp (-π) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  have hr8 : Real.exp (-π * u) < 1 / 8 := lt_of_le_of_lt hr_le exp_neg_pi_lt_one_eighth
  have hr1 : Real.exp (-π * u) < 1 := by linarith
  have hgeom : HasSum (fun n : ℕ => 2 * Real.exp (-π * u) * Real.exp (-π * u) ^ n)
      (2 * Real.exp (-π * u) * (1 - Real.exp (-π * u))⁻¹) :=
    (hasSum_geometric_of_lt_one hr0 hr1).mul_left (2 * Real.exp (-π * u))
  have hle : ∀ n : ℕ, 2 * Real.exp (-π * (n + 1) ^ 2 * u) ≤
      2 * Real.exp (-π * u) * Real.exp (-π * u) ^ n := by
    intro n
    have heq : 2 * Real.exp (-π * u) * Real.exp (-π * u) ^ n =
        2 * Real.exp (-π * ((n : ℝ) + 1) * u) := by
      rw [mul_assoc, ← pow_succ', ← Real.exp_nat_mul]
      congr 2
      push_cast
      ring
    rw [heq]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have key : 0 ≤ π * (((n : ℝ) + 1) * u) * n := by positivity
    nlinarith [key]
  have h1 := hasSum_le hle (hasSum_nat_evenKernel₀ hu0) hgeom
  have h1r : 0 < 1 - Real.exp (-π * u) := by linarith
  have h2 : 2 * Real.exp (-π * u) * (1 - Real.exp (-π * u))⁻¹ ≤ 3 * Real.exp (-π * u) := by
    rw [← div_eq_mul_inv, div_le_iff₀ h1r]
    nlinarith [hr0, hr8]
  linarith

/-- Paso 2. Desigualdad elemental: para y ≥ 1, y² e^{-π y} ≤ 1/4. -/
theorem sq_mul_exp_neg_pi_le {y : ℝ} (hy : 1 ≤ y) :
    y ^ 2 * Real.exp (-π * y) ≤ 1 / 4 := by
  have hy0 : 0 ≤ π * y := by positivity
  have hq := Real.quadratic_le_exp_of_nonneg hy0
  have hpi2 : 9 ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
  have hE : 0 < Real.exp (π * y) := Real.exp_pos _
  have hneg : Real.exp (-π * y) = (Real.exp (π * y))⁻¹ := by
    rw [neg_mul, Real.exp_neg]
  rw [hneg, ← div_eq_mul_inv, div_le_iff₀ hE]
  have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
  have h9 : 9 * y ^ 2 ≤ π ^ 2 * y ^ 2 := mul_le_mul_of_nonneg_right hpi2 hy2
  nlinarith [hq, h9, hy0]

/-- Paso 3. Cota puntual del integrando de Mellin sobre (0, ∞). -/
theorem norm_mellin_integrand_le {w : ℂ} (hw1 : -1 / 2 ≤ w.re) (hw2 : w.re ≤ 1)
    {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ (w - 1) • (hurwitzEvenFEPair 0).f_modif t‖ ≤
      (Ioc (0 : ℝ) 1).indicator (fun _ => (3 / 4 : ℝ)) t + 3 * Real.exp (-π * t) := by
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
  have hsub : (w - 1).re = w.re - 1 := by simp
  rw [hsub]
  have hexp0 : 0 ≤ 3 * Real.exp (-π * t) := by positivity
  rcases lt_trichotomy t 1 with hlt | heq | hgt
  · -- 0 < t < 1: reflexión por la ecuación funcional.
    have hmem : t ∈ Ioo (0 : ℝ) 1 := ⟨ht, hlt⟩
    have hIoc : t ∈ Ioc (0 : ℝ) 1 := ⟨ht, hlt.le⟩
    rw [indicator_of_mem hIoc]
    rw [f_modif_eq_reflected_on_Ioo hmem]
    have hy : 1 ≤ 1 / t := by rw [le_div_iff₀ ht]; linarith
    have hK0 : 0 ≤ evenKernel 0 (1 / t) - 1 := evenKernel₀_sub_one_nonneg (by positivity)
    have hK := evenKernel₀_sub_one_le_three_exp hy
    have hpow0 : 0 ≤ t ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg ht.le _
    rw [norm_mul, Complex.norm_of_nonneg hpow0, Complex.norm_of_nonneg hK0]
    -- t^(Re w - 1) · t^(-1/2) = t^(Re w - 3/2) ≤ t^(-2) = (1/t)²
    have hcomb : t ^ (w.re - 1) * t ^ (-(1 / 2 : ℝ)) = t ^ (w.re - 1 + -(1 / 2 : ℝ)) :=
      (Real.rpow_add ht _ _).symm
    have hmono : t ^ (w.re - 1 + -(1 / 2 : ℝ)) ≤ t ^ (-(2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge ht hlt.le (by linarith)
    have hm2 : t ^ (-(2 : ℝ)) = (1 / t) ^ 2 := by
      rw [Real.rpow_neg ht.le, Real.rpow_two, one_div, inv_pow]
    have hA0 : 0 ≤ t ^ (w.re - 1 + -(1 / 2 : ℝ)) := Real.rpow_nonneg ht.le _
    have hfin := sq_mul_exp_neg_pi_le hy
    calc t ^ (w.re - 1) * (t ^ (-(1 / 2 : ℝ)) * (evenKernel 0 (1 / t) - 1))
        = t ^ (w.re - 1 + -(1 / 2 : ℝ)) * (evenKernel 0 (1 / t) - 1) := by
          rw [← mul_assoc, hcomb]
      _ ≤ (1 / t) ^ 2 * (3 * Real.exp (-π * (1 / t))) := by
          rw [← hm2]
          exact mul_le_mul hmono hK hK0 (Real.rpow_nonneg ht.le _)
      _ = 3 * ((1 / t) ^ 2 * Real.exp (-π * (1 / t))) := by ring
      _ ≤ 3 * (1 / 4) := by linarith
      _ ≤ 3 / 4 + 3 * Real.exp (-π * t) := by linarith
  · -- t = 1: f_modif 1 = 0.
    subst heq
    have h0 : (hurwitzEvenFEPair 0).f_modif 1 = 0 := by
      unfold f_modif
      simp
    rw [h0, norm_zero, mul_zero]
    have hind : 0 ≤ (Ioc (0 : ℝ) 1).indicator (fun _ => (3 / 4 : ℝ)) 1 :=
      indicator_nonneg (fun _ _ => by norm_num) _
    linarith
  · -- t > 1: cola theta directa.
    rw [f_modif_eq_on_Ioi_one hgt]
    have hK0 : 0 ≤ evenKernel 0 t - 1 := evenKernel₀_sub_one_nonneg ht
    have hK := evenKernel₀_sub_one_le_three_exp hgt.le
    have hcast : ((evenKernel 0 t : ℂ) - 1) = ((evenKernel 0 t - 1 : ℝ) : ℂ) := by push_cast; rfl
    rw [hcast, Complex.norm_of_nonneg hK0]
    have hp : t ^ (w.re - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hgt.le (by linarith)
    have hp0 : 0 ≤ t ^ (w.re - 1) := Real.rpow_nonneg ht.le _
    have hind : 0 ≤ (Ioc (0 : ℝ) 1).indicator (fun _ => (3 / 4 : ℝ)) t :=
      indicator_nonneg (fun _ _ => by norm_num) _
    calc t ^ (w.re - 1) * (evenKernel 0 t - 1) ≤ 1 * (3 * Real.exp (-π * t)) :=
          mul_le_mul hp hK hK0 zero_le_one
      _ ≤ _ := by linarith

/-- Paso 4. Cota de la integral de Mellin de f_modif. -/
theorem norm_mellin_f_modif_le {w : ℂ} (hw1 : -1 / 2 ≤ w.re) (hw2 : w.re ≤ 1) :
    ‖mellin (hurwitzEvenFEPair 0).f_modif w‖ ≤ 3 / 4 + 3 / π := by
  have hind_int : Integrable ((Ioc (0 : ℝ) 1).indicator (fun _ => (3 / 4 : ℝ))) :=
    (integrableOn_const (by simp)).integrable_indicator measurableSet_Ioc
  have hexp_int : IntegrableOn (fun t : ℝ => 3 * Real.exp (-π * t)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 Real.pi_pos).const_mul 3
  have hG_int : IntegrableOn (fun t : ℝ =>
      (Ioc (0 : ℝ) 1).indicator (fun _ => (3 / 4 : ℝ)) t + 3 * Real.exp (-π * t)) (Ioi 0) :=
    hind_int.integrableOn.add hexp_int
  have hbound : ∀ᵐ t : ℝ ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖(t : ℂ) ^ (w - 1) • (hurwitzEvenFEPair 0).f_modif t‖ ≤
        (Ioc (0 : ℝ) 1).indicator (fun _ => (3 / 4 : ℝ)) t + 3 * Real.exp (-π * t) :=
    ae_restrict_of_forall_mem measurableSet_Ioi
      (fun t ht => norm_mellin_integrand_le hw1 hw2 ht)
  have hle := norm_integral_le_of_norm_le hG_int hbound
  have hI1 : ∫ t in Ioi (0 : ℝ), (Ioc (0 : ℝ) 1).indicator (fun _ => (3 / 4 : ℝ)) t = 3 / 4 := by
    rw [setIntegral_indicator measurableSet_Ioc,
      inter_eq_right.mpr Ioc_subset_Ioi_self, setIntegral_const,
      Real.volume_real_Ioc_of_le zero_le_one]
    norm_num
  have hI2 : ∫ t in Ioi (0 : ℝ), 3 * Real.exp (-π * t) = 3 / π := by
    rw [integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr Real.pi_pos) 0]
    have h1 : Real.exp (-π * 0) = 1 := by simp
    rw [h1, neg_div_neg_eq]
    ring
  have hIG : ∫ t in Ioi (0 : ℝ),
      ((Ioc (0 : ℝ) 1).indicator (fun _ => (3 / 4 : ℝ)) t + 3 * Real.exp (-π * t)) =
        3 / 4 + 3 / π := by
    rw [integral_add hind_int.integrableOn hexp_int, hI1, hI2]
  unfold mellin
  rw [← hIG]
  exact hle

/-- Paso 5. La Cajita, sin hipótesis: ‖Λ₀(z)‖ ≤ 1 en todo leftoverRect. -/
theorem zeta₀_norm_le_one_on_leftoverRect :
    ∀ z ∈ leftoverRect, ‖completedRiemannZeta₀ z‖ ≤ 1 := by
  intro z hz
  obtain ⟨h1, h2, _⟩ := hz
  have hre : (z / 2).re = z.re / 2 := by simp
  have hb := norm_mellin_f_modif_le (w := z / 2) (by rw [hre]; linarith) (by rw [hre]; linarith)
  have hpi : 3 / π < 1 := (div_lt_one Real.pi_pos).mpr Real.pi_gt_three
  rw [completedRiemannZeta₀_eq_half_mellin, norm_div]
  have h2n : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2n, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- Corolario: ζ(s) ≠ 0 en el interior de la Cajita, sin hipótesis. -/
theorem cajita_zeta_ne_zero_unconditional :
    ∀ s ∈ leftoverInterior, riemannZeta s ≠ 0 :=
  (habitacion1_resolved_of_zeta₀_bound zeta₀_norm_le_one_on_leftoverRect).1

/-- Corolario: entireXi no se anula en la Cajita, sin hipótesis. -/
theorem cajita_entireXi_ne_zero_unconditional :
    ∀ z ∈ leftoverRect, entireXi z ≠ 0 :=
  (habitacion1_resolved_of_zeta₀_bound zeta₀_norm_le_one_on_leftoverRect).2

end RhG1Lean
