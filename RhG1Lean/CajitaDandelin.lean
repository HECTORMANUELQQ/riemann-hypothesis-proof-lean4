/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.

# Lo cercano domina lo lejano: ‖Λ₀(σ + it)‖ ≤ ‖Λ₀(σ)‖ (incondicional)

f_modif ≥ 0 en (0, ∞) (la serie theta y su reflejo por x ↦ 1/x son positivos). Por eso el
módulo del integrando de Mellin t^{w-1}·f_modif(t) sólo depende de Re w, y

    ‖mellin f_modif w‖ ≤ ∫ ‖t^{w-1} f_modif t‖ = mellin f_modif (Re w)      (real, ≥ 0).

Consecuencia: en cada recta vertical el máximo de ‖Λ₀‖ está sobre el eje real (t = 0), a
cualquier altura. El problema bidimensional de la Cajita se reduce al segmento real: una cota
‖Λ₀(σ)‖ ≤ B en σ ∈ [a, b] da ‖Λ₀‖ ≤ B en toda la franja a ≤ Re ≤ b, y el óvalo de Cassini
‖z(z-1)‖·B < 1 queda libre de ceros de ξ. (Numéricamente B = Λ₀(-1) = Λ₀(2) ≈ 0.0236.)
No se usa integrabilidad: basta `norm_integral_le_integral_norm`.
-/
import RhG1Lean.CajitaUnconditional
import RhG1Lean.XiEntire

open Complex Real Set MeasureTheory HurwitzZeta WeakFEPair

namespace RhG1Lean

/-- f_modif es real y no negativa en (0, ∞): f_modif t = ‖f_modif t‖. -/
theorem f_modif_eq_norm {t : ℝ} (ht : 0 < t) :
    (hurwitzEvenFEPair 0).f_modif t = ((‖(hurwitzEvenFEPair 0).f_modif t‖ : ℝ) : ℂ) := by
  rcases lt_trichotomy t 1 with hlt | heq | hgt
  · have hmem : t ∈ Ioo (0 : ℝ) 1 := ⟨ht, hlt⟩
    have hy : 0 < 1 / t := by positivity
    have hK0 : 0 ≤ evenKernel 0 (1 / t) - 1 := evenKernel₀_sub_one_nonneg hy
    have hp0 : 0 ≤ t ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg ht.le _
    rw [f_modif_eq_reflected_on_Ioo hmem, ← Complex.ofReal_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp0 hK0)]
  · subst heq
    have h0 : (hurwitzEvenFEPair 0).f_modif 1 = 0 := by
      unfold f_modif
      simp
    rw [h0, norm_zero, Complex.ofReal_zero]
  · have hK0 : 0 ≤ evenKernel 0 t - 1 := evenKernel₀_sub_one_nonneg ht
    have hcast : ((evenKernel 0 t : ℂ) - 1) = ((evenKernel 0 t - 1 : ℝ) : ℂ) := by push_cast; rfl
    rw [f_modif_eq_on_Ioi_one hgt, hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hK0]

/-- **El eje real domina.** ‖mellin f_modif w‖ ≤ ‖mellin f_modif (Re w)‖, para todo w. -/
theorem norm_mellin_f_modif_le_re (w : ℂ) :
    ‖mellin (hurwitzEvenFEPair 0).f_modif w‖ ≤
      ‖mellin (hurwitzEvenFEPair 0).f_modif (w.re : ℂ)‖ := by
  set F := (hurwitzEvenFEPair 0).f_modif with hF
  -- h t = t^{Re w - 1}·‖F t‖ (real, ≥ 0)
  set h : ℝ → ℝ := fun t => t ^ (w.re - 1) * ‖F t‖ with hh
  have hnorm : ∀ t ∈ Ioi (0 : ℝ), ‖(t : ℂ) ^ (w - 1) • F t‖ = h t := by
    intro t ht
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
    simp [hh]
  have hreal : ∀ t ∈ Ioi (0 : ℝ), (t : ℂ) ^ ((w.re : ℂ) - 1) • F t = ((h t : ℝ) : ℂ) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have hFt := f_modif_eq_norm ht0
    rw [← hF] at hFt
    rw [smul_eq_mul, hFt]
    have hc : ((w.re : ℂ) - 1) = ((w.re - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [hc, ← Complex.ofReal_cpow ht0.le, ← Complex.ofReal_mul]
  have hh0 : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ h t := fun t ht =>
    mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (norm_nonneg _)
  have h1 : ‖mellin F w‖ ≤ ∫ t in Ioi (0 : ℝ), h t := by
    unfold mellin
    calc ‖∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (w - 1) • F t‖
        ≤ ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (w - 1) • F t‖ := norm_integral_le_integral_norm _
      _ = ∫ t in Ioi (0 : ℝ), h t := setIntegral_congr_fun measurableSet_Ioi hnorm
  have h2 : mellin F (w.re : ℂ) = ((∫ t in Ioi (0 : ℝ), h t : ℝ) : ℂ) := by
    unfold mellin
    rw [setIntegral_congr_fun measurableSet_Ioi hreal, integral_complex_ofReal]
  have h3 : 0 ≤ ∫ t in Ioi (0 : ℝ), h t := setIntegral_nonneg measurableSet_Ioi hh0
  rw [h2, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h3]
  exact h1

/-- **Lo cercano domina lo lejano.** ‖Λ₀(σ + it)‖ ≤ ‖Λ₀(σ)‖ para todo z, a cualquier altura. -/
theorem norm_completedRiemannZeta₀_le_re (z : ℂ) :
    ‖completedRiemannZeta₀ z‖ ≤ ‖completedRiemannZeta₀ (z.re : ℂ)‖ := by
  rw [completedRiemannZeta₀_eq_half_mellin, completedRiemannZeta₀_eq_half_mellin, norm_div,
    norm_div]
  have hre : (((z / 2).re : ℝ) : ℂ) = (z.re : ℂ) / 2 := by
    have : (z / 2).re = z.re / 2 := by simp
    rw [this]; push_cast; ring
  have hb := norm_mellin_f_modif_le_re (z / 2)
  rw [hre] at hb
  exact div_le_div_of_nonneg_right hb (norm_nonneg _)

/-- **Reducción al segmento real.** Si ‖Λ₀(σ)‖ ≤ B para σ ∈ [a, b], entonces en la franja
a ≤ Re z ≤ b el óvalo ‖z(z-1)‖·B < 1 es libre de ceros de ξ, a cualquier altura. -/
theorem entireXi_ne_zero_of_real_segment_bound {a b B : ℝ}
    (hB : ∀ σ : ℝ, a ≤ σ → σ ≤ b → ‖completedRiemannZeta₀ (σ : ℂ)‖ ≤ B)
    {z : ℂ} (h1 : a ≤ z.re) (h2 : z.re ≤ b) (h : ‖z * (z - 1)‖ * B < 1) :
    entireXi z ≠ 0 := by
  have hL : ‖completedRiemannZeta₀ z‖ ≤ B :=
    (norm_completedRiemannZeta₀_le_re z).trans (hB z.re h1 h2)
  apply entireXi_ne_zero_of_sub_half_lt
  have heq : entireXi z - 1 / 2 = (z * (z - 1) / 2) * completedRiemannZeta₀ z := by
    unfold entireXi; ring
  rw [heq, norm_mul, norm_div]
  have h2n : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2n]
  calc ‖z * (z - 1)‖ / 2 * ‖completedRiemannZeta₀ z‖
      ≤ ‖z * (z - 1)‖ / 2 * B := mul_le_mul_of_nonneg_left hL (by positivity)
    _ = (‖z * (z - 1)‖ * B) / 2 := by ring
    _ < 1 / 2 := by linarith

end RhG1Lean
