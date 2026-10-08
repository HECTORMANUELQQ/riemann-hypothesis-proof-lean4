/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.

# Las costuras de los cimientos son costuras exactas de ξ (pendiente desde la Partida 1)

Se corta la viga de los cimientos (el núcleo de theta modificado f_modif) en la ventana redonda con un
peso w que cumple el espejo w(1/x) = 1 − w(x) (0 ≤ w ≤ 1, medible):

    E_w(s) = 1/4 + s(s − 1)/4 · M[f_modif · w](s/2).

* **Costura exacta**: ξ(s) = E_w(s) + E_w♯(s), con E_w♯(s) = conj(E_w(1 − conj s)) = E_w(1 − s).
* **Sin inclinación** (la causa de la Partida 1): el reflejo de la costura con peso w es la costura con
  el peso complementario 1 − w: E_w(1 − s) = 1/4 + s(s − 1)/4 · M[f_modif · (1 − w)](s/2).
* **Entera**: E_w es diferenciable en todo ℂ.
* Casos concretos: el **corte duro de Riemann** (1 si x > 1, 1/2 si x = 1, 0 si no) y el **corte suave**
  x²/(1 + x²) (k = 2, el medido en las partidas).
-/
import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import RhG1Lean.CajitaMellinRepresentation
import RhG1Lean.RutaCostura

open Complex Real Set MeasureTheory HurwitzZeta Filter Asymptotics ComplexConjugate
open scoped Topology

namespace RhG1Lean

/-- La viga de los cimientos: el núcleo de theta modificado. -/
noncomputable abbrev fm : ℝ → ℂ := (hurwitzEvenFEPair 0).f_modif

/-- Para el par par de Hurwitz en a = 0, las dos vigas modificadas coinciden. -/
theorem g_modif_eq_fm : (hurwitzEvenFEPair 0).g_modif = fm := by
  funext x
  simp [WeakFEPair.f_modif, WeakFEPair.g_modif, hurwitzEvenFEPair, evenKernel_eq_cosKernel_of_zero]

/-- **El espejo de la viga**: fm(1/x) = √x · fm(x). -/
theorem fm_inv {x : ℝ} (hx : 0 < x) : fm x⁻¹ = (x : ℂ) ^ (1 / 2 : ℂ) * fm x := by
  have h := (hurwitzEvenFEPair 0).hf_modif_FE x hx
  rw [one_div] at h
  rw [show fm x⁻¹ = (hurwitzEvenFEPair 0).f_modif x⁻¹ from rfl, h, g_modif_eq_fm]
  simp only [hurwitzEvenFEPair, one_mul, smul_eq_mul]
  rw [ofReal_cpow hx.le]
  push_cast
  ring

theorem fm_top (r : ℝ) : fm =O[atTop] (· ^ r) :=
  (WeakFEPair.isStrongFEPair_toStrongFEPair (hurwitzEvenFEPair 0)).hf_top r

theorem fm_zero (r : ℝ) : fm =O[𝓝[>] 0] (· ^ r) :=
  (WeakFEPair.isStrongFEPair_toStrongFEPair (hurwitzEvenFEPair 0)).hf_zero r

theorem mellinConvergent_fm (s : ℂ) : MellinConvergent fm s :=
  ((WeakFEPair.isStrongFEPair_toStrongFEPair (hurwitzEvenFEPair 0)).hasMellin s).1

/-- Un corte válido de la viga: medible, entre 0 y 1, y con el espejo w(1/x) = 1 − w(x). -/
structure Corte (w : ℝ → ℝ) : Prop where
  medible : Measurable w
  entre : ∀ x, 0 ≤ w x ∧ w x ≤ 1
  espejo : ∀ x, 0 < x → w x⁻¹ = 1 - w x

/-- El peso complementario también es un corte. -/
theorem Corte.complemento {w : ℝ → ℝ} (h : Corte w) : Corte (fun x => 1 - w x) :=
  ⟨measurable_const.sub h.medible,
   fun x => ⟨by linarith [(h.entre x).2], by linarith [(h.entre x).1]⟩,
   fun x hx => by simp [h.espejo x hx]⟩

theorem mellinConvergent_corte {w : ℝ → ℝ} (hw : Corte w) (s : ℂ) :
    MellinConvergent (fun t => fm t * (w t : ℂ)) s := by
  have h := mellinConvergent_fm s
  unfold MellinConvergent at h ⊢
  have hmeas : AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ (s - 1) • (fm t * (w t : ℂ)))
      (volume.restrict (Ioi 0)) := by
    have h1 := h.aestronglyMeasurable.mul
      ((Complex.measurable_ofReal.comp hw.medible).aestronglyMeasurable (μ := volume.restrict (Ioi 0)))
    refine h1.congr (Eventually.of_forall fun t => ?_)
    simp only [Pi.mul_apply, Function.comp, smul_eq_mul]
    ring
  refine MeasureTheory.Integrable.mono h hmeas (Eventually.of_forall fun t => ?_)
  simp only [smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hw.entre t).1]
  have := (hw.entre t).2
  have h0 := norm_nonneg ((t : ℂ) ^ (s - 1))
  have h1 := norm_nonneg (fm t)
  nlinarith [mul_nonneg h0 h1]

/-- Las dos mitades suman la viga entera. -/
theorem mellin_corte_add {w : ℝ → ℝ} (hw : Corte w) (s : ℂ) :
    mellin (fun t => fm t * (w t : ℂ)) s + mellin (fun t => fm t * ((1 - w t : ℝ) : ℂ)) s
      = mellin fm s := by
  unfold mellin
  rw [← integral_add (mellinConvergent_corte hw s) (mellinConvergent_corte hw.complemento s)]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  simp only [smul_eq_mul]
  push_cast
  ring

/-- **Sin inclinación**: el espejo convierte el peso w en el peso complementario. -/
theorem mellin_corte_espejo {w : ℝ → ℝ} (hw : Corte w) (s : ℂ) :
    mellin (fun t => fm t * (w t : ℂ)) ((1 - s) / 2)
      = mellin (fun t => fm t * ((1 - w t : ℝ) : ℂ)) (s / 2) := by
  have h1 : (1 - s) / 2 = -((s - 1) / 2) := by ring
  rw [h1, ← mellin_comp_inv (fun t => fm t * (w t : ℂ))]
  have h2 : mellin (fun t : ℝ => fm t⁻¹ * (w t⁻¹ : ℂ)) ((s - 1) / 2)
      = mellin (fun t : ℝ => (t : ℂ) ^ (1 / 2 : ℂ) • (fm t * ((1 - w t : ℝ) : ℂ))) ((s - 1) / 2) := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    simp only [smul_eq_mul]
    rw [fm_inv ht, hw.espejo t ht]
    ring
  rw [show (fun t : ℝ => (fun t => fm t * (w t : ℂ)) t⁻¹) = fun t : ℝ => fm t⁻¹ * (w t⁻¹ : ℂ) from rfl,
    h2, mellin_cpow_smul]
  congr 1
  ring

/-- **La costura de los cimientos** con corte w. -/
noncomputable def costuraCimientos (w : ℝ → ℝ) (s : ℂ) : ℂ :=
  1 / 4 + s * (s - 1) / 4 * mellin (fun t => fm t * (w t : ℂ)) (s / 2)

/-- **Sin inclinación**: la mitad reflejada es la misma integral con el peso complementario. -/
theorem costuraCimientos_one_sub {w : ℝ → ℝ} (hw : Corte w) (s : ℂ) :
    costuraCimientos w (1 - s)
      = 1 / 4 + s * (s - 1) / 4 * mellin (fun t => fm t * ((1 - w t : ℝ) : ℂ)) (s / 2) := by
  unfold costuraCimientos
  rw [mellin_corte_espejo hw s]
  ring

/-- ξ es la suma de la costura y su mitad reflejada. -/
theorem entireXi_eq_costuraCimientos_add {w : ℝ → ℝ} (hw : Corte w) (s : ℂ) :
    entireXi s = costuraCimientos w s + costuraCimientos w (1 - s) := by
  rw [costuraCimientos_one_sub hw]
  unfold costuraCimientos entireXi
  rw [completedRiemannZeta₀_eq_half_mellin, ← mellin_corte_add hw (s / 2)]
  ring

/-- La viga de los cimientos toma valores reales. -/
theorem conj_fm (t : ℝ) : conj (fm t) = fm t := by
  simp only [fm, WeakFEPair.f_modif, hurwitzEvenFEPair, Pi.add_apply, Set.indicator_apply]
  split_ifs <;> simp [map_sub]

/-- La transformada de Mellin de una función real conmuta con la conjugación. -/
theorem conj_mellin_real {F : ℝ → ℂ} (hF : ∀ t, conj (F t) = F t) (s : ℂ) :
    conj (mellin F (conj s)) = mellin F s := by
  unfold mellin
  rw [← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  simp only [smul_eq_mul, map_mul, hF]
  congr 1
  have harg : (t : ℂ).arg ≠ π := by
    rw [arg_ofReal_of_nonneg (le_of_lt ht)]; exact Real.pi_pos.ne
  have h1 : conj s - 1 = conj (s - 1) := by simp [map_sub]
  rw [h1, cpow_conj _ _ harg, Complex.conj_ofReal, Complex.conj_conj]

theorem conj_costuraCimientos (w : ℝ → ℝ) (s : ℂ) :
    conj (costuraCimientos w (conj s)) = costuraCimientos w s := by
  unfold costuraCimientos
  have hF : ∀ t, conj (fm t * (w t : ℂ)) = fm t * (w t : ℂ) := fun t => by
    rw [map_mul, conj_fm, Complex.conj_ofReal]
  have hs2 : conj s / 2 = conj (s / 2) := by rw [map_div₀, map_ofNat]
  simp only [map_add, map_mul, map_div₀, map_sub, map_one, map_ofNat, Complex.conj_conj]
  rw [hs2, conj_mellin_real hF]

/-- El reflejo de la costura de los cimientos es su mitad en 1 − s. -/
theorem reflejo_costuraCimientos (w : ℝ → ℝ) (s : ℂ) :
    reflejo (costuraCimientos w) s = costuraCimientos w (1 - s) := by
  unfold reflejo
  have h : (1 : ℂ) - conj s = conj (1 - s) := by simp [map_sub]
  rw [h, conj_costuraCimientos]

/-- **La costura de los cimientos es una costura exacta de ξ.** -/
theorem costuraCimientos_es_costura {w : ℝ → ℝ} (hw : Corte w) (s : ℂ) :
    entireXi s = costuraCimientos w s + reflejo (costuraCimientos w) s := by
  rw [reflejo_costuraCimientos]
  exact entireXi_eq_costuraCimientos_add hw s

/-- **La costura de los cimientos es entera.** -/
theorem differentiable_costuraCimientos {w : ℝ → ℝ} (hw : Corte w) :
    Differentiable ℂ (costuraCimientos w) := by
  have hM : Differentiable ℂ (mellin (fun t => fm t * (w t : ℂ))) := by
    intro s
    have hfc : LocallyIntegrableOn (fun t => fm t * (w t : ℂ)) (Ioi 0) := by
      have h := mellinConvergent_corte hw 1
      unfold MellinConvergent at h
      simp only [sub_self, cpow_zero, one_smul] at h
      exact h.locallyIntegrableOn
    have hbound : (fun t => fm t * (w t : ℂ)) =O[⊤] fm := by
      refine IsBigO.of_bound 1 (Eventually.of_forall fun t => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw.entre t).1, one_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hw.entre t).2
    obtain ⟨a, ha⟩ := exists_gt s.re
    obtain ⟨b, hb⟩ := exists_lt s.re
    exact mellin_differentiableAt_of_isBigO_rpow hfc ((hbound.mono le_top).trans (fm_top (-a))) ha
      ((hbound.mono le_top).trans (fm_zero (-b))) hb
  intro s
  have hdiv : DifferentiableAt ℂ (fun z : ℂ => z / 2) s := differentiableAt_id.div_const (2 : ℂ)
  have h1 : DifferentiableAt ℂ (fun z : ℂ => mellin (fun t => fm t * (w t : ℂ)) (z / 2)) s :=
    DifferentiableAt.comp (g := mellin (fun t => fm t * (w t : ℂ))) s (hM (s / 2)) hdiv
  have h2 : DifferentiableAt ℂ (fun z : ℂ => z * (z - 1) / 4) s := by fun_prop
  exact (differentiableAt_const _).add (h2.mul h1)

/-- **El corte duro de Riemann**: 1 arriba de la ventana redonda, 1/2 en ella, 0 abajo. -/
noncomputable def corteDuro (x : ℝ) : ℝ := if 1 < x then 1 else if x = 1 then 1 / 2 else 0

theorem corteDuro_corte : Corte corteDuro := by
  refine ⟨?_, ?_, ?_⟩
  · exact Measurable.ite measurableSet_Ioi measurable_const
      (Measurable.ite (measurableSet_singleton 1) measurable_const measurable_const)
  · intro x; unfold corteDuro; split_ifs <;> norm_num
  · intro x hx
    unfold corteDuro
    rcases lt_trichotomy x 1 with h | rfl | h
    · have h1 : 1 < x⁻¹ := one_lt_inv_iff₀.mpr ⟨hx, h⟩
      simp [h1, not_lt.mpr h.le, h.ne]
    · norm_num
    · have h1 : x⁻¹ < 1 := inv_lt_one_of_one_lt₀ h
      simp [h, not_lt.mpr h1.le, h1.ne]

/-- **El corte suave k = 2**: x²/(1 + x²). -/
noncomputable def corteSuave (x : ℝ) : ℝ := x ^ 2 / (1 + x ^ 2)

theorem corteSuave_corte : Corte corteSuave := by
  refine ⟨?_, ?_, ?_⟩
  · exact (Continuous.div (by fun_prop) (by fun_prop) (fun x => by positivity)).measurable
  · intro x
    unfold corteSuave
    have hp : 0 < 1 + x ^ 2 := by positivity
    exact ⟨div_nonneg (sq_nonneg x) hp.le, (div_le_one hp).mpr (by linarith)⟩
  · intro x hx
    unfold corteSuave
    have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx.ne'
    have hp : 1 + x ^ 2 ≠ 0 := by positivity
    field_simp
    ring

/-- La costura del corte duro de Riemann es una costura exacta de ξ, y es entera. -/
theorem costura_riemann_exacta (s : ℂ) :
    entireXi s = costuraCimientos corteDuro s + reflejo (costuraCimientos corteDuro) s :=
  costuraCimientos_es_costura corteDuro_corte s

/-- La costura del corte suave (k = 2) es una costura exacta de ξ, y es entera. -/
theorem costura_suave_exacta (s : ℂ) :
    entireXi s = costuraCimientos corteSuave s + reflejo (costuraCimientos corteSuave) s :=
  costuraCimientos_es_costura corteSuave_corte s

end RhG1Lean
