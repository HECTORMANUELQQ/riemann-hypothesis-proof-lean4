/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.

# Las orillas de las bahías (formalización de la rebanada y de las islas prohibidas)

Una **bahía** de una costura ξ = E + E♯ es una región acotada y conexa donde el reflejo gana
(‖E‖ < ‖E♯‖ adentro) y empata en la orilla (‖E‖ = ‖E♯‖ en la frontera).

* **La orilla cubre el círculo** (sin principio del argumento): si g es holomorfa en una región
  acotada y conexa U, continua hasta la orilla, con ‖g‖ < 1 adentro y ‖g‖ = 1 en la orilla, entonces
  g toma en la orilla **todos** los valores de módulo 1. (Aplicación abierta + compacidad: la imagen de U
  es abierta y cerrada en el disco, luego es todo el disco; la imagen de la clausura es compacta y
  contiene al disco cerrado; los puntos del círculo solo pueden venir de la orilla.)
* **Toda bahía toca a un huésped**: con g = E/E♯ y el valor −1, en la orilla de cada bahía hay un
  punto donde E + E♯ = ξ = 0.
* **Las islas delatan escapados**: si la clausura de la bahía está dentro del ala abierta, ese huésped
  está fuera de la recta.
* **Bajo la meta, cada bahía guarda su huésped en la pared**: si ξ no se anula en el ala abierta y la
  bahía vive en el ala cerrada, el huésped de su orilla está en Re s = 1/2 (el retroceso trae un huésped).
* **El polo apaga una costura que pasa por cero en s = 1**: si E(1) = 0, el reflejo gana en s = 1.
-/
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Complex.AbsMax
import RhG1Lean.RutaCostura

open Complex Set Metric Filter ComplexConjugate
open scoped Topology

namespace RhG1Lean

/-- Un conjunto acotado de ℂ no es todo ℂ. -/
theorem ne_univ_of_isBounded {U : Set ℂ} (hU : Bornology.IsBounded U) : U ≠ univ := by
  intro h
  obtain ⟨r, hr⟩ := (isBounded_iff_subset_closedBall (0 : ℂ)).mp hU
  have hmem : ((|r| + 1 : ℝ) : ℂ) ∈ closedBall (0 : ℂ) r := hr (h ▸ mem_univ _)
  rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] at hmem
  have : |r| + 1 ≤ |r| := by
    calc |r| + 1 = |(|r| + 1)| := (abs_of_pos (by positivity)).symm
      _ ≤ r := hmem
      _ ≤ |r| := le_abs_self r
  linarith

/-- Una región acotada no vacía de ℂ tiene orilla. -/
theorem frontier_nonempty_of_isBounded {U : Set ℂ} (hU : Bornology.IsBounded U) (hne : U.Nonempty) :
    (frontier U).Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty, ← isClopen_iff_frontier_eq_empty] at h
  exact ne_univ_of_isBounded hU (h.eq_univ hne)

/-- **La orilla cubre el círculo.** -/
theorem orilla_cubre_circulo {g : ℂ → ℂ} {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUb : Bornology.IsBounded U) (hne : U.Nonempty) (hd : DiffContOnCl ℂ g U)
    (hin : ∀ z ∈ U, ‖g z‖ < 1) (hfr : ∀ z ∈ frontier U, ‖g z‖ = 1) :
    ∀ w : ℂ, ‖w‖ = 1 → ∃ z ∈ frontier U, g z = w := by
  have hcomp : IsCompact (closure U) := hUb.isCompact_closure
  have himg : IsCompact (g '' closure U) := hcomp.image_of_continuousOn hd.continuousOn
  have hcl : IsClosed (g '' closure U) := himg.isClosed
  have hsub : closure (g '' U) ⊆ g '' closure U :=
    closure_minimal (image_mono subset_closure) hcl
  obtain ⟨z₀, hz₀⟩ := hne
  have hA : AnalyticOnNhd ℂ g U := hd.differentiableOn.analyticOnNhd hUo
  rcases hA.is_constant_or_isOpen hUc with ⟨c, hc⟩ | hopen
  · -- constante: imposible, adentro mide < 1 y en la orilla mide 1
    exfalso
    obtain ⟨z₁, hz₁⟩ := frontier_nonempty_of_isBounded hUb ⟨z₀, hz₀⟩
    have heq : EqOn g (fun _ => c) (closure U) :=
      EqOn.of_subset_closure (fun z hz => hc z hz) hd.continuousOn continuousOn_const subset_closure
        subset_rfl
    have h1 := hfr z₁ hz₁
    rw [heq (frontier_subset_closure hz₁)] at h1
    have h2 := hin z₀ hz₀
    rw [hc z₀ hz₀] at h2
    linarith
  · have hgU : IsOpen (g '' U) := hopen U subset_rfl hUo
    -- la imagen de U llena el disco abierto
    have hball : ball (0 : ℂ) 1 ⊆ g '' U := by
      refine (isPreconnected_ball (x := (0 : ℂ)) (r := 1)).subset_of_closure_inter_subset hgU ?_ ?_
      · exact ⟨g z₀, by rw [mem_ball_zero_iff]; exact hin z₀ hz₀, mem_image_of_mem g hz₀⟩
      · rintro w ⟨hw, hwb⟩
        obtain ⟨z, hz, rfl⟩ := hsub hw
        by_cases hzU : z ∈ U
        · exact mem_image_of_mem g hzU
        · exfalso
          have hzf : z ∈ frontier U := by rw [hUo.frontier_eq]; exact ⟨hz, hzU⟩
          rw [mem_ball_zero_iff, hfr z hzf] at hwb
          exact lt_irrefl _ hwb
    -- la imagen de la clausura contiene al disco cerrado
    have hcball : closedBall (0 : ℂ) 1 ⊆ g '' closure U := by
      rw [← closure_ball (0 : ℂ) one_ne_zero]
      exact (closure_mono hball).trans hsub
    intro w hw
    obtain ⟨z, hz, rfl⟩ := hcball (by rw [mem_closedBall, dist_zero_right, hw])
    refine ⟨z, ?_, rfl⟩
    rw [hUo.frontier_eq]
    refine ⟨hz, fun hzU => ?_⟩
    have := hin z hzU
    rw [hw] at this
    exact lt_irrefl _ this

/-- **Toda bahía toca a un huésped.** En la orilla de una bahía de la costura hay un punto donde la
luz directa y su reflejo se cancelan. -/
theorem bahia_toca_huesped {E : ℂ → ℂ} (hE : Differentiable ℂ E) {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsPreconnected U) (hUb : Bornology.IsBounded U) (hne : U.Nonempty)
    (hin : ∀ z ∈ U, ‖E z‖ < ‖reflejo E z‖) (hfr : ∀ z ∈ frontier U, ‖E z‖ = ‖reflejo E z‖) :
    ∃ z ∈ frontier U, E z + reflejo E z = 0 := by
  by_cases h0 : ∃ z ∈ frontier U, reflejo E z = 0
  · obtain ⟨z, hz, hz0⟩ := h0
    have hEz : E z = 0 := by
      have h := hfr z hz
      rw [hz0, norm_zero] at h
      exact norm_eq_zero.mp h
    exact ⟨z, hz, by rw [hEz, hz0, add_zero]⟩
  have h0' : ∀ z ∈ frontier U, reflejo E z ≠ 0 := fun z hz h => h0 ⟨z, hz, h⟩
  have hcl : ∀ z ∈ closure U, reflejo E z ≠ 0 := by
    intro z hz
    by_cases hzU : z ∈ U
    · intro h
      have := hin z hzU
      rw [h, norm_zero] at this
      exact absurd this (not_lt.mpr (norm_nonneg _))
    · exact h0' z (by rw [hUo.frontier_eq]; exact ⟨hz, hzU⟩)
  have hdz : ∀ z ∈ closure U, DifferentiableAt ℂ (fun z => E z / reflejo E z) z :=
    fun z hz => (hE z).div ((differentiable_reflejo hE) z) (hcl z hz)
  have hd : DiffContOnCl ℂ (fun z => E z / reflejo E z) U :=
    ⟨fun z hz => (hdz z (subset_closure hz)).differentiableWithinAt,
     fun z hz => (hdz z hz).continuousAt.continuousWithinAt⟩
  have hin' : ∀ z ∈ U, ‖E z / reflejo E z‖ < 1 := by
    intro z hz
    rw [norm_div, div_lt_one (norm_pos_iff.mpr (hcl z (subset_closure hz)))]
    exact hin z hz
  have hfr' : ∀ z ∈ frontier U, ‖E z / reflejo E z‖ = 1 := by
    intro z hz
    rw [norm_div, hfr z hz, div_self (norm_ne_zero_iff.mpr (h0' z hz))]
  obtain ⟨z, hz, hgz⟩ := orilla_cubre_circulo hUo hUc hUb hne hd hin' hfr' (-1) (by simp)
  refine ⟨z, hz, ?_⟩
  rw [div_eq_iff (h0' z hz)] at hgz
  linear_combination hgz

/-- Para una costura de ξ: en la orilla de cada bahía, ξ se anula. -/
theorem bahia_toca_huesped_xi {E : ℂ → ℂ} (hE : Differentiable ℂ E)
    (hxi : ∀ s, entireXi s = E s + reflejo E s) {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsPreconnected U) (hUb : Bornology.IsBounded U) (hne : U.Nonempty)
    (hin : ∀ z ∈ U, ‖E z‖ < ‖reflejo E z‖) (hfr : ∀ z ∈ frontier U, ‖E z‖ = ‖reflejo E z‖) :
    ∃ z ∈ frontier U, entireXi z = 0 := by
  obtain ⟨z, hz, h⟩ := bahia_toca_huesped hE hUo hUc hUb hne hin hfr
  exact ⟨z, hz, by rw [hxi z]; exact h⟩

/-- **Las islas delatan escapados.** Una bahía cuya clausura vive en el ala abierta obliga un cero de ξ
fuera de la recta. -/
theorem isla_delata_escapado {E : ℂ → ℂ} (hE : Differentiable ℂ E)
    (hxi : ∀ s, entireXi s = E s + reflejo E s) {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsPreconnected U) (hUb : Bornology.IsBounded U) (hne : U.Nonempty)
    (hin : ∀ z ∈ U, ‖E z‖ < ‖reflejo E z‖) (hfr : ∀ z ∈ frontier U, ‖E z‖ = ‖reflejo E z‖)
    (hala : closure U ⊆ {z : ℂ | 1 / 2 < z.re}) :
    ∃ z : ℂ, 1 / 2 < z.re ∧ entireXi z = 0 := by
  obtain ⟨z, hz, h⟩ := bahia_toca_huesped_xi hE hxi hUo hUc hUb hne hin hfr
  exact ⟨z, hala (frontier_subset_closure hz), h⟩

/-- **Bajo la meta no hay islas.** Si ξ no se anula en el ala abierta, ninguna bahía tiene su clausura
dentro del ala abierta. -/
theorem sin_islas {E : ℂ → ℂ} (hE : Differentiable ℂ E)
    (hxi : ∀ s, entireXi s = E s + reflejo E s) (hmeta : ∀ z : ℂ, 1 / 2 < z.re → entireXi z ≠ 0)
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U) (hUb : Bornology.IsBounded U)
    (hne : U.Nonempty) (hin : ∀ z ∈ U, ‖E z‖ < ‖reflejo E z‖)
    (hfr : ∀ z ∈ frontier U, ‖E z‖ = ‖reflejo E z‖) :
    ¬ closure U ⊆ {z : ℂ | 1 / 2 < z.re} := by
  intro hala
  obtain ⟨z, hz, h⟩ := isla_delata_escapado hE hxi hUo hUc hUb hne hin hfr hala
  exact hmeta z hz h

/-- **Bajo la meta, cada bahía guarda su huésped en la pared.** Si ξ no se anula en el ala abierta y
la bahía vive en el ala cerrada, en su tramo de pared hay un huésped (el retroceso trae un huésped). -/
theorem bahia_huesped_en_pared {E : ℂ → ℂ} (hE : Differentiable ℂ E)
    (hxi : ∀ s, entireXi s = E s + reflejo E s) (hmeta : ∀ z : ℂ, 1 / 2 < z.re → entireXi z ≠ 0)
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U) (hUb : Bornology.IsBounded U)
    (hne : U.Nonempty) (hin : ∀ z ∈ U, ‖E z‖ < ‖reflejo E z‖)
    (hfr : ∀ z ∈ frontier U, ‖E z‖ = ‖reflejo E z‖)
    (hala : closure U ⊆ {z : ℂ | 1 / 2 ≤ z.re}) :
    ∃ z ∈ frontier U, z.re = 1 / 2 ∧ entireXi z = 0 := by
  obtain ⟨z, hz, h⟩ := bahia_toca_huesped_xi hE hxi hUo hUc hUb hne hin hfr
  refine ⟨z, hz, ?_, h⟩
  have h1 : 1 / 2 ≤ z.re := hala (frontier_subset_closure hz)
  by_contra hne'
  exact hmeta z (lt_of_le_of_ne h1 (Ne.symm hne')) h

/-- **El polo apaga la costura**: si una costura de ξ vale 0 en s = 1, ahí el reflejo gana
(vale ξ(1) = 1/2). -/
theorem polo_apaga_costura {E : ℂ → ℂ} (hxi : ∀ s, entireXi s = E s + reflejo E s) (h1 : E 1 = 0) :
    ‖E 1‖ < ‖reflejo E 1‖ := by
  have h := hxi 1
  rw [entireXi_one, h1, zero_add] at h
  rw [h1, ← h]
  norm_num

end RhG1Lean
