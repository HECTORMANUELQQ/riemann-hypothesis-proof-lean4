/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.

# Cuatro frentes (Partida 4)

* **Por abajo · certificado de región**: si en una región acotada y conexa la luz directa no se apaga
  (E ≠ 0 en la clausura) y el reflejo no le gana en la orilla, entonces ξ no se anula adentro.
  Es la forma de certificar un tramo entero del edificio con una sola cuenta en su borde.
* **Por dentro · la costura inclinada**: E_α = (ξ + ξ′/α)/2 es una costura exacta de ξ, su reflejo es
  (ξ − ξ′/α)/2, y su balanza es ‖E_α‖² − ‖E_α♯‖² = Re(conj ξ · ξ′)/α: la luz gana justo donde la
  pendiente logarítmica de ξ empuja hacia afuera.
-/
import RhG1Lean.Bahias
import RhG1Lean.DeduccionesPapel
import RhG1Lean.DualCancellation

open Complex Set Filter ComplexConjugate
open scoped Topology

namespace RhG1Lean

/-- ξ no se anula en ningún abierto no vacío (si se anulara, se anularía en todo ℂ, y ξ(0) = 1/2). -/
theorem entireXi_not_eventually_zero (z : ℂ) : ¬ (entireXi =ᶠ[𝓝 z] 0) := by
  intro h
  have hA : AnalyticOnNhd ℂ entireXi univ :=
    differentiable_entireXi.differentiableOn.analyticOnNhd isOpen_univ
  have h0 := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ z) h
    (mem_univ 0)
  rw [entireXi_zero] at h0
  norm_num at h0

/-- **Certificado de región (por abajo).** -/
theorem certificado_sin_escapados {E : ℂ → ℂ} (hE : Differentiable ℂ E)
    (hxi : ∀ s, entireXi s = E s + reflejo E s) {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsPreconnected U) (hUb : Bornology.IsBounded U)
    (hluz : ∀ z ∈ closure U, E z ≠ 0) (hfr : ∀ z ∈ frontier U, ‖reflejo E z‖ ≤ ‖E z‖) :
    ∀ z ∈ U, entireXi z ≠ 0 := by
  set q : ℂ → ℂ := fun z => reflejo E z / E z with hq
  have hdz : ∀ z ∈ closure U, DifferentiableAt ℂ q z :=
    fun z hz => ((differentiable_reflejo hE) z).div (hE z) (hluz z hz)
  have hd : DiffContOnCl ℂ q U :=
    ⟨fun z hz => (hdz z (subset_closure hz)).differentiableWithinAt,
     fun z hz => (hdz z hz).continuousAt.continuousWithinAt⟩
  have hC : ∀ z ∈ frontier U, ‖q z‖ ≤ 1 := by
    intro z hz
    have hEz := hluz z (frontier_subset_closure hz)
    simp only [hq, norm_div]
    exact (div_le_one (norm_pos_iff.mpr hEz)).mpr (hfr z hz)
  have hle : ∀ z ∈ U, ‖q z‖ ≤ 1 := fun z hz =>
    Complex.norm_le_of_forall_mem_frontier_norm_le hUb hd hC (subset_closure hz)
  intro z hz hzero
  have hEz : E z ≠ 0 := hluz z (subset_closure hz)
  have hqz : q z = -1 := by
    have h := hxi z
    rw [hzero] at h
    have hr : reflejo E z = -E z := by linear_combination -h
    simp only [hq, hr, neg_div, div_self hEz]
  have hmax : IsMaxOn (norm ∘ q) U z := by
    refine isMaxOn_iff.mpr fun x hx => ?_
    show ‖q x‖ ≤ ‖q z‖
    rw [hqz, norm_neg, norm_one]
    exact hle x hx
  have heq := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hUc hUo hd.differentiableOn hz hmax
  -- q = −1 en todo U, luego ξ = E (1 + q) = 0 en todo U: imposible
  apply entireXi_not_eventually_zero z
  filter_upwards [hUo.mem_nhds hz] with x hx
  have h1 : q x = -1 := by simpa [hqz] using heq hx
  have hEx : E x ≠ 0 := hluz x (subset_closure hx)
  have hr : reflejo E x = -E x := by
    simp only [hq] at h1
    rw [div_eq_iff hEx] at h1
    linear_combination h1
  rw [hxi x, hr]
  simp

/-- La derivada de ξ respeta la conjugación. -/
theorem deriv_entireXi_conj (z : ℂ) : deriv entireXi (conj z) = conj (deriv entireXi z) := by
  have h : HasDerivAt (conj ∘ entireXi ∘ conj) (conj (deriv entireXi z)) (conj z) :=
    (differentiable_entireXi z).hasDerivAt.conj_conj
  have heq : (conj ∘ entireXi ∘ conj) = entireXi := by
    funext w
    simp [Function.comp, entireXi_conj]
  rw [heq] at h
  exact h.deriv

/-- La costura inclinada E_α = (ξ + ξ′/α)/2. -/
noncomputable def costuraInclinada (α : ℝ) (s : ℂ) : ℂ := (entireXi s + deriv entireXi s / α) / 2

/-- Su reflejo es (ξ − ξ′/α)/2. -/
theorem reflejo_costuraInclinada (α : ℝ) (s : ℂ) :
    reflejo (costuraInclinada α) s = (entireXi s - deriv entireXi s / α) / 2 := by
  unfold reflejo costuraInclinada
  have h1 : (1 : ℂ) - conj s = conj (1 - s) := by simp [map_sub]
  rw [h1, entireXi_conj, deriv_entireXi_conj, map_div₀, map_add, map_div₀, Complex.conj_conj,
    Complex.conj_conj, Complex.conj_ofReal, entireXi_one_sub, deriv_entireXi_one_sub]
  simp only [map_ofNat]
  ring

/-- **La costura inclinada es una costura exacta de ξ.** -/
theorem costuraInclinada_es_costura (α : ℝ) (s : ℂ) :
    entireXi s = costuraInclinada α s + reflejo (costuraInclinada α) s := by
  rw [reflejo_costuraInclinada]
  unfold costuraInclinada
  ring

/-- La costura inclinada es entera. -/
theorem differentiable_costuraInclinada (α : ℝ) : Differentiable ℂ (costuraInclinada α) := by
  have hd : Differentiable ℂ (deriv entireXi) := by
    intro z
    have hA : AnalyticOnNhd ℂ entireXi univ :=
      differentiable_entireXi.differentiableOn.analyticOnNhd isOpen_univ
    exact (hA.deriv z (mem_univ z)).differentiableAt
  intro z
  unfold costuraInclinada
  exact ((differentiable_entireXi z).add ((hd z).div_const _)).div_const _

/-- **Balanza de la costura inclinada.** -/
theorem balanza_costuraInclinada (α : ℝ) (s : ℂ) :
    ‖costuraInclinada α s‖ ^ 2 - ‖reflejo (costuraInclinada α) s‖ ^ 2
      = (conj (entireXi s) * deriv entireXi s).re / α := by
  rw [costura_balanza_xi (costuraInclinada_es_costura α s), reflejo_costuraInclinada]
  unfold costuraInclinada
  have h : (entireXi s + deriv entireXi s / ↑α) / 2 - (entireXi s - deriv entireXi s / ↑α) / 2
      = deriv entireXi s / ↑α := by ring
  rw [h, mul_div_assoc', Complex.div_ofReal_re]

/-- Donde la pendiente de ξ empuja hacia afuera (Re(conj ξ · ξ′) > 0) y α > 0, la luz inclinada gana. -/
theorem inclinada_gana {α : ℝ} (hα : 0 < α) {s : ℂ} (h : 0 < (conj (entireXi s) * deriv entireXi s).re) :
    ‖reflejo (costuraInclinada α) s‖ < ‖costuraInclinada α s‖ := by
  have hb := balanza_costuraInclinada α s
  have hpos : 0 < ‖costuraInclinada α s‖ ^ 2 - ‖reflejo (costuraInclinada α) s‖ ^ 2 := by
    rw [hb]; exact div_pos h hα
  have h2 : ‖reflejo (costuraInclinada α) s‖ ^ 2 < ‖costuraInclinada α s‖ ^ 2 := by linarith
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h2

end RhG1Lean
