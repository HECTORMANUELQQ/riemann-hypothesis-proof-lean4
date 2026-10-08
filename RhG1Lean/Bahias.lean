/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.

# El mapa de bahías de una costura (Partida 2)

Una costura parte a ξ en luz directa y reflejo, ξ = E + E♯ con E♯(s) = conj (E (1 - conj s)).

* **Balanza de la costura**: ‖e‖² − ‖f‖² = Re((e − f)·conj(e + f)).
* **La mitad más un giro**: toda costura es ξ/2 + h; su balanza es 2·Re(conj ξ · h).
* **Los huéspedes viven en el empate**: si E + E♯ = 0 entonces ‖E‖ = ‖E♯‖. Donde una de las
  dos luces le gana a la otra no puede haber un huésped.
* **Cada bahía contiene un apagón**: si en una región acotada el reflejo no le gana a la luz en
  el borde pero sí le gana adentro, la luz directa E se apaga en algún punto de la región
  (principio del máximo para E♯/E).
* **La rosa de la dominancia**: si en un punto de la pared ‖q‖ = 1 y a su derecha ‖q‖ ≤ 1,
  entonces Re(q′·conj q) ≤ 0. Es la rapidez angular de q a lo largo de la pared: la fase del
  cociente no sube, la rosa de la luz directa no retrocede.
-/
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import RhG1Lean.RutaCostura

open Complex Set Filter ComplexConjugate
open scoped Topology

namespace RhG1Lean

/-- **Balanza de una costura.** -/
theorem balanza_costura (e f : ℂ) : ‖e‖ ^ 2 - ‖f‖ ^ 2 = ((e - f) * conj (e + f)).re := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im]
  ring

/-- **La mitad más un giro.** Si x = e + f (por ejemplo ξ = E + E♯), la balanza es Re(conj x·(e − f)),
es decir 2·Re(conj ξ · h) con h = (E − E♯)/2. -/
theorem costura_balanza_xi {x e f : ℂ} (hx : x = e + f) :
    ‖e‖ ^ 2 - ‖f‖ ^ 2 = (conj x * (e - f)).re := by
  rw [balanza_costura, ← hx]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im]
  ring

/-- La misma identidad escrita con la mitad y el giro: ‖a/2 + h‖² − ‖a/2 − h‖² = 2·Re(conj a · h). -/
theorem mitad_giro (a h : ℂ) : ‖a / 2 + h‖ ^ 2 - ‖a / 2 - h‖ ^ 2 = 2 * (conj a * h).re := by
  rw [costura_balanza_xi (show a = a / 2 + h + (a / 2 - h) by ring)]
  have h2 : a / 2 + h - (a / 2 - h) = 2 * h := by ring
  rw [h2]
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.re_ofNat,
    Complex.im_ofNat]
  ring

/-- **Los huéspedes viven en el empate.** -/
theorem huesped_en_empate {r p : ℂ} (h : r + p = 0) : ‖r‖ = ‖p‖ := by
  have hr : r = -p := by linear_combination h
  rw [hr, norm_neg]

/-- Donde la luz directa y su reflejo no empatan, ξ no se anula. -/
theorem entireXi_ne_zero_fuera_del_empate {E : ℂ → ℂ}
    (hxi : ∀ s, entireXi s = E s + reflejo E s) {s : ℂ} (h : ‖E s‖ ≠ ‖reflejo E s‖) :
    entireXi s ≠ 0 := by
  rw [hxi s]
  exact fun h0 => h (huesped_en_empate h0)

/-- **Cada bahía contiene un apagón.** Si en una región acotada U el reflejo no le gana a la luz
en el borde, pero sí le gana en un punto de adentro, entonces la luz directa E se apaga en la
clausura de U. -/
theorem bahia_contiene_apagon {E : ℂ → ℂ} (hE : Differentiable ℂ E) {U : Set ℂ}
    (hU : Bornology.IsBounded U) (hfr : ∀ z ∈ frontier U, ‖reflejo E z‖ ≤ ‖E z‖)
    {z : ℂ} (hz : z ∈ U) (hgana : ‖E z‖ < ‖reflejo E z‖) :
    ∃ w ∈ closure U, E w = 0 := by
  by_contra hno
  have hne : ∀ w ∈ closure U, E w ≠ 0 := fun w hw h0 => hno ⟨w, hw, h0⟩
  have hd : ∀ w ∈ closure U, DifferentiableAt ℂ (fun w => reflejo E w / E w) w :=
    fun w hw => ((differentiable_reflejo hE) w).div (hE w) (hne w hw)
  have hdc : DiffContOnCl ℂ (fun w => reflejo E w / E w) U :=
    ⟨fun w hw => (hd w (subset_closure hw)).differentiableWithinAt,
     fun w hw => (hd w hw).continuousAt.continuousWithinAt⟩
  have hC : ∀ w ∈ frontier U, ‖reflejo E w / E w‖ ≤ 1 := by
    intro w hw
    have hEw : E w ≠ 0 := hne w (frontier_subset_closure hw)
    rw [norm_div]
    exact (div_le_one (norm_pos_iff.mpr hEw)).mpr (hfr w hw)
  have hle := Complex.norm_le_of_forall_mem_frontier_norm_le hU hdc hC (subset_closure hz)
  have hEz : E z ≠ 0 := hne z (subset_closure hz)
  rw [norm_div, div_le_one (norm_pos_iff.mpr hEz)] at hle
  exact absurd hle (not_le.mpr hgana)

/-- Si una función real tiene derivada en 0 y a la derecha de 0 no supera su valor en 0, la
derivada no es positiva. -/
theorem deriv_nonpos_of_le_right {g : ℝ → ℝ} {g' : ℝ} (hg : HasDerivAt g g' 0)
    (hle : ∀ᶠ x in 𝓝[>] (0:ℝ), g x ≤ g 0) : g' ≤ 0 := by
  have ht : Tendsto (slope g 0) (𝓝[>] 0) (𝓝 g') :=
    (hasDerivAt_iff_tendsto_slope.mp hg).mono_left
      (nhdsWithin_mono _ fun x hx => Set.mem_compl_singleton_iff.mpr (ne_of_gt (Set.mem_Ioi.mp hx)))
  refine le_of_tendsto ht ?_
  filter_upwards [hle, self_mem_nhdsWithin] with x hx hpos
  rw [slope_def_field]
  exact div_nonpos_iff.mpr (Or.inr ⟨by linarith, by linarith [Set.mem_Ioi.mp hpos]⟩)

/-- **La rosa de la dominancia.** Si en un punto s₀ de la pared el cociente q (reflejo / luz) tiene
módulo 1 y justo a su derecha no pasa de 1, entonces Re(q′(s₀)·conj q(s₀)) ≤ 0. -/
theorem rosa_de_dominancia {q : ℂ → ℂ} {s₀ : ℂ} (hq : DifferentiableAt ℂ q s₀)
    (h1 : ‖q s₀‖ = 1) (hder : ∀ᶠ x : ℝ in 𝓝[>] 0, ‖q (s₀ + (x : ℂ))‖ ≤ 1) :
    (deriv q s₀ * conj (q s₀)).re ≤ 0 := by
  have h0 : HasDerivAt (fun z : ℂ => q (s₀ + z)) (deriv q s₀) ((0:ℝ):ℂ) := by
    have hq' : HasDerivAt q (deriv q s₀) (s₀ + ((0:ℝ):ℂ)) := by simpa using hq.hasDerivAt
    exact hq'.comp_const_add s₀ ((0:ℝ):ℂ)
  have hre : HasDerivAt (fun x : ℝ => (q (s₀ + x)).re) (deriv q s₀).re 0 := h0.real_of_complex
  have him : HasDerivAt (fun x : ℝ => (q (s₀ + x)).im) (deriv q s₀).im 0 := by
    have h := (h0.const_mul (-I)).real_of_complex
    simpa [Complex.mul_re] using h
  have hg := (hre.mul hre).add (him.mul him)
  have hkey := deriv_nonpos_of_le_right hg (by
    filter_upwards [hder] with x hx
    have hx2 : ‖q (s₀ + x)‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (q (s₀ + x))]
    have e1 : (q (s₀ + x)).re * (q (s₀ + x)).re + (q (s₀ + x)).im * (q (s₀ + x)).im
        = ‖q (s₀ + x)‖ ^ 2 := by rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    have e0 : (q (s₀ + ((0:ℝ):ℂ))).re * (q (s₀ + ((0:ℝ):ℂ))).re
        + (q (s₀ + ((0:ℝ):ℂ))).im * (q (s₀ + ((0:ℝ):ℂ))).im = 1 := by
      rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq]; simp [h1]
    simp only [Pi.add_apply, Pi.mul_apply]
    rw [e1, e0]; exact hx2)
  simp only [Complex.ofReal_zero, add_zero] at hkey
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  nlinarith [hkey]

/-- La rapidez angular de q a lo largo de la pared (la curva t ↦ q(s₀ + t·i), de velocidad i·q′)
es Im(i·q′·conj q) = Re(q′·conj q): el teorema anterior dice que esa fase no sube. -/
theorem rapidez_angular_pared (d c : ℂ) : (I * d * conj c).im = (d * conj c).re := by
  simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.conj_re,
    Complex.conj_im]
  ring

end RhG1Lean
