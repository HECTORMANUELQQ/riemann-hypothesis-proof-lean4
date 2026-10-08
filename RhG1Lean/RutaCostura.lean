/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.

# La ruta de la costura: luz directa cosida ⇒ ningún huésped escapa

Edificio de papel: se parte ξ en una "luz directa" E y su "reflejo" en el gran espejo,

    E♯(s) = conj (E (1 - conj s)),        ξ = E + E♯.

* Equilibrio en la pared (exacto): en Re s = 1/2, ‖E♯ s‖ = ‖E s‖.
* Lente redonda (Phragmén–Lindelöf + principio del máximo): si E no se apaga en la franja
  1/2 ≤ Re s ≤ b y el reflejo no le gana en el borde Re s = b, entonces E + E♯ ≠ 0 en el
  interior de la franja.
* Con el jardín (Re ≥ 1 sin ceros) y el espejo (ξ(1-s) = ξ(s)), eso da la Hipótesis de
  Riemann en la forma oficial de Mathlib (`RiemannHypothesis`).

El único paso NO demostrado (el paso 2 de la ruta) aparece como hipótesis explícita:
existe una costura E entera que no se apaga en la franja, con crecimiento controlado y con
el reflejo dominado en el borde Re s = b. Este archivo prueba la implicación, no la hipótesis.
-/
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.Convex
import RhG1Lean.ConeO1ZeroFree
import RhG1Lean.StripReduction

open Complex Set Filter Asymptotics ComplexConjugate
open scoped Real Topology

namespace RhG1Lean

/-- El reflejo de una mitad `E` en el gran espejo del pasillo. -/
noncomputable def reflejo (E : ℂ → ℂ) (s : ℂ) : ℂ := conj (E (1 - conj s))

/-- En la pared (el pasillo), `1 - conj s = s`. -/
theorem one_sub_conj_eq_self_of_re_half {s : ℂ} (hs : s.re = 1 / 2) : 1 - conj s = s := by
  apply Complex.ext
  · simp only [sub_re, one_re, conj_re]; rw [hs]; norm_num
  · simp only [sub_im, one_im, conj_im]; ring

/-- **Equilibrio exacto en la pared.** En el pasillo, el reflejo pesa lo mismo que la luz directa. -/
theorem norm_reflejo_eq_on_wall (E : ℂ → ℂ) {s : ℂ} (hs : s.re = 1 / 2) :
    ‖reflejo E s‖ = ‖E s‖ := by
  unfold reflejo
  rw [one_sub_conj_eq_self_of_re_half hs]
  exact Complex.norm_conj _

/-- El reflejo de una mitad entera es entero. -/
theorem differentiable_reflejo {E : ℂ → ℂ} (hE : Differentiable ℂ E) :
    Differentiable ℂ (reflejo E) := by
  intro s
  have hg : Differentiable ℂ (fun w => E (1 - w)) :=
    hE.comp ((differentiable_const 1).sub differentiable_id)
  have h := (hg (conj s)).conj_conj
  rw [Complex.conj_conj] at h
  exact h

/-- **Lente redonda (abstracta).** En una franja vertical a < Re z < b: si E no se apaga en la
franja cerrada, el reflejo F no le gana en los dos bordes, el cociente F/E crece de forma
controlada, y E + F no es idénticamente nula, entonces E + F no se anula en el interior. -/
theorem add_ne_zero_of_costura_strip {E F : ℂ → ℂ} {a b : ℝ} (hab : a < b)
    (hE : Differentiable ℂ E) (hF : Differentiable ℂ F)
    (hE0 : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → E z ≠ 0)
    (hB : ∃ c < π / (b - a), ∃ B, (fun z => F z / E z) =O[comap (_root_.abs ∘ im) atTop ⊓
      𝓟 (re ⁻¹' Ioo a b)] fun z ↦ Real.exp (B * Real.exp (c * |z.im|)))
    (ha : ∀ z : ℂ, z.re = a → ‖F z‖ ≤ ‖E z‖) (hb : ∀ z : ℂ, z.re = b → ‖F z‖ ≤ ‖E z‖)
    (hnt : ∃ z₀ : ℂ, a < z₀.re ∧ z₀.re < b ∧ E z₀ + F z₀ ≠ 0) :
    ∀ z : ℂ, a < z.re → z.re < b → E z + F z ≠ 0 := by
  have hqd : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → DifferentiableAt ℂ (fun z => F z / E z) z :=
    fun z h1 h2 => (hF z).div (hE z) (hE0 z h1 h2)
  have hcl : closure (re ⁻¹' Ioo a b) = re ⁻¹' Icc a b := by
    rw [closure_preimage_re, closure_Ioo hab.ne]
  have hqdc : DiffContOnCl ℂ (fun z => F z / E z) (re ⁻¹' Ioo a b) := by
    refine ⟨fun z hz => (hqd z hz.1.le hz.2.le).differentiableWithinAt, ?_⟩
    rw [hcl]
    intro z hz
    exact (hqd z hz.1 hz.2).continuousAt.continuousWithinAt
  -- cota en los bordes: ‖F/E‖ ≤ 1
  have hbd_a : ∀ w : ℂ, w.re = a → ‖F w / E w‖ ≤ 1 := by
    intro w hw
    have hEw : E w ≠ 0 := hE0 w (le_of_eq hw.symm) (by rw [hw]; exact hab.le)
    rw [norm_div]
    exact (div_le_one (norm_pos_iff.mpr hEw)).mpr (ha w hw)
  have hbd_b : ∀ w : ℂ, w.re = b → ‖F w / E w‖ ≤ 1 := by
    intro w hw
    have hEw : E w ≠ 0 := hE0 w (by rw [hw]; exact hab.le) (le_of_eq hw)
    rw [norm_div]
    exact (div_le_one (norm_pos_iff.mpr hEw)).mpr (hb w hw)
  -- Phragmén–Lindelöf: ‖F/E‖ ≤ 1 en toda la franja cerrada
  have hle : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖F z / E z‖ ≤ 1 := fun z h1 h2 =>
    PhragmenLindelof.vertical_strip (f := fun z => F z / E z) hqdc hB hbd_a hbd_b h1 h2
  -- si E + F se anulara en el interior, F/E = -1 sería un máximo interior
  intro z hz1 hz2 hzero
  have hEz : E z ≠ 0 := hE0 z hz1.le hz2.le
  have hqz : F z / E z = -1 := by
    have hF' : F z = -E z := by linear_combination hzero
    rw [hF', neg_div, div_self hEz]
  have hUo : IsOpen (re ⁻¹' Ioo a b) := isOpen_Ioo.preimage continuous_re
  have hUc : IsPreconnected (re ⁻¹' Ioo a b) := by
    have hset : re ⁻¹' Ioo a b = {c : ℂ | a < c.re} ∩ {c : ℂ | c.re < b} := by
      ext c; simp [Set.mem_Ioo]
    rw [hset]
    exact ((convex_halfSpace_re_gt a).inter (convex_halfSpace_re_lt b)).isPreconnected
  have hmax : IsMaxOn (norm ∘ fun z => F z / E z) (re ⁻¹' Ioo a b) z := by
    refine isMaxOn_iff.mpr fun x hx => ?_
    show ‖F x / E x‖ ≤ ‖F z / E z‖
    rw [hqz, norm_neg, norm_one]
    exact hle x hx.1.le hx.2.le
  have heq := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hUc hUo hqdc.differentiableOn
    ⟨hz1, hz2⟩ hmax
  obtain ⟨z₀, h01, h02, hne⟩ := hnt
  have hq0 : F z₀ / E z₀ = -1 := by
    have h := heq (show z₀ ∈ re ⁻¹' Ioo a b from ⟨h01, h02⟩)
    simpa [hqz] using h
  apply hne
  have hE0' : E z₀ ≠ 0 := hE0 z₀ h01.le h02.le
  have h := (div_eq_iff hE0').mp hq0
  linear_combination h

/-- **La ruta de la costura para ξ.** Si existe una luz directa cosida E (entera) con
ξ = E + E♯, que no se apaga en 1/2 ≤ Re s ≤ b (b > 1), cuyo reflejo no le gana en Re s = b y con
crecimiento controlado, entonces ξ no se anula en 1/2 < Re s < b. -/
theorem entireXi_ne_zero_of_costura {E : ℂ → ℂ} {b : ℝ} (hb1 : 1 < b)
    (hEd : Differentiable ℂ E) (hxi : ∀ s, entireXi s = E s + reflejo E s)
    (hE0 : ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ b → E z ≠ 0)
    (hB : ∃ c < π / (b - 1 / 2), ∃ B, (fun z => reflejo E z / E z) =O[comap (_root_.abs ∘ im)
      atTop ⊓ 𝓟 (re ⁻¹' Ioo (1 / 2) b)] fun z ↦ Real.exp (B * Real.exp (c * |z.im|)))
    (hb : ∀ z : ℂ, z.re = b → ‖reflejo E z‖ ≤ ‖E z‖) :
    ∀ s : ℂ, 1 / 2 < s.re → s.re < b → entireXi s ≠ 0 := by
  intro s h1 h2
  rw [hxi s]
  refine add_ne_zero_of_costura_strip (by linarith) hEd (differentiable_reflejo hEd) hE0 hB
    (fun z hz => (norm_reflejo_eq_on_wall E hz).le) hb ?_ s h1 h2
  refine ⟨(((1 + b) / 2 : ℝ) : ℂ), ?_, ?_, ?_⟩
  · simp only [ofReal_re]; linarith
  · simp only [ofReal_re]; linarith
  · rw [← hxi]
    apply entireXi_ne_zero_of_one_le_re
    simp only [ofReal_re]; linarith

/-- Con la costura, todo cero de ζ en la franja crítica está en el pasillo. -/
theorem zeta_zero_on_line_of_costura {E : ℂ → ℂ} {b : ℝ} (hb1 : 1 < b)
    (hEd : Differentiable ℂ E) (hxi : ∀ s, entireXi s = E s + reflejo E s)
    (hE0 : ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ b → E z ≠ 0)
    (hB : ∃ c < π / (b - 1 / 2), ∃ B, (fun z => reflejo E z / E z) =O[comap (_root_.abs ∘ im)
      atTop ⊓ 𝓟 (re ⁻¹' Ioo (1 / 2) b)] fun z ↦ Real.exp (B * Real.exp (c * |z.im|)))
    (hb : ∀ z : ℂ, z.re = b → ‖reflejo E z‖ ≤ ‖E z‖) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → s.re = 1 / 2 := by
  intro s h0 h1 hz
  have hxi0 : entireXi s = 0 := (entireXi_eq_zero_iff_zeta_of_mem_strip h0 h1).mpr hz
  have key := entireXi_ne_zero_of_costura hb1 hEd hxi hE0 hB hb
  rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
  · exfalso
    have hw1 : 1 / 2 < (1 - s).re := by simp only [sub_re, one_re]; linarith
    have hw2 : (1 - s).re < b := by simp only [sub_re, one_re]; linarith
    exact key (1 - s) hw1 hw2 (by rw [entireXi_one_sub]; exact hxi0)
  · exact heq
  · exact absurd hxi0 (key s hgt (by linarith))

/-- El jardín izquierdo: fuera de los ceros triviales (y de s = 0), ζ no se anula en Re s ≤ 0.
Se deduce de la ecuación funcional de Mathlib y del jardín derecho Re ≥ 1. -/
theorem riemannZeta_ne_zero_of_re_nonpos {s : ℂ} (hs : s.re ≤ 0)
    (hnt : ¬∃ n : ℕ, s = -2 * (n + 1)) : riemannZeta s ≠ 0 := by
  by_cases h0 : s = 0
  · subst h0; rw [riemannZeta_zero]; norm_num
  have hsw : s = 1 - (1 - s) := by ring
  have hwre : 1 ≤ (1 - s).re := by simp only [sub_re, one_re]; linarith
  have hwn : ∀ n : ℕ, (1 - s) ≠ -n := by
    intro n hn
    have h := congrArg Complex.re hn
    simp only [sub_re, one_re, neg_re, natCast_re] at h
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hw1 : (1 - s) ≠ 1 := by
    intro h; apply h0; linear_combination -h
  rw [hsw, riemannZeta_one_sub hwn hw1]
  have hz : riemannZeta (1 - s) ≠ 0 := riemannZeta_ne_zero_of_one_le_re hwre
  have hG : Complex.Gamma (1 - s) ≠ 0 := Complex.Gamma_ne_zero hwn
  have h2pi : (2 * (π : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hp : (2 * (π : ℂ)) ^ (-(1 - s)) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    rintro ⟨h, -⟩
    exact h2pi h
  have hc : Complex.cos (π * (1 - s) / 2) ≠ 0 := by
    rw [Ne, Complex.cos_eq_zero_iff]
    rintro ⟨k, hk⟩
    have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hmul : (π : ℂ) * ((1 - s) - (2 * k + 1)) = 0 := by linear_combination 2 * hk
    have hwk : (1 - s) = 2 * k + 1 := by
      rcases mul_eq_zero.mp hmul with h | h
      · exact absurd h hpi
      · linear_combination h
    have hre := congrArg Complex.re hwk
    simp only [sub_re, one_re, add_re, mul_re, re_ofNat, intCast_re, im_ofNat, intCast_im,
      mul_zero, sub_zero] at hre
    have hk0 : (0 : ℝ) ≤ k := by linarith
    have hk0' : 0 ≤ k := by exact_mod_cast hk0
    rcases (show k = 0 ∨ 1 ≤ k by omega) with hk | hk
    · apply hw1; rw [hwk, hk]; simp
    · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ k - 1 by omega)
      apply hnt
      refine ⟨n, ?_⟩
      have hkn : k = (n : ℤ) + 1 := by omega
      have hs : s = 1 - (2 * k + 1) := by linear_combination -hwk
      rw [hs, hkn]; push_cast; ring
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hp) hG) hc) hz

/-- **La ruta de la costura ⇒ Hipótesis de Riemann** (en la forma oficial de Mathlib).
Todo está demostrado excepto la existencia de la costura E, que es la hipótesis. -/
theorem riemannHypothesis_of_costura {E : ℂ → ℂ} {b : ℝ} (hb1 : 1 < b)
    (hEd : Differentiable ℂ E) (hxi : ∀ s, entireXi s = E s + reflejo E s)
    (hE0 : ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ b → E z ≠ 0)
    (hB : ∃ c < π / (b - 1 / 2), ∃ B, (fun z => reflejo E z / E z) =O[comap (_root_.abs ∘ im)
      atTop ⊓ 𝓟 (re ⁻¹' Ioo (1 / 2) b)] fun z ↦ Real.exp (B * Real.exp (c * |z.im|)))
    (hb : ∀ z : ℂ, z.re = b → ‖reflejo E z‖ ≤ ‖E z‖) :
    _root_.RiemannHypothesis := by
  intro s hz hnt _hs1
  have hre1 : s.re < 1 := by
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hz
  have hre0 : 0 < s.re := by
    by_contra h
    exact riemannZeta_ne_zero_of_re_nonpos (not_lt.mp h) hnt hz
  exact zeta_zero_on_line_of_costura hb1 hEd hxi hE0 hB hb s hre0 hre1 hz

/-- La misma conclusión en la forma del proyecto (franja crítica). -/
theorem riemannHypothesis_strip_of_costura {E : ℂ → ℂ} {b : ℝ} (hb1 : 1 < b)
    (hEd : Differentiable ℂ E) (hxi : ∀ s, entireXi s = E s + reflejo E s)
    (hE0 : ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ b → E z ≠ 0)
    (hB : ∃ c < π / (b - 1 / 2), ∃ B, (fun z => reflejo E z / E z) =O[comap (_root_.abs ∘ im)
      atTop ⊓ 𝓟 (re ⁻¹' Ioo (1 / 2) b)] fun z ↦ Real.exp (B * Real.exp (c * |z.im|)))
    (hb : ∀ z : ℂ, z.re = b → ‖reflejo E z‖ ≤ ‖E z‖) :
    RiemannHypothesis :=
  zeta_zero_on_line_of_costura hb1 hEd hxi hE0 hB hb

end RhG1Lean
