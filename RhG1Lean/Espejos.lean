/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.

# Espejos dentro de espejos, la ley de la rampa, y espejos curvos

* Ley de la rampa: si la luz directa E es más fuerte en (σ, t) que en su punto espejo (1-σ, t)
  (por ejemplo, si crece hacia el jardín en cada piso), el reflejo nunca la cancela: ningún
  huésped escapa. Pointwise; sin Phragmén–Lindelöf; conclusión: `RiemannHypothesis` de Mathlib.
* Espejos dentro de espejos: el espejo del pasillo (σ = 1/2) compuesto con el espejo de la pared
  (σ = 0, el de cada primo) es la traslación s ↦ s + 1; iterado, infinitas traslaciones.
* El espejo de cada primo es un espejo INCLINADO: ‖1 - p^{conj s}‖ = p^{Re s} ‖1 - p^{-s}‖.
* El espejo curvo de los cimientos: la matriz S = [[0,-1],[1,0]] (τ ↦ -1/τ) manda ix ↦ i/x
  (el doblez x ↦ 1/x de θ), y la inversión en el círculo unidad fija ese círculo.
-/
import RhG1Lean.RutaCostura
import RhG1Lean.DeduccionesPapel

open Complex ComplexConjugate Set

namespace RhG1Lean

/-! ## Ley de la rampa -/

/-- El punto espejo de s está en el mismo piso, del otro lado del pasillo. -/
theorem one_sub_conj_re_im (s : ℂ) :
    (1 - conj s).re = 1 - s.re ∧ (1 - conj s).im = s.im := by
  constructor <;> simp

/-- **Ley de la rampa (puntual).** Si la luz directa es más fuerte en s que en su punto espejo,
el reflejo no puede cancelarla. -/
theorem add_reflejo_ne_zero_of_rampa {E : ℂ → ℂ} {s : ℂ}
    (h : ‖E (1 - conj s)‖ < ‖E s‖) : E s + reflejo E s ≠ 0 := by
  intro h0
  have hr : reflejo E s = -E s := by linear_combination h0
  have hn : ‖reflejo E s‖ = ‖E (1 - conj s)‖ := by unfold reflejo; exact Complex.norm_conj _
  rw [hr, norm_neg] at hn
  linarith

/-- Una rampa (luz directa estrictamente creciente hacia el jardín en cada piso, en [0,1])
cumple la hipótesis puntual en toda el ala derecha de la franja. -/
theorem rampa_of_strictMonoOn {E : ℂ → ℂ}
    (hm : ∀ t : ℝ, StrictMonoOn (fun σ : ℝ => ‖E ((σ : ℂ) + (t : ℂ) * I)‖) (Icc 0 1)) :
    ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → ‖E (1 - conj s)‖ < ‖E s‖ := by
  intro s h1 h2
  have hs : s = ((s.re : ℝ) : ℂ) + ((s.im : ℝ) : ℂ) * I := (Complex.re_add_im s).symm
  have hm' : (1 - conj s) = ((1 - s.re : ℝ) : ℂ) + ((s.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  have key := hm s.im (show 1 - s.re ∈ Icc (0 : ℝ) 1 by constructor <;> linarith)
    (show s.re ∈ Icc (0 : ℝ) 1 by constructor <;> linarith) (by linarith)
  simp only at key
  rw [hm']
  conv_rhs => rw [hs]
  exact key

/-- **La ley de la rampa ⇒ Hipótesis de Riemann** (forma oficial de Mathlib). Basta una
costura E con ξ = E + E♯ cuya luz sea más fuerte que en el punto espejo en todo el ala
derecha de la franja crítica. No se pide ni holomorfía de E. -/
theorem riemannHypothesis_of_rampa {E : ℂ → ℂ} (hxi : ∀ s, entireXi s = E s + reflejo E s)
    (hr : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → ‖E (1 - conj s)‖ < ‖E s‖) :
    _root_.RiemannHypothesis := by
  have key : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → entireXi s ≠ 0 := fun s h1 h2 => by
    rw [hxi s]; exact add_reflejo_ne_zero_of_rampa (hr s h1 h2)
  intro s hz hnt _hs1
  have hre1 : s.re < 1 := by
    by_contra h; exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hz
  have hre0 : 0 < s.re := by
    by_contra h; exact riemannZeta_ne_zero_of_re_nonpos (not_lt.mp h) hnt hz
  have hxi0 : entireXi s = 0 := (entireXi_eq_zero_iff_zeta_of_mem_strip hre0 hre1).mpr hz
  rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
  · exfalso
    have hw1 : 1 / 2 < (1 - s).re := by simp only [sub_re, one_re]; linarith
    have hw2 : (1 - s).re < 1 := by simp only [sub_re, one_re]; linarith
    exact key (1 - s) hw1 hw2 (by rw [entireXi_one_sub]; exact hxi0)
  · exact heq
  · exact absurd hxi0 (key s hgt hre1)

/-! ## Espejos dentro de espejos -/

/-- El espejo del pasillo (refleja cada piso a través de σ = 1/2). -/
def espejoPasillo (s : ℂ) : ℂ := 1 - conj s

/-- El espejo de la pared σ = 0 (el espejo natural de cada primo). -/
def espejoPared (s : ℂ) : ℂ := -conj s

theorem espejoPasillo_involutivo (s : ℂ) : espejoPasillo (espejoPasillo s) = s := by
  simp [espejoPasillo]

theorem espejoPared_involutivo (s : ℂ) : espejoPared (espejoPared s) = s := by
  simp [espejoPared]

/-- **Dos espejos paralelos dan una traslación:** pasillo ∘ pared = s ↦ s + 1. -/
theorem espejos_dan_traslacion (s : ℂ) : espejoPasillo (espejoPared s) = s + 1 := by
  simp [espejoPasillo, espejoPared]; ring

/-- **Infinitos espejos dentro de los espejos:** iterar la pareja da todas las traslaciones s + n. -/
theorem espejos_iterados (n : ℕ) (s : ℂ) :
    (espejoPasillo ∘ espejoPared)^[n] s = s + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Function.comp_apply, espejos_dan_traslacion]
    push_cast; ring

/-- ξ respeta el espejo del pasillo (en módulo). -/
theorem norm_entireXi_espejoPasillo (s : ℂ) : ‖entireXi (espejoPasillo s)‖ = ‖entireXi s‖ := by
  unfold espejoPasillo
  rw [entireXi_one_sub, entireXi_conj, Complex.norm_conj]

/-- **El espejo de cada primo es un espejo inclinado:** reflejado en la pared σ = 0, el factor
de Euler cambia de tamaño exactamente por p^{Re s}. -/
theorem espejo_primo_inclinado {p : ℝ} (hp : 0 < p) (s : ℂ) :
    ‖1 - (p : ℂ) ^ (-(espejoPared s))‖ = p ^ s.re * ‖1 - (p : ℂ) ^ (-s)‖ := by
  unfold espejoPared
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have harg : ((p : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hp.le]; exact Real.pi_ne_zero.symm
  rw [neg_neg, Complex.cpow_conj _ _ harg, Complex.conj_ofReal]
  have hns : ‖(p : ℂ) ^ s‖ = p ^ s.re := Complex.norm_cpow_eq_rpow_re_of_pos hp s
  have hpos : (0 : ℝ) < p ^ s.re := Real.rpow_pos_of_pos hp _
  have hne : (p : ℂ) ^ s ≠ 0 := by
    intro h; rw [h, norm_zero] at hns; linarith
  have h1 : ‖1 - conj ((p : ℂ) ^ s)‖ = ‖1 - (p : ℂ) ^ s‖ := by
    rw [← Complex.norm_conj, map_sub, map_one, Complex.conj_conj]
  rw [h1, Complex.cpow_neg]
  have h2 : (1 : ℂ) - ((p : ℂ) ^ s)⁻¹ = -((1 - (p : ℂ) ^ s) / (p : ℂ) ^ s) := by
    field_simp; ring
  rw [h2, norm_neg, norm_div, hns]
  field_simp

/-! ## El espejo curvo de los cimientos (matriz de Möbius) -/

/-- La matriz S = [[0,-1],[1,0]] actúa como τ ↦ -1/τ. Sobre el eje imaginario es el doblez
de los cimientos: i·x ↦ i·(1/x). -/
theorem mobius_S_doblez {x : ℝ} (hx : x ≠ 0) :
    -1 / (I * (x : ℂ)) = I * ((1 / x : ℝ) : ℂ) := by
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  push_cast
  field_simp
  rw [I_sq]

/-- **El espejo curvo:** la inversión en el círculo unidad (τ ↦ 1/conj τ) deja fijo cada punto
del círculo; manda i·x a i/x. -/
theorem inversion_circulo_fija {τ : ℂ} (h : ‖τ‖ = 1) : 1 / conj τ = τ := by
  have hτ : τ ≠ 0 := by intro h0; rw [h0, norm_zero] at h; norm_num at h
  have hmul : τ * conj τ = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h]; norm_num
  have hc : conj τ ≠ 0 := by rwa [map_ne_zero]
  rw [div_eq_iff hc]
  exact hmul.symm

theorem inversion_circulo_doblez {x : ℝ} (hx : x ≠ 0) :
    1 / conj (I * (x : ℂ)) = I * ((1 / x : ℝ) : ℂ) := by
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  field_simp
  rw [I_sq]

/-! ## El espejo de mosaico: muchos espejos pequeños forman el gran espejo -/

/-- **Cada azulejo es un espejo perfecto:** una ventana más su reflejo es real. -/
theorem azulejo_real (z : ℂ) : (z + conj z).im = 0 := by simp

/-- **El mosaico entero es un espejo perfecto:** la suma de azulejos es real (el termómetro). -/
theorem mosaico_real {ι : Type*} (S : Finset ι) (z : ι → ℂ) :
    (∑ j ∈ S, (z j + conj (z j))).im = 0 := by
  rw [Complex.im_sum]
  exact Finset.sum_eq_zero (fun j _ => azulejo_real (z j))

/-- **Fuera del pasillo cada azulejo se inclina según su velocidad ω:** la luz directa pesa
e^{2δω} veces su reflejo (δ = distancia al pasillo). -/
theorem azulejo_inclinado (a ω δ α : ℝ) :
    ‖((a * Real.exp (δ * ω) : ℝ) : ℂ) * Complex.exp (α * I)‖ =
      Real.exp (2 * δ * ω) * ‖((a * Real.exp (-(δ * ω)) : ℝ) : ℂ) * Complex.exp (-(α * I))‖ := by
  rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I]
  have h2 : ‖Complex.exp (-(α * I))‖ = 1 := by
    rw [show -((α : ℂ) * I) = ((-α : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [h2, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
  have : Real.exp (δ * ω) = Real.exp (2 * δ * ω) * Real.exp (-(δ * ω)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [this]; ring

end RhG1Lean
