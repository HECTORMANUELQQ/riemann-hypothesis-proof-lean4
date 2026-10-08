/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.

# Deducciones del Edificio de Papel, verificadas en Lean

Cada resultado corresponde a una deducción "📐" de las rondas de pensamiento:

* D4  · Cassini = cono:            s(s-1) = (s - 1/2)² - 1/4.
* D4  · El pasillo es la mediatriz de las esquinas 0 y 1:  ‖s‖ = ‖s-1‖ ↔ Re s = 1/2.
* D4  · Un escapado sube en Cassini: ‖ρ‖²‖ρ-1‖² - (1/4+γ²)² = b²(2γ² - 1/2 + b²).
* V1  · Pisos y columnas del cono son parábolas con foco en el corazón (foco–directriz).
* H2  · Equilibrio exacto del pasillo: ξ es real en la recta y Re(ξ'/ξ) = 0 ahí.
* H1  · Puerta del valle (dirección fácil).
* D3  · Los pilotes son las ventanas: Φₙ(u) = n^(-1/2) Φ₁(u + log n).
* H8  · Pliegue roto: Φ₁'(0) > 0 y Φₙ'(0) < 0 para todo n ≥ 2 (el pilote 1 rompe el doblez
        hacia un lado y todos los demás hacia el otro).
* D3  · El pilote 1 solo es negativo a la izquierda; cada pilote es positivo para u ≥ 0.
* V4  · Lente redonda: ∫ δ/(δ²+x²) dx = π (un huésped = media ventana) y = -π si δ < 0.
* B23 · Rice: γ = √5/3 con espectro uniforme; 0.1273 < (1 - √5/3)/2 < 0.1274.
* B22 · Dandelin: ∫₀^{π/4} dφ/cos φ = log(1 + √2).
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.Deriv.Star
import RhG1Lean.XiEntire
import RhG1Lean.Conj
import RhG1Lean.DualCancellation
import RhG1Lean.StripReduction

open Complex Set Filter ComplexConjugate
open scoped Real Topology

namespace RhG1Lean

/-! ## D4 · El cono y las esquinas -/

/-- **Cassini = cono.** La lupa s(s-1) es u - 1/4 con u = (s - 1/2)². -/
theorem lupa_eq_cono (s : ℂ) : s * (s - 1) = (s - 1 / 2) ^ 2 - 1 / 4 := by ring

/-- ‖s‖² - ‖s-1‖² = 2 Re s - 1. -/
theorem normSq_sub_normSq_sub_one (s : ℂ) :
    Complex.normSq s - Complex.normSq (s - 1) = 2 * s.re - 1 := by
  simp only [Complex.normSq_apply, sub_re, one_re, sub_im, one_im, sub_zero]
  ring

/-- **El pasillo es la mediatriz de las dos esquinas** de la planta baja (0 y 1). -/
theorem norm_eq_norm_sub_one_iff (s : ℂ) : ‖s‖ = ‖s - 1‖ ↔ s.re = 1 / 2 := by
  have h := normSq_sub_normSq_sub_one s
  rw [← Complex.sq_norm, ← Complex.sq_norm] at h
  constructor
  · intro he
    rw [he] at h
    linarith
  · intro hre
    have hsq : ‖s‖ ^ 2 = ‖s - 1‖ ^ 2 := by rw [hre] at h; linarith
    have h1 := norm_nonneg s
    have h2 := norm_nonneg (s - 1)
    nlinarith [sq_nonneg (‖s‖ - ‖s - 1‖), sq_nonneg (‖s‖ + ‖s - 1‖)]

/-- **Un escapado sube en Cassini.** Para ρ = (1/2 + b) + iγ, el producto de las distancias a
las esquinas excede al del pasillo en b²(2γ² - 1/2 + b²). -/
theorem escapado_cassini_exceso (b γ : ℝ) :
    Complex.normSq (((1 / 2 + b : ℝ) : ℂ) + γ * I) *
      Complex.normSq (((1 / 2 + b : ℝ) : ℂ) + γ * I - 1) - (1 / 4 + γ ^ 2) ^ 2 =
      b ^ 2 * (2 * γ ^ 2 - 1 / 2 + b ^ 2) := by
  simp only [Complex.normSq_apply, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, add_im,
    mul_im, sub_re, one_re, sub_im, one_im]
  ring

/-- Si |γ| > 1/2 y b ≠ 0, el escapado está estrictamente "más arriba" en Cassini. -/
theorem escapado_cassini_sube {b γ : ℝ} (hb : b ≠ 0) (hγ : 1 / 4 < γ ^ 2) :
    (1 / 4 + γ ^ 2) ^ 2 < Complex.normSq (((1 / 2 + b : ℝ) : ℂ) + γ * I) *
      Complex.normSq (((1 / 2 + b : ℝ) : ℂ) + γ * I - 1) := by
  have h := escapado_cassini_exceso b γ
  have hb2 : 0 < b ^ 2 := by positivity
  have : 0 < b ^ 2 * (2 * γ ^ 2 - 1 / 2 + b ^ 2) := by
    apply mul_pos hb2; nlinarith
  linarith

/-! ## V1 · Pisos y columnas del cono son parábolas con foco en el corazón -/

/-- **Cada piso es una parábola con foco en el corazón.** Para w = δ + i t (t ≠ 0) y u = w²:
la distancia al foco (0) es igual a la distancia a la directriz Re = -2t², y el vértice es el
punto del pasillo u = -t². -/
theorem piso_parabola (δ t : ℝ) (ht : t ≠ 0) :
    let u := ((δ : ℂ) + t * I) ^ 2
    u.re = u.im ^ 2 / (4 * t ^ 2) - t ^ 2 ∧ ‖u‖ = u.re + 2 * t ^ 2 := by
  intro u
  have hre : u.re = δ ^ 2 - t ^ 2 := by
    simp only [u, sq, mul_re, add_re, ofReal_re, mul_im, add_im, ofReal_im, I_re, I_im]; ring
  have him : u.im = 2 * δ * t := by
    simp only [u, sq, mul_re, add_re, ofReal_re, mul_im, add_im, ofReal_im, I_re, I_im]; ring
  have hnorm : ‖u‖ = δ ^ 2 + t ^ 2 := by
    simp only [u, norm_pow]
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, add_im, mul_im]
    ring
  refine ⟨?_, ?_⟩
  · rw [hre, him]; field_simp; ring
  · rw [hnorm, hre]; ring

/-- **Cada columna es una parábola con el mismo foco** (abierta hacia el otro lado):
vértice en la planta baja u = δ², directriz Re = 2δ². -/
theorem columna_parabola (δ t : ℝ) (hδ : δ ≠ 0) :
    let u := ((δ : ℂ) + t * I) ^ 2
    u.re = δ ^ 2 - u.im ^ 2 / (4 * δ ^ 2) ∧ ‖u‖ = 2 * δ ^ 2 - u.re := by
  intro u
  have hre : u.re = δ ^ 2 - t ^ 2 := by
    simp only [u, sq, mul_re, add_re, ofReal_re, mul_im, add_im, ofReal_im, I_re, I_im]; ring
  have him : u.im = 2 * δ * t := by
    simp only [u, sq, mul_re, add_re, ofReal_re, mul_im, add_im, ofReal_im, I_re, I_im]; ring
  have hnorm : ‖u‖ = δ ^ 2 + t ^ 2 := by
    simp only [u, norm_pow]
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, add_im, mul_im]
    ring
  refine ⟨?_, ?_⟩
  · rw [hre, him]; field_simp; ring
  · rw [hnorm, hre]; ring

/-! ## H2 · Equilibrio exacto del pasillo -/

/-- ξ conmuta con la conjugación (en todo ℂ), por el teorema de identidad. -/
theorem entireXi_conj (s : ℂ) : entireXi (conj s) = conj (entireXi s) := by
  have hf : Differentiable ℂ entireXi := differentiable_entireXi
  have hg : Differentiable ℂ (conj ∘ entireXi ∘ conj) := fun z =>
    differentiableAt_conj_conj_iff.mpr (hf (conj z))
  have hfa : AnalyticOnNhd ℂ entireXi univ := fun z _ => hf.analyticAt z
  have hga : AnalyticOnNhd ℂ (conj ∘ entireXi ∘ conj) univ := fun z _ => hg.analyticAt z
  have hev : entireXi =ᶠ[𝓝 (2 : ℂ)] (conj ∘ entireXi ∘ conj) := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const continuous_re
    have hmem : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by simp
    filter_upwards [hopen.mem_nhds hmem] with z hz
    have hz' : 1 < z.re := hz
    have hz0 : z ≠ 0 := by intro h; rw [h] at hz'; norm_num at hz'
    have hz1 : z ≠ 1 := by intro h; rw [h] at hz'; norm_num at hz'
    have hcz : 1 < (conj z).re := by simpa using hz'
    have hcz0 : conj z ≠ 0 := by intro h; rw [h] at hcz; norm_num at hcz
    have hcz1 : conj z ≠ 1 := by intro h; rw [h] at hcz; norm_num at hcz
    have hG : Gammaℝ z ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
    have hcG : Gammaℝ (conj z) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
    show entireXi z = conj (entireXi (conj z))
    rw [entireXi_eq_riemannXi hz0 hz1 hG, entireXi_eq_riemannXi hcz0 hcz1 hcG,
      riemannXi_conj, Complex.conj_conj]
  have hall := AnalyticOnNhd.eq_of_eventuallyEq hfa hga hev
  have h := congrFun hall (conj s)
  simp only [Function.comp, Complex.conj_conj] at h
  exact h

/-- En el pasillo, conj s = 1 - s. -/
theorem conj_eq_one_sub_on_line (t : ℝ) :
    conj ((1 / 2 : ℂ) + I * t) = 1 - ((1 / 2 : ℂ) + I * t) := by
  apply Complex.ext <;> norm_num

/-- **ξ es real en el pasillo.** -/
theorem entireXi_im_zero_on_line (t : ℝ) : (entireXi ((1 / 2 : ℂ) + I * t)).im = 0 := by
  have h1 := entireXi_conj ((1 / 2 : ℂ) + I * t)
  rw [conj_eq_one_sub_on_line, entireXi_one_sub] at h1
  exact Complex.conj_eq_iff_im.mp h1.symm

/-- **La pendiente horizontal es nula en el pasillo:** ξ' es imaginaria pura en la recta. -/
theorem deriv_entireXi_re_zero_on_line (t : ℝ) :
    (deriv entireXi ((1 / 2 : ℂ) + I * t)).re = 0 := by
  set s : ℂ := (1 / 2 : ℂ) + I * t with hs
  have hfun : (conj ∘ entireXi ∘ conj) = entireXi := by
    funext z
    simp only [Function.comp, entireXi_conj, Complex.conj_conj]
  have hd : deriv entireXi = conj ∘ deriv entireXi ∘ conj := by
    rw [← deriv_conj_conj, hfun]
  have h1 : deriv entireXi s = conj (deriv entireXi (conj s)) := by
    have := congrFun hd s
    simpa using this
  rw [hs, conj_eq_one_sub_on_line, deriv_entireXi_one_sub, map_neg] at h1
  -- d = -conj d  ⇒  Re d = 0
  have hre := congrArg Complex.re h1
  simp only [neg_re, conj_re] at hre
  linarith

/-- **Equilibrio exacto del pasillo (H2):** donde ξ no se anula, Re(ξ'/ξ) = 0 en la recta.
La pendiente de la arquitectura y la de las ventanas se cancelan exactamente. -/
theorem re_logDeriv_entireXi_on_line (t : ℝ) :
    (deriv entireXi ((1 / 2 : ℂ) + I * t) / entireXi ((1 / 2 : ℂ) + I * t)).re = 0 := by
  rw [Complex.div_re, deriv_entireXi_re_zero_on_line, entireXi_im_zero_on_line]
  simp

/-! ## H1 · Puerta del valle (dirección fácil) -/

/-- Si en cada piso el pasillo es estrictamente lo más oscuro, no hay escapados. -/
theorem entireXi_ne_zero_of_valle {s : ℂ}
    (hvalle : ‖entireXi ((1 / 2 : ℂ) + I * s.im)‖ < ‖entireXi s‖) : entireXi s ≠ 0 := by
  intro h
  rw [h, norm_zero] at hvalle
  exact absurd hvalle (not_lt.mpr (norm_nonneg _))

/-! ## D3 · Los pilotes son las ventanas -/

/-- El pilote n de los cimientos: Φₙ(u) = (2π²n⁴e^{9u/2} - 3πn²e^{5u/2})·exp(-πn²e^{2u}). -/
noncomputable def pilote (n u : ℝ) : ℝ :=
  (2 * π ^ 2 * n ^ 4 * Real.exp (9 * u / 2) - 3 * π * n ^ 2 * Real.exp (5 * u / 2)) *
    Real.exp (-π * n ^ 2 * Real.exp (2 * u))

/-- **El pilote n es el pilote 1 corrido log n y atenuado n^(-1/2)** (la ventana n). -/
theorem pilote_eq_ventana {n : ℝ} (hn : 0 < n) (u : ℝ) :
    pilote n u = n ^ (-(1 / 2 : ℝ)) * pilote 1 (u + Real.log n) := by
  have e9 : Real.exp (9 * (u + Real.log n) / 2) = Real.exp (9 * u / 2) * n ^ ((9 : ℝ) / 2) := by
    rw [Real.rpow_def_of_pos hn, ← Real.exp_add]; congr 1; ring
  have e5 : Real.exp (5 * (u + Real.log n) / 2) = Real.exp (5 * u / 2) * n ^ ((5 : ℝ) / 2) := by
    rw [Real.rpow_def_of_pos hn, ← Real.exp_add]; congr 1; ring
  have e2 : Real.exp (2 * (u + Real.log n)) = Real.exp (2 * u) * n ^ 2 := by
    have : n ^ 2 = Real.exp (2 * Real.log n) := by
      rw [← Real.log_rpow hn, Real.exp_log (by positivity)]; norm_num
    rw [this, ← Real.exp_add]; congr 1; ring
  have p9 : n ^ (-(1 / 2 : ℝ)) * n ^ ((9 : ℝ) / 2) = n ^ 4 := by
    rw [← Real.rpow_add hn, show (-(1 / 2 : ℝ)) + 9 / 2 = ((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
  have p5 : n ^ (-(1 / 2 : ℝ)) * n ^ ((5 : ℝ) / 2) = n ^ 2 := by
    rw [← Real.rpow_add hn, show (-(1 / 2 : ℝ)) + 5 / 2 = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
  unfold pilote
  rw [e9, e5, e2]
  have hX : Real.exp (-π * 1 ^ 2 * (Real.exp (2 * u) * n ^ 2)) =
      Real.exp (-π * n ^ 2 * Real.exp (2 * u)) := by congr 1; ring
  rw [hX]
  linear_combination (-(2 * π ^ 2 * Real.exp (9 * u / 2) *
      Real.exp (-π * n ^ 2 * Real.exp (2 * u)))) * p9 +
    (3 * π * Real.exp (5 * u / 2) * Real.exp (-π * n ^ 2 * Real.exp (2 * u))) * p5

/-- Cada pilote es positivo del lado de afuera de la ventana redonda (u ≥ 0, n ≥ 1). -/
theorem pilote_pos {n u : ℝ} (hn : 1 ≤ n) (hu : 0 ≤ u) : 0 < pilote n u := by
  unfold pilote
  apply mul_pos _ (Real.exp_pos _)
  have h9 : Real.exp (9 * u / 2) = Real.exp (5 * u / 2) * Real.exp (2 * u) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h9]
  have he2 : 1 ≤ Real.exp (2 * u) := Real.one_le_exp (by linarith)
  have he5 : 0 < Real.exp (5 * u / 2) := Real.exp_pos _
  have hn2 : 1 ≤ n ^ 2 := one_le_pow₀ hn
  have hpi := Real.pi_gt_three
  have k1 : 2 * π ≤ 2 * π * n ^ 2 := by nlinarith
  have k2 : 2 * π * n ^ 2 ≤ 2 * π * n ^ 2 * Real.exp (2 * u) :=
    le_mul_of_one_le_right (by positivity) he2
  have key : 3 < 2 * π * n ^ 2 * Real.exp (2 * u) := by linarith
  have hpos : 0 < π * n ^ 2 * Real.exp (5 * u / 2) := by positivity
  have heq : 2 * π ^ 2 * n ^ 4 * (Real.exp (5 * u / 2) * Real.exp (2 * u)) -
      3 * π * n ^ 2 * Real.exp (5 * u / 2) =
      π * n ^ 2 * Real.exp (5 * u / 2) * (2 * π * n ^ 2 * Real.exp (2 * u) - 3) := by ring
  rw [heq]
  exact mul_pos hpos (by linarith)

/-- El pilote 1 solo es negativo a la izquierda del punto log(3/(2π))/2 ≈ -0.37. -/
theorem pilote_one_neg {u : ℝ} (hu : u < Real.log (3 / (2 * π)) / 2) : pilote 1 u < 0 := by
  unfold pilote
  apply mul_neg_of_neg_of_pos _ (Real.exp_pos _)
  have h2u : Real.exp (2 * u) < 3 / (2 * π) := by
    rw [← Real.exp_log (show (0 : ℝ) < 3 / (2 * π) by positivity)]
    exact Real.exp_lt_exp.mpr (by linarith)
  have h9 : Real.exp (9 * u / 2) = Real.exp (5 * u / 2) * Real.exp (2 * u) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h9]
  have he5 : 0 < Real.exp (5 * u / 2) := Real.exp_pos _
  have hpi := Real.pi_pos
  have key : 2 * π * Real.exp (2 * u) < 3 := by
    have := mul_lt_mul_of_pos_left h2u (show 0 < 2 * π by positivity)
    rwa [mul_div_cancel₀ _ (by positivity : (2 * π) ≠ 0)] at this
  have hpos : 0 < π * Real.exp (5 * u / 2) := by positivity
  nlinarith

/-! ## H8 · El pliegue roto: el signo de Φₙ'(0) -/

/-- Derivada del pilote n en el doblez u = 0:
Φₙ'(0) = π n² e^{-πn²} (15πn² - 15/2 - 4π²n⁴). -/
theorem hasDerivAt_pilote_zero (n : ℝ) :
    HasDerivAt (pilote n)
      (π * n ^ 2 * Real.exp (-π * n ^ 2) * (15 * π * n ^ 2 - 15 / 2 - 4 * π ^ 2 * n ^ 4)) 0 := by
  have h9 : HasDerivAt (fun u : ℝ => Real.exp (9 * u / 2)) (Real.exp (9 * 0 / 2) * (9 / 2)) 0 :=
    (((hasDerivAt_id (0 : ℝ)).const_mul 9).div_const 2).exp.congr_deriv (by simp)
  have h5 : HasDerivAt (fun u : ℝ => Real.exp (5 * u / 2)) (Real.exp (5 * 0 / 2) * (5 / 2)) 0 :=
    (((hasDerivAt_id (0 : ℝ)).const_mul 5).div_const 2).exp.congr_deriv (by simp)
  have h2 : HasDerivAt (fun u : ℝ => Real.exp (2 * u)) (Real.exp (2 * 0) * 2) 0 :=
    ((hasDerivAt_id (0 : ℝ)).const_mul 2).exp.congr_deriv (by simp)
  have hA := ((h9.const_mul (2 * π ^ 2 * n ^ 4)).sub (h5.const_mul (3 * π * n ^ 2)))
  have hB := (h2.const_mul (-π * n ^ 2)).exp
  have hP := hA.mul hB
  unfold pilote
  convert hP using 1
  simp only [Pi.sub_apply, mul_zero, zero_div, Real.exp_zero, mul_one]
  ring

/-- **El pilote 1 rompe el doblez hacia un lado:** Φ₁'(0) > 0. -/
theorem pilote_one_deriv_pos :
    0 < π * 1 ^ 2 * Real.exp (-π * 1 ^ 2) * (15 * π * 1 ^ 2 - 15 / 2 - 4 * π ^ 2 * 1 ^ 4) := by
  have h3 := Real.pi_gt_three
  have h315 := Real.pi_lt_d2
  have hq : 0 < 15 * π - 15 / 2 - 4 * π ^ 2 := by nlinarith
  have he : 0 < Real.exp (-π * 1 ^ 2) := Real.exp_pos _
  simp only [one_pow, mul_one]
  positivity

/-- **Todos los demás pilotes lo tapan desde el otro lado:** Φₙ'(0) < 0 para n ≥ 2. -/
theorem pilote_deriv_neg {n : ℝ} (hn : 2 ≤ n) :
    π * n ^ 2 * Real.exp (-π * n ^ 2) * (15 * π * n ^ 2 - 15 / 2 - 4 * π ^ 2 * n ^ 4) < 0 := by
  have h3 := Real.pi_gt_three
  have hn2 : 4 ≤ n ^ 2 := by nlinarith
  have hq : 15 * π * n ^ 2 - 15 / 2 - 4 * π ^ 2 * n ^ 4 < 0 := by
    have : 15 * π * n ^ 2 < 4 * π ^ 2 * n ^ 4 := by
      have h1 : 15 < 4 * π * n ^ 2 := by nlinarith
      have h2 : 0 < π * n ^ 2 := by positivity
      nlinarith
    linarith
  have hpos : 0 < π * n ^ 2 * Real.exp (-π * n ^ 2) := by positivity
  exact mul_neg_of_pos_of_neg hpos hq

/-! ## V4 · La lente redonda: cada huésped aporta media ventana (π) -/

/-- **Un huésped visto con la lente δ > 0 aporta exactamente π.** -/
theorem integral_lente {δ : ℝ} (hδ : 0 < δ) : ∫ x : ℝ, δ / (δ ^ 2 + x ^ 2) = π := by
  have hfun : (fun x : ℝ => δ / (δ ^ 2 + x ^ 2)) = fun x => δ⁻¹ * (1 + (x / δ) ^ 2)⁻¹ := by
    funext x
    have : δ ^ 2 + x ^ 2 ≠ 0 := by positivity
    field_simp
  rw [hfun, MeasureTheory.integral_const_mul,
    MeasureTheory.Measure.integral_comp_div (fun y => (1 + y ^ 2)⁻¹) δ,
    integral_univ_inv_one_add_sq, abs_of_pos hδ, smul_eq_mul]
  field_simp

/-- **Un escapado más lejos que la lente aporta -π** (δ - b < 0). -/
theorem integral_lente_neg {c : ℝ} (hc : c < 0) : ∫ x : ℝ, c / (c ^ 2 + x ^ 2) = -π := by
  have h := integral_lente (neg_pos.mpr hc)
  have hfun : (fun x : ℝ => c / (c ^ 2 + x ^ 2)) = fun x => -((-c) / ((-c) ^ 2 + x ^ 2)) := by
    funext x; ring
  rw [hfun, MeasureTheory.integral_neg, h]

/-! ## B23 · El valor universal de Rice -/

/-- Momentos espectrales del espectro uniforme en [0, L]: λₖ = L^{k+1}/(k+1). -/
theorem momento_espectral (L : ℝ) (k : ℕ) :
    ∫ x in (0 : ℝ)..L, x ^ k = L ^ (k + 1) / (k + 1) := by
  rw [integral_pow]; simp

/-- **Rice:** γ = λ₂/√(λ₀λ₄) = √5/3 para el espectro uniforme (independiente de L). -/
theorem rice_gamma {L : ℝ} (hL : 0 < L) :
    (L ^ 3 / 3) / Real.sqrt (L * (L ^ 5 / 5)) = Real.sqrt 5 / 3 := by
  have h5 : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : L * (L ^ 5 / 5) = (L ^ 3 / Real.sqrt 5) ^ 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]; ring
  rw [hsq, Real.sqrt_sq (by positivity)]
  field_simp

/-- **El 12.73 %:** 0.1273 < (1 - √5/3)/2 < 0.1274. -/
theorem rice_fraccion :
    0.1273 < (1 - Real.sqrt 5 / 3) / 2 ∧ (1 - Real.sqrt 5 / 3) / 2 < 0.1274 := by
  have hlo : (2.2356 : ℝ) < Real.sqrt 5 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hhi : Real.sqrt 5 < 2.2362 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  constructor <;> linarith

/-! ## B22 · Dandelin: el promedio de las distancias focales -/

/-- ∫₀^{π/4} dφ / cos φ = log(1 + √2)  (el promedio universal es (8/π)·log(1+√2)). -/
theorem integral_sec_cuarto :
    ∫ x in (0 : ℝ)..(π / 4), 1 / Real.cos x = Real.log (1 + Real.sqrt 2) := by
  have hcos_pos : ∀ x ∈ uIcc (0 : ℝ) (π / 4), 0 < Real.cos x := by
    intro x hx
    rw [uIcc_of_le (by positivity)] at hx
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [hx.1, hx.2, Real.pi_pos]
  have hsin_ge : ∀ x ∈ uIcc (0 : ℝ) (π / 4), 0 ≤ Real.sin x := by
    intro x hx
    rw [uIcc_of_le (by positivity)] at hx
    apply Real.sin_nonneg_of_nonneg_of_le_pi hx.1
    linarith [hx.2, Real.pi_pos]
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) (π / 4),
      HasDerivAt (fun y => Real.log ((1 + Real.sin y) / Real.cos y)) (1 / Real.cos x) x := by
    intro x hx
    have hc := hcos_pos x hx
    have hs := hsin_ge x hx
    have hq : HasDerivAt (fun y => (1 + Real.sin y) / Real.cos y)
        ((Real.cos x * Real.cos x - (1 + Real.sin x) * (-Real.sin x)) / Real.cos x ^ 2) x :=
      ((hasDerivAt_const x (1 : ℝ)).add (Real.hasDerivAt_sin x)).div (Real.hasDerivAt_cos x)
        hc.ne' |>.congr_deriv (by simp only [Pi.add_apply]; ring)
    have hpos : 0 < (1 + Real.sin x) / Real.cos x := by positivity
    convert hq.log hpos.ne' using 1
    have hsc := Real.sin_sq_add_cos_sq x
    field_simp
    nlinarith [hsc]
  have hint : IntervalIntegrable (fun x => 1 / Real.cos x) MeasureTheory.volume 0 (π / 4) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const Real.continuous_cos.continuousOn
    intro x hx; exact (hcos_pos x hx).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  rw [Real.sin_pi_div_four, Real.cos_pi_div_four, Real.sin_zero, Real.cos_zero]
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hval : (1 + Real.sqrt 2 / 2) / (Real.sqrt 2 / 2) = 1 + Real.sqrt 2 := by
    field_simp
    nlinarith [Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2,
      Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  rw [hval]
  simp

end RhG1Lean
