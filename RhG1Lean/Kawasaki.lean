/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.

# Kawasaki (euclidiano y de Lorentz) y las esquinas de las bahías

* **La flecha de Kawasaki.** Doblar el papel por una recta con ángulo α es la reflexión z ↦ e^{2iα} z̄
  (la flecha se voltea). Dos dobleces seguidos son un giro de 2(β − α). Al dar la vuelta completa con
  pares de pliegues (α₁, α₂), (α₃, α₄), … el papel regresa a su sitio ⇔ la suma alterna Σ(α₂ₖ − α₂ₖ₋₁)
  es múltiplo de π; si está entre 0 y 2π, ⇔ vale π (180°): **el teorema de Kawasaki**.
* **Kawasaki de Lorentz (campo infinito).** En 1+1 dimensiones con coordenadas de cono de luz, la
  reflexión por la recta de rapidez η es (u, v) ↦ (e^{2η} v, e^{−2η} u); dos seguidas son un *boost*.
  Cerrar ⇔ la suma alterna de rapideces es **exactamente 0** (no hay "módulo π": las rapideces no dan
  la vuelta). Lo finito (ángulos, compacto) contra lo infinito (rapideces, no compacto).
* **Vértices de ángulos iguales.** Alrededor de un punto crítico de orden m de una función holomorfa las
  líneas de empate son 2(m+1) rayos a ángulos iguales y el signo (la flecha) se voltea en cada uno; un
  vértice de 2m pliegues iguales cumple Kawasaki. m = 2: las esquinas de las bahías (4 × 90°);
  m = 3: 6 × 60° (la molécula de TreeMaker, el nacimiento de una bahía).
* **Espejo ⇒ Kawasaki.** Si la sucesión de sectores es simétrica por un espejo que pasa por dos
  pliegues, la suma alterna es 0. La ecuación funcional (q·q♯ = 1) hace eso con todo círculo centrado
  en la pared.
* **Esquinas = puntos críticos.** Si |q| = 1 a lo largo de la pared y la fase de q está quieta (v = 0),
  entonces q′ = 0. **Puerta = cero doble**: con ζ = R(1 + q), un huésped en una esquina (q = −1, q′ = 0)
  es un cero doble, y al revés. Todo cero (con R ≠ 0) vive en el patrón de empate |q| = 1.
* **Azimut = tilt** (Cauchy–Riemann): para g holomorfa, la razón de cambio de Re g hacia adentro
  (tilt) es igual a la de Im g a lo largo de la pared (azimut): las dos son Re g′.
* **Contracción de Lorentz de la bahía**: h = r·√(1 − k²) con k = d/r (velocidad β = k).
* **Ford**: el círculo de 0/1 toca al de 1/n en (n/(n²+1), 1/(n²+1)); la altura según el ángulo es
  sin²(φ/2); la inversión −1/z (un elemento de Lorentz discreto) lleva el peine infinito n + i al
  círculo finito.
* **Carga imagen**: la pared es equipotencial de una carga y su imagen; las esquinas son los puntos de
  campo cero (estancamiento) y el equilibrio de la fuerza imagen con el campo uniforme es d·c = 1/2.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

namespace RhG1Lean
open Complex ComplexConjugate

/-! ## Kawasaki euclidiano -/

/-- Doblar por la recta de ángulo α: la reflexión z ↦ e^{2iα} z̄ (la flecha se voltea). -/
noncomputable def reflE (α : ℝ) (z : ℂ) : ℂ := exp (2 * α * I) * conj z

/-- Dos dobleces seguidos son un giro de 2(β − α). -/
theorem reflE_reflE (α β : ℝ) (z : ℂ) : reflE β (reflE α z) = exp (2 * (β - α) * I) * z := by
  unfold reflE
  have h : conj (exp (2 * (α : ℂ) * I)) = exp (-(2 * (α : ℂ) * I)) := by
    rw [← Complex.exp_conj]
    congr 1
    simp [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  rw [map_mul, Complex.conj_conj, h, ← mul_assoc, ← Complex.exp_add]
  congr 1
  ring

/-- Doblar por pares de pliegues (α₁, α₂), (α₃, α₄), … -/
noncomputable def doblarE : List (ℝ × ℝ) → ℂ → ℂ
  | [], z => z
  | (a, b) :: l, z => doblarE l (reflE b (reflE a z))

/-- La suma alterna Σ(α₂ₖ − α₂ₖ₋₁): la suma de un sector sí y uno no. -/
def sumaAlterna : List (ℝ × ℝ) → ℝ
  | [] => 0
  | (a, b) :: l => (b - a) + sumaAlterna l

/-- Toda la vuelta de dobleces es un giro por el doble de la suma alterna. -/
theorem doblarE_eq (l : List (ℝ × ℝ)) (z : ℂ) :
    doblarE l z = exp (2 * (sumaAlterna l : ℂ) * I) * z := by
  induction l generalizing z with
  | nil => simp [doblarE, sumaAlterna]
  | cons p l ih =>
    obtain ⟨a, b⟩ := p
    simp only [doblarE, sumaAlterna]
    rw [ih, reflE_reflE, ← mul_assoc, ← Complex.exp_add]
    congr 1
    push_cast
    ring

/-- **Kawasaki (cierre)**: el papel regresa a su sitio ⇔ la suma alterna es múltiplo de π. -/
theorem kawasaki_euclidiano (l : List (ℝ × ℝ)) :
    (∀ z, doblarE l z = z) ↔ ∃ n : ℤ, sumaAlterna l = n * Real.pi := by
  constructor
  · intro h
    have h1 := h 1
    rw [doblarE_eq, mul_one, Complex.exp_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    refine ⟨n, ?_⟩
    have := congrArg Complex.im hn
    simp at this
    linarith
  · rintro ⟨n, hn⟩ z
    rw [doblarE_eq, hn]
    have : exp (2 * (((n : ℝ) * Real.pi : ℝ) : ℂ) * I) = 1 := by
      rw [Complex.exp_eq_one_iff]
      exact ⟨n, by push_cast; ring⟩
    rw [this, one_mul]

/-- **Kawasaki (180°)**: si la suma de un sector sí y uno no está entre 0 y 2π, el papel cierra ⇔ vale π. -/
theorem kawasaki_180 (l : List (ℝ × ℝ)) (h0 : 0 < sumaAlterna l) (h2 : sumaAlterna l < 2 * Real.pi) :
    (∀ z, doblarE l z = z) ↔ sumaAlterna l = Real.pi := by
  rw [kawasaki_euclidiano]
  have hp := Real.pi_pos
  constructor
  · rintro ⟨n, hn⟩
    have h1 : (0 : ℝ) < n := by
      by_contra hc
      push Not at hc
      nlinarith [mul_le_mul_of_nonneg_right hc hp.le]
    have h2' : (n : ℝ) < 2 := by
      by_contra hc
      push Not at hc
      nlinarith [mul_le_mul_of_nonneg_right hc hp.le]
    have hn1 : n = 1 := by
      have a : (0 : ℤ) < n := by exact_mod_cast h1
      have b : n < 2 := by exact_mod_cast h2'
      omega
    rw [hn, hn1]
    simp
  · intro h
    exact ⟨1, by rw [h]; simp⟩

/-! ## Kawasaki de Lorentz (rapideces: el campo infinito) -/

/-- Reflexión de Lorentz por la recta de rapidez η, en coordenadas de cono de luz (u, v). -/
noncomputable def reflL (η : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (Real.exp (2 * η) * p.2, Real.exp (-(2 * η)) * p.1)

/-- Dos reflexiones de Lorentz son un *boost* de rapidez 2(β − α). -/
theorem reflL_reflL (α β : ℝ) (p : ℝ × ℝ) :
    reflL β (reflL α p) = (Real.exp (2 * (β - α)) * p.1, Real.exp (-(2 * (β - α))) * p.2) := by
  unfold reflL
  ext
  · simp only
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  · simp only
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring

/-- Doblar el plano de Minkowski por pares de pliegues. -/
noncomputable def doblarL : List (ℝ × ℝ) → ℝ × ℝ → ℝ × ℝ
  | [], p => p
  | (a, b) :: l, p => doblarL l (reflL b (reflL a p))

theorem doblarL_eq (l : List (ℝ × ℝ)) (p : ℝ × ℝ) :
    doblarL l p = (Real.exp (2 * sumaAlterna l) * p.1, Real.exp (-(2 * sumaAlterna l)) * p.2) := by
  induction l generalizing p with
  | nil => simp [doblarL, sumaAlterna]
  | cons x l ih =>
    obtain ⟨a, b⟩ := x
    simp only [doblarL, sumaAlterna]
    rw [ih, reflL_reflL]
    ext
    · simp only
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    · simp only
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- **Kawasaki de Lorentz**: el plano de Minkowski cierra ⇔ la suma alterna de rapideces es exactamente 0. -/
theorem kawasaki_lorentz (l : List (ℝ × ℝ)) : (∀ p, doblarL l p = p) ↔ sumaAlterna l = 0 := by
  constructor
  · intro h
    have h1 := congrArg Prod.fst (h (1, 1))
    rw [doblarL_eq] at h1
    simp only [mul_one] at h1
    have := Real.exp_eq_one_iff (2 * sumaAlterna l) |>.mp h1
    linarith
  · intro h p
    rw [doblarL_eq, h]
    simp

/-! ## Vértices de ángulos iguales y la flecha que se voltea -/

/-- Girar π/(m+1) voltea el signo de Re(c·z^{m+1}): en un punto crítico de orden m las 2(m+1) líneas de
empate están a ángulos iguales y la flecha (el signo de log|q|) se voltea en cada una. -/
theorem flecha_se_voltea (c u : ℂ) (m : ℕ) :
    (c * (u * exp (Real.pi / (m + 1) * I)) ^ (m + 1)).re = -(c * u ^ (m + 1)).re := by
  have hm : ((m : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have h : exp (Real.pi / (m + 1) * I) ^ (m + 1) = -1 := by
    rw [← Complex.exp_nat_mul]
    have : ((m + 1 : ℕ) : ℂ) * (Real.pi / (m + 1) * I) = Real.pi * I := by
      push_cast
      field_simp
    rw [this, Complex.exp_pi_mul_I]
  rw [mul_pow, h]
  simp

/-- Un vértice con pliegues a ángulos kθ (k = 0, …, 2n−1), por pares. -/
noncomputable def verticeIgual (θ : ℝ) : ℕ → List (ℝ × ℝ)
  | 0 => []
  | n + 1 => (2 * n * θ, (2 * n + 1) * θ) :: verticeIgual θ n

theorem sumaAlterna_verticeIgual (θ : ℝ) (n : ℕ) : sumaAlterna (verticeIgual θ n) = n * θ := by
  induction n with
  | zero => simp [verticeIgual, sumaAlterna]
  | succ n ih =>
    simp only [verticeIgual, sumaAlterna, ih]
    push_cast
    ring

/-- **Todo vértice de 2m pliegues iguales (π/m) cumple Kawasaki**: m = 2 (esquina, 4 × 90°),
m = 3 (6 × 60°, la molécula de TreeMaker). -/
theorem kawasaki_vertice_igual (m : ℕ) (hm : 0 < m) :
    ∀ z, doblarE (verticeIgual (Real.pi / m) m) z = z := by
  rw [kawasaki_euclidiano]
  refine ⟨1, ?_⟩
  rw [sumaAlterna_verticeIgual]
  have : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp
  simp

/-! ## Espejo ⇒ Kawasaki -/

/-- Suma alterna de una lista de sectores: s₁ − s₂ + s₃ − ⋯ -/
def alterna : List ℝ → ℝ
  | [] => 0
  | x :: l => x - alterna l

theorem alterna_append (l l' : List ℝ) :
    alterna (l ++ l') = alterna l + (-1) ^ l.length * alterna l' := by
  induction l with
  | nil => simp [alterna]
  | cons x l ih =>
    simp only [List.cons_append, alterna, ih, List.length_cons, pow_succ]
    ring

theorem alterna_reverse (l : List ℝ) : alterna l.reverse = (-1) ^ (l.length + 1) * alterna l := by
  induction l with
  | nil => simp [alterna]
  | cons x l ih =>
    rw [List.reverse_cons, alterna_append, ih]
    simp only [alterna, List.length_reverse, List.length_cons]
    ring

/-- **Espejo ⇒ Kawasaki**: los sectores s₁, …, sₘ seguidos de su reflejo sₘ, …, s₁ (un espejo que pasa por
dos pliegues) tienen suma alterna 0. -/
theorem kawasaki_espejo (l : List ℝ) : alterna (l ++ l.reverse) = 0 := by
  have h : ((-1 : ℝ) ^ l.length) * (-1) ^ l.length = 1 := by
    rw [← mul_pow]
    norm_num
  rw [alterna_append, alterna_reverse, pow_succ]
  linear_combination (-alterna l) * h

/-! ## Esquinas, puertas y ceros -/

/-- **Todo cero vive en el patrón de empate**: si ζ = R(1 + q) se anula y R ≠ 0, entonces q = −1 y |q| = 1. -/
theorem cero_en_empate {R q : ℂ} (hR : R ≠ 0) (hz : R * (1 + q) = 0) : q = -1 ∧ ‖q‖ = 1 := by
  have h : 1 + q = 0 := (mul_eq_zero.mp hz).resolve_left hR
  have hq : q = -1 := by linear_combination h
  exact ⟨hq, by rw [hq, norm_neg, norm_one]⟩

/-- **La esquina es un punto crítico**: si |q| = 1 a lo largo de la pared cerca de ½ + it₀ y la fase de q está
quieta ahí (Re(q′·q̄) = 0, es decir v = 0), entonces q′ = 0. -/
theorem esquina_critica {q : ℂ → ℂ} {q' : ℂ} {t₀ : ℝ}
    (hd : HasDerivAt q q' (1 / 2 + (t₀ : ℂ) * I))
    (hmod : ∀ᶠ t : ℝ in nhds t₀, ‖q (1 / 2 + (t : ℂ) * I)‖ = 1)
    (hvel : (q' * conj (q (1 / 2 + (t₀ : ℂ) * I))).re = 0) : q' = 0 := by
  have hp : HasDerivAt (fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ) * I) I t₀ := by
    simpa using ((hasDerivAt_id t₀).ofReal_comp.mul_const I).const_add (1 / 2 : ℂ)
  have hγ : HasDerivAt (fun t : ℝ => q (1 / 2 + (t : ℂ) * I)) (q' * I) t₀ := hd.comp t₀ hp
  have hre : HasDerivAt (fun t : ℝ => (q (1 / 2 + (t : ℂ) * I)).re) (q' * I).re t₀ := by
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t₀ hγ
  have him : HasDerivAt (fun t : ℝ => (q (1 / 2 + (t : ℂ) * I)).im) (q' * I).im t₀ := by
    exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt t₀ hγ
  have hN := (hre.mul hre).add (him.mul him)
  have hconst : (fun t : ℝ => (q (1 / 2 + (t : ℂ) * I)).re * (q (1 / 2 + (t : ℂ) * I)).re
      + (q (1 / 2 + (t : ℂ) * I)).im * (q (1 / 2 + (t : ℂ) * I)).im) =ᶠ[nhds t₀] fun _ => 1 := by
    filter_upwards [hmod] with t ht
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, ht]
    norm_num
  have h0 := (hasDerivAt_const t₀ (1 : ℝ)).congr_of_eventuallyEq hconst
  have hu := hN.unique h0
  have hn1 : ‖q (1 / 2 + (t₀ : ℂ) * I)‖ = 1 := hmod.self_of_nhds
  have hn : (q (1 / 2 + (t₀ : ℂ) * I)).re * (q (1 / 2 + (t₀ : ℂ) * I)).re
      + (q (1 / 2 + (t₀ : ℂ) * I)).im * (q (1 / 2 + (t₀ : ℂ) * I)).im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hn1]
    norm_num
  set b := q (1 / 2 + (t₀ : ℂ) * I)
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.conj_re,
    Complex.conj_im] at hu hvel
  apply Complex.ext
  · simp only [Complex.zero_re]
    linear_combination b.re * hvel + (b.im / 2) * hu - q'.re * hn
  · simp only [Complex.zero_im]
    linear_combination b.im * hvel - (b.re / 2) * hu - q'.im * hn

/-- **La puerta es un cero doble**: con ζ = R(1 + q), si q = −1 y q′ = 0 en s, entonces ζ′(s) = 0. -/
theorem puerta_cero_doble {R q : ℂ → ℂ} {R' : ℂ} {s : ℂ} (hR : HasDerivAt R R' s) (hq : HasDerivAt q 0 s)
    (h1 : q s = -1) : HasDerivAt (fun z => R z * (1 + q z)) 0 s := by
  have h := hR.mul (hq.const_add 1)
  convert h using 1
  rw [h1]
  ring

/-- **Y al revés**: un cero doble de ζ = R(1 + q) con R ≠ 0 es un huésped en una esquina (q = −1, q′ = 0). -/
theorem cero_doble_es_esquina {R q : ℂ → ℂ} {R' q' : ℂ} {s : ℂ} (hR : HasDerivAt R R' s)
    (hq : HasDerivAt q q' s) (hRs : R s ≠ 0) (hz : R s * (1 + q s) = 0)
    (hz' : HasDerivAt (fun z => R z * (1 + q z)) 0 s) : q s = -1 ∧ q' = 0 := by
  have hq1 : 1 + q s = 0 := (mul_eq_zero.mp hz).resolve_left hRs
  refine ⟨by linear_combination hq1, ?_⟩
  have h := (hR.mul (hq.const_add 1)).unique hz'
  rw [hq1, mul_zero, zero_add] at h
  exact (mul_eq_zero.mp h).resolve_left hRs

/-- **Azimut = tilt** (Cauchy–Riemann): la razón de Re g hacia adentro (σ) y la de Im g a lo largo de la
pared (t) son las dos Re g′. Con g = log q: el tilt de log|q| es el azimut de arg q (= −2v en la pared). -/
theorem azimut_igual_tilt {g : ℂ → ℂ} {g' : ℂ} {σ t : ℝ} (hg : HasDerivAt g g' (σ + t * I)) :
    HasDerivAt (fun x : ℝ => (g (x + t * I)).re) g'.re σ ∧
      HasDerivAt (fun y : ℝ => (g (σ + y * I)).im) g'.re t := by
  constructor
  · have hp : HasDerivAt (fun x : ℝ => (x : ℂ) + t * I) 1 σ := by
      simpa using ((hasDerivAt_id σ).ofReal_comp).add_const ((t : ℂ) * I)
    have h2 : HasDerivAt (fun x : ℝ => g (x + t * I)) (g' * 1) σ := hg.comp σ hp
    have h3 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt σ h2
    rw [mul_one] at h3
    exact h3
  · have hp : HasDerivAt (fun y : ℝ => (σ : ℂ) + y * I) I t := by
      simpa using ((hasDerivAt_id t).ofReal_comp.mul_const I).const_add (σ : ℂ)
    have h2 : HasDerivAt (fun y : ℝ => g (σ + y * I)) (g' * I) t := hg.comp t hp
    have h3 : HasDerivAt (fun y : ℝ => (g (σ + y * I)).im) (g' * I).im t :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt t h2
    simpa using h3

/-! ## Lorentz, Ford y la carga imagen -/

/-- **Contracción de Lorentz de la bahía**: con h² + d² = r² y velocidad β = k = d/r, h = r·√(1 − k²). -/
theorem contraccion_lorentz {d h r : ℝ} (hr : 0 < r) (hh : 0 ≤ h) (hpit : h ^ 2 + d ^ 2 = r ^ 2) :
    h = r * Real.sqrt (1 - (d / r) ^ 2) := by
  have h1 : 1 - (d / r) ^ 2 = (h / r) ^ 2 := by
    field_simp
    linarith
  rw [h1, Real.sqrt_sq (div_nonneg hh hr.le)]
  field_simp

/-- **Tangencias de Ford**: el círculo de 0/1 y el de 1/n se tocan en (n/(n²+1), 1/(n²+1)). -/
theorem ford_tangencia (n : ℝ) (hn : n ≠ 0) :
    (n / (n ^ 2 + 1)) ^ 2 + (1 / (n ^ 2 + 1) - 1 / 2) ^ 2 = (1 / 2) ^ 2 ∧
      (n / (n ^ 2 + 1) - 1 / n) ^ 2 + (1 / (n ^ 2 + 1) - 1 / (2 * n ^ 2)) ^ 2 = (1 / (2 * n ^ 2)) ^ 2 := by
  have h1 : n ^ 2 + 1 ≠ 0 := by positivity
  constructor <;> (field_simp; ring)

/-- **Altura según el ángulo**: si cot(φ/2) = n, la altura del punto de tangencia 1/(n²+1) es sin²(φ/2). -/
theorem altura_por_angulo (u : ℝ) (hs : Real.sin u ≠ 0) :
    1 / ((Real.cos u / Real.sin u) ^ 2 + 1) = Real.sin u ^ 2 := by
  have h := Real.sin_sq_add_cos_sq u
  have h2 : (Real.cos u / Real.sin u) ^ 2 + 1 = 1 / Real.sin u ^ 2 := by
    field_simp
    linarith
  rw [h2, one_div_one_div]

/-- **Del infinito al finito**: la inversión −1/z (elemento del grupo modular, un Lorentz discreto) lleva el
peine infinito n + i a los puntos de tangencia (−n + i)/(n² + 1) del círculo finito de 0/1. -/
theorem del_infinito_al_finito (n : ℝ) : -1 / ((n : ℂ) + I) = (-n + I) / ((n : ℂ) ^ 2 + 1) := by
  have h1 : (n : ℂ) + I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
  have h2 : (n : ℂ) ^ 2 + 1 ≠ 0 := by
    have : ((n : ℂ) ^ 2 + 1) = ((n ^ 2 + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [this]
    exact_mod_cast (by positivity : (n ^ 2 + 1 : ℝ) ≠ 0)
  rw [div_eq_div_iff h1 h2]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **La pared es equipotencial**: un punto de la pared equidista de la carga (a distancia d) y de su imagen. -/
theorem pared_equipotencial (d τ : ℝ) :
    Complex.normSq ((τ : ℂ) * I - d) = Complex.normSq ((τ : ℂ) * I + d) := by
  simp [Complex.normSq_apply]

/-- **Esquinas = estancamiento**: el campo normal de la carga y su imagen sobre la pared, 2d/(d² + τ²), iguala al
campo uniforme 2c exactamente en τ² = d/c − d² (los extremos del retroceso). -/
theorem estancamiento_esquina {d c τ : ℝ} (hd : 0 < d) (hc : 0 < c) :
    2 * d / (d ^ 2 + τ ^ 2) = 2 * c ↔ τ ^ 2 = d / c - d ^ 2 := by
  have h1 : d ^ 2 + τ ^ 2 ≠ 0 := by positivity
  rw [div_eq_iff h1, eq_sub_iff_add_eq, eq_div_iff hc.ne']
  constructor <;> intro h <;> linarith

/-- **Equilibrio de la fuerza imagen**: la energía −log(2d) + 2cd tiene derivada −1/d + 2c, que se anula ⇔ d·c = 1/2. -/
theorem equilibrio_imagen {d c : ℝ} (hd : 0 < d) : -1 / d + 2 * c = 0 ↔ d * c = 1 / 2 := by
  rw [div_add' _ _ _ hd.ne', div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · linarith
    · exact absurd h hd.ne'
  · intro h
    left
    linarith

/-- **El reloj de casa es el área de un segmento circular.** En el modelo de disco (apagón a distancia d de la pared,
retroceso de semilargo h, r² = h² + d², c = d/r²), el giro hacia atrás de la rosa en el retroceso,
2·arctan(h/d) − 2ch, es 2α − sin 2α con cos α = d/r = k: el doble del área del segmento que la pared corta al disco,
dividido entre r². En lenguaje de Lorentz (β = k): 2 arccos β − 2β√(1 − β²); se cierra (→ 0) en el cono de luz β = 1. -/
theorem reloj_de_casa {d h r : ℝ} (hd : 0 < d) (hh : 0 < h) (hr : 0 < r) (hp : h ^ 2 + d ^ 2 = r ^ 2) :
    2 * Real.arctan (h / d) - 2 * (d / r ^ 2) * h
      = 2 * Real.arccos (d / r) - Real.sin (2 * Real.arccos (d / r)) := by
  have hk0 : 0 < d / r := div_pos hd hr
  have hdr : d ≤ r := by nlinarith
  have hk1 : d / r ≤ 1 := by rw [div_le_iff₀ hr]; linarith
  have hs : Real.sqrt (1 - (d / r) ^ 2) = h / r := by
    have h1 : 1 - (d / r) ^ 2 = (h / r) ^ 2 := by
      field_simp
      linarith
    rw [h1, Real.sqrt_sq (div_nonneg hh.le hr.le)]
  have ha : Real.arccos (d / r) = Real.arctan (h / d) := by
    rw [Real.arccos_eq_arctan hk0, hs]
    congr 1
    field_simp
  rw [Real.sin_two_mul, Real.sin_arccos, Real.cos_arccos (by linarith) hk1, hs, ha]
  field_simp

/-- **El modelo lineal pone su cero en la pared.** Cerca de un apagón (a distancia d de la pared), la costura
G + G♯ con G lineal es Z(u) = B(u − d) − B̄(u + d). Si B ≠ 0 y d ≠ 0, todo cero tiene Re u = 0 (está en la pared),
a la altura Im u = −d·Re B/Im B = −d·cot(arg B). Sin la deriva (tilt) no hay escapados. -/
theorem modelo_lineal_en_pared {B u : ℂ} {d : ℝ} (hB : B ≠ 0) (hd : d ≠ 0)
    (hz : B * (u - d) - conj B * (u + d) = 0) : u.re = 0 ∧ u.im * B.im = -d * B.re := by
  have h1 := congrArg Complex.re hz
  have h2 := congrArg Complex.im hz
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.zero_re, Complex.zero_im] at h1 h2
  have hre : B.im * u.re = 0 := by linarith
  have him : u.im * B.im = -d * B.re := by linarith
  refine ⟨?_, him⟩
  rcases mul_eq_zero.mp hre with hy | ha
  · exfalso
    apply hB
    have hx : B.re = 0 := by
      have : d * B.re = 0 := by rw [hy] at him; linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hd
      · exact h
    exact Complex.ext hx hy
  · exact ha

/-- **El modelo inclinado (Apolonio con deriva).** Si B(u − d)e^{cu} = B̄(u + d)e^{−cu} con B ≠ 0, entonces
|u + d| = |u − d|·e^{2c·Re u}: el cero está en la curva de empate del modelo (el círculo de Apolonio doblado por el tilt). -/
theorem modelo_inclinado_apolonio {B u : ℂ} {d c : ℝ} (hB : B ≠ 0)
    (hz : B * (u - d) * exp (c * u) = conj B * (u + d) * exp (-(c * u))) :
    ‖u + d‖ = ‖u - d‖ * Real.exp (2 * c * u.re) := by
  have h := congrArg norm hz
  simp only [norm_mul, Complex.norm_exp, Complex.norm_conj] at h
  have hB' : 0 < ‖B‖ := norm_pos_iff.mpr hB
  have hre1 : ((c : ℂ) * u).re = c * u.re := by simp
  have hre2 : (-((c : ℂ) * u)).re = -(c * u.re) := by simp
  rw [hre1, hre2] at h
  have he : Real.exp (2 * c * u.re) = Real.exp (c * u.re) / Real.exp (-(c * u.re)) := by
    rw [← Real.exp_sub]
    ring_nf
  rw [he]
  have hpos : 0 < Real.exp (-(c * u.re)) := Real.exp_pos _
  field_simp
  have := h.symm
  nlinarith [this, hB', Real.exp_pos (c * u.re), hpos, norm_nonneg (u + d), norm_nonneg (u - d)]

/-- **La ventana en rapidez (gudermanniana): del infinito al finito.** Con k = tanh δ (δ = rapidez de la bahía), la
ventana del reloj de casa 2 arccos k − sin(2 arccos k) es π − 2·arcsin(tanh δ) − 2·tanh δ/cosh δ; arcsin(tanh δ) = gd(δ)
lleva la rapidez (infinita) a un ángulo (finito). -/
theorem ventana_gudermann (δ : ℝ) :
    2 * Real.arccos (Real.tanh δ) - Real.sin (2 * Real.arccos (Real.tanh δ))
      = Real.pi - 2 * Real.arcsin (Real.tanh δ) - 2 * Real.tanh δ / Real.cosh δ := by
  have hc : 0 < Real.cosh δ := Real.cosh_pos δ
  have hid := Real.cosh_sq_sub_sinh_sq δ
  have ht : Real.tanh δ = Real.sinh δ / Real.cosh δ := Real.tanh_eq_sinh_div_cosh δ
  have h1 : 1 - Real.tanh δ ^ 2 = (1 / Real.cosh δ) ^ 2 := by
    rw [ht]; field_simp; linarith
  have hs : Real.sqrt (1 - Real.tanh δ ^ 2) = 1 / Real.cosh δ := by
    rw [h1, Real.sqrt_sq (by positivity)]
  have hb : Real.tanh δ ^ 2 ≤ 1 := by nlinarith [h1, sq_nonneg (1 / Real.cosh δ)]
  have hlo : -1 ≤ Real.tanh δ := by nlinarith [sq_nonneg (Real.tanh δ + 1)]
  have hhi : Real.tanh δ ≤ 1 := by nlinarith [sq_nonneg (Real.tanh δ - 1)]
  rw [Real.sin_two_mul, Real.sin_arccos, Real.cos_arccos hlo hhi, hs, Real.arccos_eq_pi_div_two_sub_arcsin]
  field_simp

/-- **Un apagón se puede "reflejar" cambiando de costura ⇔ su fase está candada (modelo lineal).**
La costura B(s − ρ) (cero a la derecha, a distancia d: una bahía) y la costura B(s − ρ*) (cero en el espejo: sin bahía)
dan la misma suma E + E♯ = B(s − ρ) − B̄(s − ρ*) para todo s ⇔ Re B = 0, es decir, β = arg B = ±π/2. -/
theorem apagon_reflejable_iff {B : ℂ} {d t₀ : ℝ} (hd : d ≠ 0) :
    (∀ s : ℂ, B * (s - (1 / 2 + d + t₀ * I)) - conj B * (s - (1 / 2 - d + t₀ * I))
        = B * (s - (1 / 2 - d + t₀ * I)) - conj B * (s - (1 / 2 + d + t₀ * I))) ↔ B.re = 0 := by
  constructor
  · intro h
    have h0 := h 0
    have hre := congrArg Complex.re h0
    simp only [Complex.sub_re, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.sub_im, Complex.mul_im, Complex.div_ofNat_re,
      Complex.div_ofNat_im, Complex.one_re, Complex.one_im] at hre
    have : 4 * d * B.re = 0 := by linarith
    rcases mul_eq_zero.mp this with h4 | h4
    · exact absurd (by linarith : d = 0) hd
    · exact h4
  · intro hB s
    have hconj : conj B = -B := by
      apply Complex.ext
      · simp [hB]
      · simp
    rw [hconj]
    ring

/-- **Multiplicador de Denjoy–Wolff del cero al revés (modelo de disco).** Con la deriva c = d/r² y la velocidad k = d/r,
λ = 1 + v·(d² + τ²)/d, donde v = c − d/(d² + τ²) es la velocidad de la rosa en el cero, vale k²(1 + τ²/d²). -/
theorem multiplicador_dw {d r τ : ℝ} (hd : 0 < d) (hr : 0 < r) :
    1 + (d / r ^ 2 - d / (d ^ 2 + τ ^ 2)) * (d ^ 2 + τ ^ 2) / d = (d / r) ^ 2 * (1 + τ ^ 2 / d ^ 2) := by
  have h1 : d ^ 2 + τ ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- **La puerta es el punto parabólico:** con h² + d² = r², el multiplicador k²(1 + τ²/d²) vale 1 ⇔ τ² = h² (el cero en la
esquina), y es < 1 ⇔ τ² < h² (el cero dentro del retroceso: atractor). -/
theorem multiplicador_parabolico_iff {d r h τ : ℝ} (hd : 0 < d) (hr : 0 < r) (hp : h ^ 2 + d ^ 2 = r ^ 2) :
    ((d / r) ^ 2 * (1 + τ ^ 2 / d ^ 2) = 1 ↔ τ ^ 2 = h ^ 2) ∧
      ((d / r) ^ 2 * (1 + τ ^ 2 / d ^ 2) < 1 ↔ τ ^ 2 < h ^ 2) := by
  have hdr : (d / r) ^ 2 * (1 + τ ^ 2 / d ^ 2) = (d ^ 2 + τ ^ 2) / r ^ 2 := by
    field_simp
  rw [hdr]
  have hr2 : 0 < r ^ 2 := by positivity
  constructor
  · rw [div_eq_one_iff_eq hr2.ne']
    constructor <;> intro h <;> linarith
  · rw [div_lt_one hr2]
    constructor <;> intro h <;> linarith

end RhG1Lean
