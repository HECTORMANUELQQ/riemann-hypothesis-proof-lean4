import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# La costura canónica (R1–R2): las formas 1, 2 y 3 de la pieza faltante son una sola

Mitad exacta `E_α = (Λ + Λ′/α)/2`, con `Λ = E_α + E_α♯` y `w = Λ′/Λ`. El espejo da `q_α = E_α♯/E_α = (α − w)/(α + w)`.

* `mitad_canonica_suma`, `mitad_canonica_cociente`: las dos mitades suman `Λ` y su cociente es la transformada de Cayley de `w`.
* `cayley_lt_iff`, `cayley_gt_iff`, `cayley_eq_iff`: `|q_α| < 1 ⇔ Re w > 0` (pasividad), `|q_α| > 1 ⇔ Re w < 0` (bahía),
  `|q_α| = 1 ⇔ Re w = 0` (pared).
* `bahia_no_depende_de_alfa`: la bahía es la misma para todo `α > 0`.
* `fase_canonica_deriv`: en la pared, la fase `φ = 2·arctan(Ξ′/(αΞ))` tiene derivada `−2α𝓛/(α²Ξ² + Ξ′²)`, con `𝓛 = Ξ′² − ΞΞ″`.
* `fase_gira_un_lado`, `fase_retrocede_iff`: la fase gira siempre hacia el mismo lado si `𝓛 > 0`; retrocede exactamente donde `𝓛 < 0`.
* `carga_propia_par`: un par de ceros `γ ± iδ` aporta `−2/δ²` a `−(log Ξ)″` en su centro.
* `par_calor_deriv`, `par_calor_puerta`: con el flujo de calor, el par aislado cumple `δ′ = −1/δ` y llega a la recta en `λ = δ₀²/2`.
* `par_real_calor_deriv`: dos ceros reales a distancia `g` cumplen `g′ = 4/g` (hacia atrás chocan en `λ = −g₀²/8`).
* `puerta_por_carga`: tiempo a la puerta × carga propia = `−1`.
* `apagon_no_cruza_borde`: en el borde de la bahía (Re w = 0) nunca vale w = −α; por eso el apagón de E_α no puede salir de su bahía al variar α.
-/

namespace RhG1Lean

open Complex

theorem mitad_canonica_suma {K : Type*} [Field K] (L D α : K) (h2 : (2 : K) ≠ 0) :
    (L + D / α) / 2 + (L - D / α) / 2 = L := by
  field_simp
  ring

theorem mitad_canonica_cociente {K : Type*} [Field K] {L D α : K} (h2 : (2 : K) ≠ 0) (hL : L ≠ 0)
    (hα : α ≠ 0) (h : α * L + D ≠ 0) :
    ((L - D / α) / 2) / ((L + D / α) / 2) = (α - D / L) / (α + D / L) := by
  have e1 : (L + D / α) / 2 = (α * L + D) / (2 * α) := by field_simp
  have e2 : (L - D / α) / 2 = (α * L - D) / (2 * α) := by field_simp
  have e3 : α + D / L = (α * L + D) / L := by field_simp
  have e4 : α - D / L = (α * L - D) / L := by field_simp
  rw [e1, e2, e3, e4, div_div_div_cancel_right₀ (mul_ne_zero h2 hα), div_div_div_cancel_right₀ hL]

theorem normSq_alfa_menos (α : ℝ) (w : ℂ) :
    Complex.normSq ((α : ℂ) - w) = (α - w.re) ^ 2 + w.im ^ 2 := by
  rw [Complex.normSq_apply]; simp; ring

theorem normSq_alfa_mas (α : ℝ) (w : ℂ) :
    Complex.normSq ((α : ℂ) + w) = (α + w.re) ^ 2 + w.im ^ 2 := by
  rw [Complex.normSq_apply]; simp; ring

theorem sq_norm_dif (α : ℝ) (w : ℂ) :
    ‖(α : ℂ) + w‖ ^ 2 - ‖(α : ℂ) - w‖ ^ 2 = 4 * α * w.re := by
  rw [Complex.sq_norm, Complex.sq_norm, normSq_alfa_menos, normSq_alfa_mas]; ring

theorem cayley_lt_iff {α : ℝ} (hα : 0 < α) (w : ℂ) :
    ‖(α : ℂ) - w‖ < ‖(α : ℂ) + w‖ ↔ 0 < w.re := by
  rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)]
  have h := sq_norm_dif α w
  constructor
  · intro h1
    have : 0 < 4 * α * w.re := by linarith
    by_contra hn
    have hn' : w.re ≤ 0 := not_lt.mp hn
    nlinarith
  · intro h1
    have : 0 < 4 * α * w.re := by positivity
    linarith

theorem cayley_gt_iff {α : ℝ} (hα : 0 < α) (w : ℂ) :
    ‖(α : ℂ) + w‖ < ‖(α : ℂ) - w‖ ↔ w.re < 0 := by
  rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)]
  have h := sq_norm_dif α w
  constructor
  · intro h1
    have : 4 * α * w.re < 0 := by linarith
    by_contra hn
    have hn' : 0 ≤ w.re := not_lt.mp hn
    nlinarith
  · intro h1
    have hneg : 0 < -w.re := by linarith
    have : 0 < 4 * α * (-w.re) := by positivity
    linarith

theorem cayley_eq_iff {α : ℝ} (hα : 0 < α) (w : ℂ) :
    ‖(α : ℂ) - w‖ = ‖(α : ℂ) + w‖ ↔ w.re = 0 := by
  have h := sq_norm_dif α w
  constructor
  · intro h1
    rw [h1] at h
    have : 4 * α * w.re = 0 := by linarith
    rcases mul_eq_zero.mp this with h4 | h4
    · nlinarith
    · exact h4
  · intro h1
    rw [h1, mul_zero, sub_eq_zero] at h
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h.symm

theorem bahia_no_depende_de_alfa {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (w : ℂ) :
    ‖(α : ℂ) + w‖ < ‖(α : ℂ) - w‖ ↔ ‖(β : ℂ) + w‖ < ‖(β : ℂ) - w‖ := by
  rw [cayley_gt_iff hα, cayley_gt_iff hβ]

theorem fase_canonica_deriv {f f1 : ℝ → ℝ} {f2 t α : ℝ} (hα : 0 < α)
    (hf : HasDerivAt f (f1 t) t) (hf1 : HasDerivAt f1 f2 t) (h0 : f t ≠ 0) :
    HasDerivAt (fun x => 2 * Real.arctan (f1 x / (α * f x)))
      (-(2 * α * (f1 t ^ 2 - f t * f2)) / (α ^ 2 * f t ^ 2 + f1 t ^ 2)) t := by
  have hαf : α * f t ≠ 0 := mul_ne_zero hα.ne' h0
  have hd : HasDerivAt (fun x => f1 x / (α * f x))
      ((f2 * (α * f t) - f1 t * (α * f1 t)) / (α * f t) ^ 2) t := hf1.div (hf.const_mul α) hαf
  have ha := (hd.arctan).const_mul 2
  convert ha using 1
  have hft : 0 < f t ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h0))
  have hden : α ^ 2 * f t ^ 2 + f1 t ^ 2 ≠ 0 := by positivity
  have hden2 : 1 + (f1 t / (α * f t)) ^ 2 ≠ 0 := by positivity
  field_simp
  ring

theorem fase_gira_un_lado {x y z α : ℝ} (hα : 0 < α) (hx : x ≠ 0) (hL : 0 < y ^ 2 - x * z) :
    -(2 * α * (y ^ 2 - x * z)) / (α ^ 2 * x ^ 2 + y ^ 2) < 0 := by
  have hx2 : 0 < x ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hx))
  have hd : 0 < α ^ 2 * x ^ 2 + y ^ 2 := by positivity
  have hn : 0 < 2 * α * (y ^ 2 - x * z) := by positivity
  exact div_neg_of_neg_of_pos (by linarith) hd

theorem fase_retrocede_iff {x y z α : ℝ} (hα : 0 < α) (hx : x ≠ 0) :
    0 < -(2 * α * (y ^ 2 - x * z)) / (α ^ 2 * x ^ 2 + y ^ 2) ↔ y ^ 2 - x * z < 0 := by
  have hx2 : 0 < x ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hx))
  have hd : 0 < α ^ 2 * x ^ 2 + y ^ 2 := by positivity
  rw [div_pos_iff_of_pos_right hd]
  constructor
  · intro h
    by_contra hn
    have hn' : 0 ≤ y ^ 2 - x * z := not_lt.mp hn
    have : 0 ≤ 2 * α * (y ^ 2 - x * z) := by positivity
    linarith
  · intro h
    have : 0 < 2 * α * (-(y ^ 2 - x * z)) := by
      have : 0 < -(y ^ 2 - x * z) := by linarith
      positivity
    linarith

theorem carga_propia_par {δ : ℝ} (hδ : δ ≠ 0) :
    1 / ((δ : ℂ) * I) ^ 2 + 1 / (-((δ : ℂ) * I)) ^ 2 = -(2 / (δ : ℂ) ^ 2) := by
  have hc : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ
  rw [neg_sq, mul_pow, I_sq]
  field_simp
  ring

theorem par_calor_deriv {δ₀ l : ℝ} (h : 2 * l < δ₀ ^ 2) :
    HasDerivAt (fun x => Real.sqrt (δ₀ ^ 2 - 2 * x)) (-1 / Real.sqrt (δ₀ ^ 2 - 2 * l)) l := by
  have hp : 0 < δ₀ ^ 2 - 2 * l := by linarith
  have hd : HasDerivAt (fun x => δ₀ ^ 2 - 2 * x) (-(2 * 1)) l :=
    ((hasDerivAt_id l).const_mul 2).const_sub (δ₀ ^ 2)
  have hs := hd.sqrt hp.ne'
  convert hs using 1
  have hq : 0 < Real.sqrt (δ₀ ^ 2 - 2 * l) := Real.sqrt_pos.mpr hp
  field_simp

theorem par_calor_puerta (δ₀ : ℝ) : Real.sqrt (δ₀ ^ 2 - 2 * (δ₀ ^ 2 / 2)) = 0 := by
  have : δ₀ ^ 2 - 2 * (δ₀ ^ 2 / 2) = 0 := by ring
  rw [this, Real.sqrt_zero]

theorem par_real_calor_deriv {g₀ l : ℝ} (h : 0 < g₀ ^ 2 + 8 * l) :
    HasDerivAt (fun x => Real.sqrt (g₀ ^ 2 + 8 * x)) (4 / Real.sqrt (g₀ ^ 2 + 8 * l)) l := by
  have hd : HasDerivAt (fun x => g₀ ^ 2 + 8 * x) (8 * 1) l :=
    ((hasDerivAt_id l).const_mul 8).const_add (g₀ ^ 2)
  have hs := hd.sqrt h.ne'
  convert hs using 1
  have hq : 0 < Real.sqrt (g₀ ^ 2 + 8 * l) := Real.sqrt_pos.mpr h
  field_simp
  ring

theorem par_real_calor_choque (g₀ : ℝ) : Real.sqrt (g₀ ^ 2 + 8 * (-(g₀ ^ 2 / 8))) = 0 := by
  have : g₀ ^ 2 + 8 * (-(g₀ ^ 2 / 8)) = 0 := by ring
  rw [this, Real.sqrt_zero]

theorem puerta_por_carga {δ : ℝ} (hδ : δ ≠ 0) : (δ ^ 2 / 2) * (-(2 / δ ^ 2)) = -1 := by
  field_simp

theorem apagon_no_cruza_borde {α : ℝ} (hα : 0 < α) {w : ℂ} (h : w.re = 0) : w ≠ -(α : ℂ) := by
  intro hw
  rw [hw] at h
  simp at h
  linarith

end RhG1Lean
