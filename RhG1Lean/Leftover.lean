/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under CC-BY 4.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Data.Fin.VecNotation
import RhG1Lean.G5Interior
import RhG1Lean.MouthA

/-!
# Disco chico de O₁, anclado a G5Interior + rosas/Pick

Ya demostrado: sector y ‖w‖ > √2/2 ⇒ Re s > 1 ⇒ ξ ≠ 0.

Caja dura: |Im w| ≤ Re w ≤ 1/2 ⇒ |t| ≤ 1/2.

HTML / Pick-3: γ₁ ≈ 14.1347. Aquí solo usamos 14 ≤ |t| como cota de esa
muestra (no como teorema de “el primer cero”). Coherente con G1–G5:
esa altura no cabe en leftoverHard; si δ ≠ 0, MouthA la manda a Re u < 0.
-/

open Complex Real

namespace RhG1Lean

def leftoverHard (w : ℂ) : Prop := |w.im| ≤ w.re ∧ w.re ≤ 1 / 2

theorem leftoverHard_im_le_half {w : ℂ} (h : leftoverHard w) : |w.im| ≤ 1 / 2 :=
  le_trans h.1 h.2

/-- Cota inferior de γ₁ según rosas/HTML y Pick-3 (muestra, no Lean-cero). -/
def roseGamma1Lower : ℝ := 14

theorem roseGamma1Lower_gt_half : (1 : ℝ) / 2 < roseGamma1Lower := by
  unfold roseGamma1Lower
  norm_num

theorem rose_height_not_leftoverHard {δ t : ℝ} (ht : roseGamma1Lower ≤ |t|) :
    ¬ leftoverHard ((δ : ℂ) + I * t) := by
  intro h
  have him : |((δ : ℂ) + I * t).im| ≤ 1 / 2 := leftoverHard_im_le_half h
  have ht' : |t| ≤ 1 / 2 := by simpa using him
  have : roseGamma1Lower ≤ 1 / 2 := le_trans ht ht'
  unfold roseGamma1Lower at this
  norm_num at this

theorem large_im_not_in_small_disk {δ t : ℝ} (ht : Real.sqrt 2 / 2 < |t|) :
    ¬ ‖(δ : ℂ) + I * t‖ ≤ Real.sqrt 2 / 2 := by
  intro h
  have himle : |((δ : ℂ) + I * t).im| ≤ ‖(δ : ℂ) + I * t‖ := abs_im_le_norm _
  have : |t| ≤ ‖(δ : ℂ) + I * t‖ := by simpa using himle
  linarith

theorem rose_height_not_zero_t {t : ℝ} (ht : roseGamma1Lower ≤ |t|) : t ≠ 0 := by
  intro h
  have : roseGamma1Lower ≤ 0 := by simpa [h] using ht
  unfold roseGamma1Lower at this
  norm_num at this

/-- Altura tipo muestra (γ≥14) y δ ≠ 0: está en A, no en leftoverHard. -/
theorem rose_height_in_A_if_off_line {δ t : ℝ} (hδ : δ ≠ 0)
    (ht : roseGamma1Lower ≤ |t|) :
    (((δ : ℂ) + I * t) ^ 2).im ≠ 0 ∧ ¬ leftoverHard ((δ : ℂ) + I * t) :=
  ⟨bocaA_im_ne_zero hδ (rose_height_not_zero_t ht), rose_height_not_leftoverHard ht⟩

/-- Si |t| > |δ| (MouthA) y |t| ≥ 14, Re u < 0: G1 no lo ve. -/
theorem rose_off_line_not_in_O1 {δ t : ℝ} (h : |δ| < |t|) :
    (((δ : ℂ) + I * t) ^ 2).re < 0 :=
  bocaA_re_neg h

/-- O₁ en la franja: |t| < |δ| ≤ 1/2 (los dos lados de σ=1/2).
    leftoverHard era solo el sector derecho Re w ≥ |Im w|. -/
def stripO1Small (δ t : ℝ) : Prop := |t| < |δ| ∧ |δ| ≤ 1 / 2

theorem stripO1Small_of_O1_in_strip {δ t : ℝ} (hδ : |δ| ≤ 1 / 2)
    (hO : 0 < (((δ : ℂ) + I * t) ^ 2).re) : stripO1Small δ t := by
  refine ⟨?_, hδ⟩
  have hpos : 0 < δ * δ - t * t := by
    simpa [re_w_sq] using hO
  have ht2 : t ^ 2 < δ ^ 2 := by nlinarith
  exact sq_lt_sq.mp ht2

theorem stripO1Small_t_lt_half {δ t : ℝ} (h : stripO1Small δ t) : |t| < 1 / 2 :=
  lt_of_lt_of_le h.1 h.2

/-- La muestra γ≥14 no está en O₁-franja chica. Coherente con leftoverHard. -/
theorem rose_height_not_stripO1Small {δ t : ℝ} (ht : roseGamma1Lower ≤ |t|) :
    ¬ stripO1Small δ t := by
  intro h
  have : |t| < 1 / 2 := stripO1Small_t_lt_half h
  have : roseGamma1Lower < 1 / 2 := lt_of_le_of_lt ht this
  unfold roseGamma1Lower at this
  norm_num at this

/-- Diez cotas inferiores de la tabla Pick-3 (ceros 1…10). Finito.
    Los 50 métodos se calcularon *en* estas alturas, no en |t|<1/2;
    aquí solo hacen falta las γ. -/
def monographGammaLower : Fin 10 → ℝ :=
  ![14, 21, 25, 30, 32, 37, 40, 43, 48, 49]

theorem monographGammaLower_ge_rose (i : Fin 10) :
    roseGamma1Lower ≤ monographGammaLower i := by
  fin_cases i <;> simp [monographGammaLower, roseGamma1Lower] <;> norm_num

/-- Ninguna de las 10 alturas de la monografía cae en stripO1Small. -/
theorem monograph_sample_not_stripO1Small (i : Fin 10) {δ t : ℝ}
    (ht : monographGammaLower i ≤ |t|) : ¬ stripO1Small δ t :=
  rose_height_not_stripO1Small (le_trans (monographGammaLower_ge_rose i) ht)

end RhG1Lean
