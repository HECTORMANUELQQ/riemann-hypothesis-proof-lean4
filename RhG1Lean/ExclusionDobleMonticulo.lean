/-
Copyright (c) 2026 Antigravity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity Contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Fase 4: Exclusión del Doble Montículo y Concavidad en Extremos
## Análisis Estructural del Invariante de Laguerre en Puntos Críticos y Ceros

Este módulo formaliza la Fase 4 del Gran Plan Maestro:
1. **Positividad en Ceros de la Función:**
   Si $f = 0$, entonces $\mathcal{L}(f, f', f'') = (f')^2 \ge 0$.
2. **Positividad en Puntos de Inflexión:**
   Si $f'' = 0$, entonces $\mathcal{L}(f, f', f'') = (f')^2 \ge 0$.
3. **Comportamiento en Puntos Estacionarios ($f' = 0$):**
   - Para un máximo positivo ($f > 0$, $f'' \le 0$): $\mathcal{L} = -f \cdot f'' \ge 0$.
   - Para un mínimo negativo ($f < 0$, $0 \le f''$): $\mathcal{L} = -f \cdot f'' \ge 0$.
4. **Condición Necesaria para Violación de Laguerre:**
   $\mathcal{L} < 0$ en un punto estacionario requiere $f \cdot f'' > 0$ (un doble montículo / valle interno positivo o cresta interna negativa).
5. **Teorema de Confinamiento Unimodal:**
   Una función que no posee dobles montículos satisface $\mathcal{L} \ge 0$ en todos sus extremos locales.
-/

set_option linter.unusedVariables false
set_option linter.style.header false

namespace RhG1Lean

open Real

/-- Invariante diferencial de Laguerre L = (f')² - f * f''. -/
def laguerre_eval (f fp fpp : ℝ) : ℝ :=
  fp ^ 2 - f * fpp

/-! ### SECCIÓN 1: Positividad en Ceros e Inflexiones -/

/-- En cualquier cero (f = 0), el invariante de Laguerre es no-negativo (L = (f')² ≥ 0). -/
theorem laguerre_en_cero_no_negativo (fp fpp : ℝ) :
    0 ≤ laguerre_eval 0 fp fpp := by
  dsimp [laguerre_eval]
  have h_zero : (0 : ℝ) * fpp = 0 := by ring
  rw [h_zero, sub_zero]
  exact sq_nonneg fp

/-- En cualquier punto de inflexión (f'' = 0), el invariante de Laguerre es no-negativo (L = (f')² ≥ 0). -/
theorem laguerre_en_inflexion_no_negativo (f fp : ℝ) :
    0 ≤ laguerre_eval f fp 0 := by
  dsimp [laguerre_eval]
  have h_zero : f * (0 : ℝ) = 0 := by ring
  rw [h_zero, sub_zero]
  exact sq_nonneg fp

/-! ### SECCIÓN 2: Positividad en Extremos Canónicos (Ausencia de Doble Montículo) -/

/-- En un máximo local de cresta positiva (f > 0, fp = 0, fpp ≤ 0), L ≥ 0. -/
theorem laguerre_en_maximo_positivo (f fpp : ℝ)
    (hf_pos : 0 < f) (hfpp_neg : fpp ≤ 0) :
    0 ≤ laguerre_eval f 0 fpp := by
  dsimp [laguerre_eval]
  have h_fp0 : (0 : ℝ) ^ 2 = 0 := by ring
  rw [h_fp0, zero_sub]
  have h_prod : f * fpp ≤ 0 := by
    nlinarith [hf_pos, hfpp_neg]
  linarith [h_prod]

/-- En un mínimo local de cresta negativa (f < 0, fp = 0, 0 ≤ fpp), L ≥ 0. -/
theorem laguerre_en_minimo_negativo (f fpp : ℝ)
    (hf_neg : f < 0) (hfpp_pos : 0 ≤ fpp) :
    0 ≤ laguerre_eval f 0 fpp := by
  dsimp [laguerre_eval]
  have h_fp0 : (0 : ℝ) ^ 2 = 0 := by ring
  rw [h_fp0, zero_sub]
  have h_prod : f * fpp ≤ 0 := by
    nlinarith [hf_neg, hfpp_pos]
  linarith [h_prod]

/-- Teorema de Cierre Unimodal: Si un punto crítico fp = 0 corresponde a un extremo canónico
    (ya sea máximo de cresta positiva o mínimo de cresta negativa), entonces L ≥ 0. -/
theorem laguerre_no_negativo_en_extremos_canonicos (f fpp : ℝ)
    (h_canonico : (0 < f ∧ fpp ≤ 0) ∨ (f < 0 ∧ 0 ≤ fpp)) :
    0 ≤ laguerre_eval f 0 fpp := by
  rcases h_canonico with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact laguerre_en_maximo_positivo f fpp h1 h2
  · exact laguerre_en_minimo_negativo f fpp h1 h2

/-- Caracterización Estricta del Defecto: Si en un punto estacionario fp = 0 se tuviera L < 0,
    entonces obligatoriamente f * f'' > 0 (la función debe tener concavidad hacia afuera:
    mínimo local positivo o máximo local negativo, un doble montículo no unimodal). -/
theorem violacion_laguerre_fuerza_doble_monticulo (f fpp : ℝ)
    (h_violacion : laguerre_eval f 0 fpp < 0) :
    0 < f * fpp := by
  dsimp [laguerre_eval] at h_violacion
  have h_fp0 : (0 : ℝ) ^ 2 = 0 := by ring
  rw [h_fp0, zero_sub] at h_violacion
  linarith [h_violacion]

end RhG1Lean
