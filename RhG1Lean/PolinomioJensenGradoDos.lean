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
# Fase 3: Polinomios de Jensen de Grado 2 y Discriminante de Laguerre
## Conexión entre la Hiperbolicidad Cuadrática y el Invariante de Laguerre

Este módulo formaliza la Fase 3 del Gran Plan Maestro:
1. **Definición del Polinomio de Jensen de Grado 2:**
   $J_2(X; a_0, a_1, a_2) \coloneqq a_0 X^2 + 2 a_1 X + a_2$,
   asociado a la terna $(a_0, a_1, a_2) = (\Xi(t), \Xi'(t), \Xi''(t))$.
2. **Discriminante Exacto:**
   $\Delta(J_2) = (2 a_1)^2 - 4 a_0 a_2 = 4 (a_1^2 - a_0 a_2) = 4 \mathcal{L}(a_0, a_1, a_2)$.
3. **Equivalencia de Hiperbolicidad:**
   $\Delta(J_2) \ge 0 \iff \mathcal{L}(a_0, a_1, a_2) \ge 0$.
4. **Teorema de Confinamiento por Hiperbolicidad:**
   Si el polinomio de Jensen es hiperbólico ($\Delta \ge 0$), entonces $\mathcal{L} \ge 0$,
   lo que imposibilita la existencia de cualquier raíz fuera de la recta crítica con
   defecto singular $-4/\delta^2 + K < 0$.
-/

set_option linter.unusedVariables false
set_option linter.style.header false

namespace RhG1Lean

open Real

/-! ### SECCIÓN 1: Polinomio de Jensen y su Discriminante -/

/-- Polinomio de Jensen de grado 2 asociado a coeficientes (a0, a1, a2):
    J_2(X) = a0 * X² + 2 * a1 * X + a2. -/
def jensen_poly_grado_2 (a0 a1 a2 X : ℝ) : ℝ :=
  a0 * X ^ 2 + 2 * a1 * X + a2

/-- Discriminante algebraico del polinomio cuadrático de Jensen:
    Δ = (2 * a1)² - 4 * a0 * a2. -/
def discriminante_jensen_2 (a0 a1 a2 : ℝ) : ℝ :=
  (2 * a1) ^ 2 - 4 * a0 * a2

/-- Invariante diferencial de Laguerre L = a1² - a0 * a2. -/
def laguerre_coefs (a0 a1 a2 : ℝ) : ℝ :=
  a1 ^ 2 - a0 * a2

/-- Identidad Fundamental: El discriminante de Jensen es exactamente 4 veces
    el invariante de Laguerre: Δ(J_2) = 4 * L. -/
theorem discriminante_jensen_eq_cuatro_laguerre (a0 a1 a2 : ℝ) :
    discriminante_jensen_2 a0 a1 a2 = 4 * laguerre_coefs a0 a1 a2 := by
  dsimp [discriminante_jensen_2, laguerre_coefs]
  ring

/-- Equivalencia de No-Negatividad: Δ(J_2) ≥ 0 si y solo si L ≥ 0. -/
theorem discriminante_nonneg_iff_laguerre_nonneg (a0 a1 a2 : ℝ) :
    0 ≤ discriminante_jensen_2 a0 a1 a2 ↔ 0 ≤ laguerre_coefs a0 a1 a2 := by
  rw [discriminante_jensen_eq_cuatro_laguerre]
  constructor
  · intro h
    nlinarith [h]
  · intro h
    nlinarith [h]

/-! ### SECCIÓN 2: Teorema de Cierre por Hiperbolicidad de Jensen -/

/-- Teorema de Cierre por Hiperbolicidad de Jensen:
    Si el polinomio de Jensen de grado 2 tiene discriminante no-negativo (0 ≤ Δ(J_2)),
    y el potencial transversal se acopla vía la relación armónica 2 * L / a0² = -4 / δ² + K,
    entonces es imposible que exista un defecto singular neto negativo (-4 / δ² + K < 0). -/
theorem teorema_cierre_hiperbolicidad_jensen (δ K a0 a1 a2 : ℝ)
    (ha0_pos : 0 < a0 ^ 2)
    (h_jensen_hip : 0 ≤ discriminante_jensen_2 a0 a1 a2)
    (h_acoplamiento : 2 * laguerre_coefs a0 a1 a2 / (a0 ^ 2) = -4 / (δ ^ 2) + K)
    (h_defecto_neg : -4 / (δ ^ 2) + K < 0) :
    False := by
  rw [discriminante_nonneg_iff_laguerre_nonneg] at h_jensen_hip
  have h_two_L : 2 * laguerre_coefs a0 a1 a2 < 0 := by
    have h_prod : (2 * laguerre_coefs a0 a1 a2 / (a0 ^ 2)) * (a0 ^ 2) < 0 * (a0 ^ 2) := by
      nlinarith [h_defecto_neg, ha0_pos, h_acoplamiento]
    have h_div : (2 * laguerre_coefs a0 a1 a2 / (a0 ^ 2)) * (a0 ^ 2) = 2 * laguerre_coefs a0 a1 a2 := by
      exact div_mul_cancel₀ (2 * laguerre_coefs a0 a1 a2) (ne_of_gt ha0_pos)
    rw [h_div] at h_prod
    linarith [h_prod]
  have h_L_neg : laguerre_coefs a0 a1 a2 < 0 := by linarith [h_two_L]
  linarith [h_jensen_hip, h_L_neg]

/-- Corolario de Extinción de Desviación Fuera de la Recta Crítica:
    Si para un cero con desviación 0 < δ < 1/2 y rigidez K < 16, el discriminante
    de Jensen satisface 0 ≤ Δ(J_2), entonces se produce una contradicción lógica estricta. -/
theorem extincion_cero_por_hiperbolicidad_jensen (δ K a0 a1 a2 : ℝ)
    (ha0_pos : 0 < a0 ^ 2)
    (hδ_pos : 0 < δ)
    (hδ_band : δ < 1 / 2)
    (hK : K < 16)
    (h_jensen_hip : 0 ≤ discriminante_jensen_2 a0 a1 a2)
    (h_acoplamiento : 2 * laguerre_coefs a0 a1 a2 / (a0 ^ 2) = -4 / (δ ^ 2) + K) :
    False := by
  have hδ2_pos : 0 < δ ^ 2 := sq_pos_of_pos hδ_pos
  have h_sq_bound : δ ^ 2 < (1 / 2 : ℝ) ^ 2 := by
    nlinarith [hδ_pos, hδ_band]
  have h_sq_val : (1 / 2 : ℝ) ^ 2 = 1 / 4 := by norm_num
  rw [h_sq_val] at h_sq_bound
  have h_inv : 1 / (1 / 4 : ℝ) < 1 / (δ ^ 2) := by
    apply one_div_lt_one_div_of_lt hδ2_pos h_sq_bound
  have h_inv_val : 1 / (1 / 4 : ℝ) = 4 := by norm_num
  rw [h_inv_val] at h_inv
  have h_four : 16 < 4 / (δ ^ 2) := by
    calc
      16 = 4 * 4 := by norm_num
      _ < 4 * (1 / (δ ^ 2)) := by nlinarith [h_inv]
      _ = 4 / (δ ^ 2) := by ring
  have h_sing : -4 / (δ ^ 2) < -16 := by
    have h_eq : -4 / (δ ^ 2) = - (4 / (δ ^ 2)) := by ring
    rw [h_eq]
    linarith [h_four]
  have h_colapso : -4 / (δ ^ 2) + K < 0 := by
    linarith [h_sing, hK]
  exact teorema_cierre_hiperbolicidad_jensen δ K a0 a1 a2 ha0_pos h_jensen_hip h_acoplamiento h_colapso

end RhG1Lean
