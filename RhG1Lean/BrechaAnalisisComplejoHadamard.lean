import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import RhG1Lean.RigidezGlobalEuler

/-!
# Formalización del Análisis Complejo Clásico de la Brecha Hadamard-Euler

Este módulo formaliza la inversión de signo del término de Hadamard para ceros
desplazados fuera de la recta crítica frente a la positividad estricta en la recta:

1. `hadamard_polo_linea_critica_positivo`:
   En la recta crítica (b = 0), para todo x > 0, el término transversal
   de Hadamard 2 / x es estrictamente positivo: 0 < 2 / x.

2. `hadamard_polo_desplazado_negativo`:
   Para cualquier cero desplazado a b > 0, en todo el intervalo interior 0 < x < b,
   el término transversal 2 * x / (x^2 - b^2) es estrictamente negativo:
   2 * x / (x^2 - b^2) < 0.

3. `inversion_signo_deficit_transversal`:
   Para todo 0 < x < b, el término desplazado 2 * x / (x^2 - b^2) es estrictamente
   menor que el término confinado en la recta 2 / x: 2 * x / (x^2 - b^2) < 2 / x.

4. `cero_desplazado_denominador_negativo`:
   Para 0 ≤ x y x < b con 0 < b, la diferencia cuadrática x^2 - b^2 es estrictamente negativa.
-/

namespace RhG1Lean

open Real

/--
Teorema 1: Positividad del Término de Hadamard en la Recta Crítica (b = 0).
Para todo x > 0, 2 / x > 0.
-/
theorem hadamard_polo_linea_critica_positivo (x : ℝ) (hx : 0 < x) :
    0 < 2 / x := by
  have h2 : (0 : ℝ) < 2 := by linarith
  exact div_pos h2 hx

/--
Teorema 2: Negatividad del Denominador Cuadrático para x < b.
Para 0 ≤ x y x < b con 0 < b, x^2 - b^2 < 0.
-/
theorem cero_desplazado_denominador_negativo (x b : ℝ) (hx : 0 ≤ x) (h_lt : x < b) :
    x ^ 2 - b ^ 2 < 0 := by
  have h_sq : x ^ 2 < b ^ 2 := by
    nlinarith
  linarith

/--
Teorema 3: Negatividad Estricta del Término Local de Hadamard para x < b.
Para 0 < x y x < b, 2 * x / (x^2 - b^2) < 0.
-/
theorem hadamard_polo_desplazado_negativo (x b : ℝ) (hx : 0 < x) (h_lt : x < b) :
    (2 * x) / (x ^ 2 - b ^ 2) < 0 := by
  have h_num : 0 < 2 * x := by linarith
  have h_den : x ^ 2 - b ^ 2 < 0 := cero_desplazado_denominador_negativo x b (le_of_lt hx) h_lt
  exact div_neg_of_pos_of_neg h_num h_den

/--
Teorema 4: Déficit Estricto de Hadamard: El Término Desplazado es Estrictamente Menor que el Término en la Recta.
Para todo 0 < x y x < b, (2 * x) / (x^2 - b^2) < 2 / x.
-/
theorem inversion_signo_deficit_transversal (x b : ℝ) (hx : 0 < x) (h_lt : x < b) :
    (2 * x) / (x ^ 2 - b ^ 2) < 2 / x := by
  have h_neg : (2 * x) / (x ^ 2 - b ^ 2) < 0 := hadamard_polo_desplazado_negativo x b hx h_lt
  have h_pos : 0 < 2 / x := hadamard_polo_linea_critica_positivo x hx
  linarith

end RhG1Lean
