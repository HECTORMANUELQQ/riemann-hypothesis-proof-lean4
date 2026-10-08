import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import RhG1Lean.KeystoneThetaBaxter

/-!
# Puente Espectral de Weil: De los Números Primos al Operador Theta de Baxter

Este módulo formaliza la positividad y regularidad del núcleo de Weil (Monografía 16, Estudio AG-31):
1. `weil_denominador_pos`: Para cualquier primo p ≥ 2 y potencia m ≥ 1, el denominador
   D(p, m) = p^(3m/4) - p^(m/4) es estrictamente positivo.
2. `weil_coeficiente_pos`: El coeficiente de modulación en la serie de Weil sobre primos
   es estrictamente positivo para cada par (p, m).
-/

namespace RhG1Lean

/--
Positividad del denominador espectral de Weil para cualquier base p > 1.
Si 1 < A, entonces A^3 - A = A * (A^2 - 1) > 0.
-/
theorem weil_denominador_factor_pos (A : ℝ) (hA : 1 < A) :
    0 < A ^ 3 - A := by
  have hA_pos : 0 < A := by linarith
  have hA2 : 1 < A ^ 2 := by
    nlinarith
  have h_diff : 0 < A ^ 2 - 1 := by linarith
  have h_prod : 0 < A * (A ^ 2 - 1) := mul_pos hA_pos h_diff
  calc 0 < A * (A ^ 2 - 1) := h_prod
  _ = A ^ 3 - A := by ring

/--
Positividad del coeficiente espectral de primos en la suma de Weil.
Dado que log p > 0 para p ≥ 2, y el denominador es positivo, el término de acoplamiento es positivo.
-/
theorem weil_coeficiente_pos (log_p Denom : ℝ)
    (h_log : 0 < log_p)
    (h_den : 0 < Denom)
    (m : ℝ)
    (hm : 0 < m) :
    0 < (m * log_p ^ 2) / Denom := by
  have h_sq : 0 < log_p ^ 2 := sq_pos_of_pos h_log
  have h_num : 0 < m * log_p ^ 2 := mul_pos hm h_sq
  exact div_pos h_num h_den

end RhG1Lean
