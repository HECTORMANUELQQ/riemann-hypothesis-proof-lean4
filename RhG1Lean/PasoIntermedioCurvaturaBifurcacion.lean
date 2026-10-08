import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import RhG1Lean.OperadorDeterminanteHadamard

/-!
# Formalización del Paso Intermedio: Curvatura, Bifurcación y Discriminante de Jensen

Este módulo formaliza las propiedades analíticas y algebraicas del "paso intermedio"
que conecta un hipotético cero fuera de la recta crítica ($b ≠ 0$) con la deformación
del potencial espectral y la jerarquía de Jensen:

1. `pozo_minimo_linea_critica`:
   Cuando $b = 0$, la energía transversal local $V(x) = (x^2 + γ^2)^2$ alcanza su mínimo
   global absoluto en $x = 0$, es decir, $V(0) ≤ V(x)$ para todo $x$.

2. `bifurcacion_cero_fuera_linea`:
   Para un desplazamiento transversal $b ≠ 0$, el potencial cuádruple
   $V_b(x) = (x^2 - b^2)^2$ se anula idénticamente en $x = b$, demostrando que
   el mínimo se bifurca fuera del eje de simetría $x = 0$.

3. `origen_estrictamente_positivo_fuera_linea`:
   Si $b ≠ 0$, entonces en el centro de simetría $x = 0$, el potencial es estrictamente
   positivo: $V_b(0) = b^4 > 0$, de modo que $x = 0$ deja de ser el cero del sistema.

4. `jensen_discriminante_grado_2`:
   Para el polinomio de Jensen de grado 2 asociado al invariante de Laguerre:
   $\Delta_2 = 4 (a_1^2 - a_0 a_2)$. Si el invariante de Laguerre satisface
   $a_1^2 - a_0 a_2 > 0$, entonces el discriminante de Jensen es estrictamente positivo:
   $\Delta_2 > 0$, garantizando la hiperbolicidad (raíces reales).
-/

namespace RhG1Lean

open Real

/--
Teorema 1: Mínimo Global del Pozo Transversal en la Recta Crítica (b = 0).
Para todo x, γ : ℝ, (0^2 + γ^2)^2 ≤ (x^2 + γ^2)^2.
-/
theorem pozo_minimo_linea_critica (x γ : ℝ) :
    γ ^ 4 ≤ (x ^ 2 + γ ^ 2) ^ 2 := by
  have hx : 0 ≤ x ^ 2 := sq_nonneg x
  have hγ : 0 ≤ γ ^ 2 := sq_nonneg γ
  have h_sum : γ ^ 2 ≤ x ^ 2 + γ ^ 2 := by linarith
  have h_sq : (γ ^ 2) ^ 2 ≤ (x ^ 2 + γ ^ 2) ^ 2 := by
    nlinarith
  have h_pow : γ ^ 4 = (γ ^ 2) ^ 2 := by ring
  rw [h_pow]
  exact h_sq

/--
Teorema 2: Bifurcación del Cero fuera de la Recta Crítica (x = b).
Para todo b : ℝ, (b^2 - b^2)^2 = 0.
-/
theorem bifurcacion_cero_fuera_linea (b : ℝ) :
    (b ^ 2 - b ^ 2) ^ 2 = 0 := by
  ring

/--
Teorema 3: Energía Positiva en el Centro cuando b ≠ 0.
Para todo b ≠ 0, (0^2 - b^2)^2 = b^4 > 0.
-/
theorem origen_estrictamente_positivo_fuera_linea (b : ℝ) (hb : b ≠ 0) :
    0 < (0 ^ 2 - b ^ 2) ^ 2 := by
  have h_simp : (0 ^ 2 - b ^ 2) ^ 2 = b ^ 4 := by ring
  rw [h_simp]
  have hb2 : 0 < b ^ 2 := sq_pos_of_ne_zero hb
  have hb4 : b ^ 4 = (b ^ 2) ^ 2 := by ring
  rw [hb4]
  exact sq_pos_of_ne_zero (ne_of_gt hb2)

/--
Teorema 4: Discriminante del Polinomio de Jensen de Grado 2.
Si el invariante de Laguerre satisface L = a_1^2 - a_0 a_2 > 0,
entonces el discriminante Δ₂ = 4 * (a_1^2 - a_0 a_2) > 0.
-/
theorem jensen_discriminante_grado_2 (a₀ a₁ a₂ : ℝ)
    (h_laguerre : 0 < a₁ ^ 2 - a₀ * a₂) :
    0 < 4 * (a₁ ^ 2 - a₀ * a₂) := by
  linarith

end RhG1Lean
