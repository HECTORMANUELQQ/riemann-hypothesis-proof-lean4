import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# La maquinita del pentágono: π contiene a φ (idea de Hector)

* `phi_eq_two_cos_pi_div_five`: φ = 2·cos(π/5).
* `maquinita_phi`: e^{iπ/5} + e^{−iπ/5} = φ. Un giro de 36° más su reflejo produce el número de oro.
* `giro_acotado`: el giro nunca crece, ‖e^{iπn/5}‖ = 1.
* `phi_crece`: φ² = φ + 1, la regla de crecimiento de Fibonacci.

Es la misma operación que da Z = rosa + reflejo en la costura: un giro y su espejo dan un número real.
-/

open Real Complex
open scoped goldenRatio

namespace RhG1Lean

theorem phi_eq_two_cos_pi_div_five : goldenRatio = 2 * Real.cos (π / 5) := by
  rw [Real.cos_pi_div_five]
  ring

theorem maquinita_phi :
    Complex.exp (↑(π / 5) * I) + Complex.exp (-(↑(π / 5) * I)) = ((goldenRatio : ℝ) : ℂ) := by
  rw [phi_eq_two_cos_pi_div_five]
  push_cast
  rw [Complex.two_cos, neg_mul]

theorem giro_acotado (n : ℕ) : ‖Complex.exp (↑(π / 5 * n) * I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem phi_crece : goldenRatio ^ 2 = goldenRatio + 1 :=
  goldenRatio_sq

end RhG1Lean
