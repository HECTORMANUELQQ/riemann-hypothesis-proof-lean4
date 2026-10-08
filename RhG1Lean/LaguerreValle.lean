import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Tercera forma: la desigualdad de Laguerre (colina o valle entre ceros)

Para una función f, 𝓛 = f′² − f·f″. Si todos sus ceros son reales, 𝓛 ≥ 0 (log|f| es cóncavo: "colina").
Un par de ceros fuera de la recta produce 𝓛 < 0 cerca de él ("valle"). Es la "joroba que no llega a cero".

* `laguerre_dos_reales`: f = (x − a)(x − b) ⇒ f′² − f·f″ = (x − a)² + (x − b)² ≥ 0.
* `laguerre_par_fuera`: f = (x − γ)² + δ² (ceros γ ± iδ) ⇒ f′² − f·f″ = 2((x − γ)² − δ²), negativo si |x − γ| < |δ|.
* `aporte_cero_real`: cada cero real aporta −1/(x − γ)² < 0 a (log|f|)″ (colina).
* `aporte_par_fuera_valle`: un par γ ± iδ aporta −2((x − γ)² − δ²)/((x − γ)² + δ²)², positivo si (x − γ)² < δ² (valle).
-/

namespace RhG1Lean

theorem laguerre_dos_reales (a b x : ℝ) :
    ((x - a) + (x - b)) ^ 2 - ((x - a) * (x - b)) * 2 = (x - a) ^ 2 + (x - b) ^ 2 := by ring

theorem laguerre_dos_reales_nonneg (a b x : ℝ) :
    0 ≤ ((x - a) + (x - b)) ^ 2 - ((x - a) * (x - b)) * 2 := by
  rw [laguerre_dos_reales]; positivity

theorem laguerre_par_fuera (γ δ x : ℝ) :
    (2 * (x - γ)) ^ 2 - ((x - γ) ^ 2 + δ ^ 2) * 2 = 2 * ((x - γ) ^ 2 - δ ^ 2) := by ring

theorem laguerre_par_fuera_neg {γ δ x : ℝ} (h : (x - γ) ^ 2 < δ ^ 2) :
    (2 * (x - γ)) ^ 2 - ((x - γ) ^ 2 + δ ^ 2) * 2 < 0 := by
  rw [laguerre_par_fuera]; linarith

theorem aporte_cero_real {γ x : ℝ} (h : x ≠ γ) : -(1 / (x - γ) ^ 2) < 0 := by
  have : (x - γ) ≠ 0 := sub_ne_zero.mpr h
  have : 0 < (x - γ) ^ 2 := by positivity
  have : 0 < 1 / (x - γ) ^ 2 := by positivity
  linarith

theorem aporte_par_fuera_valle {γ δ x : ℝ} (hδ : δ ≠ 0) (h : (x - γ) ^ 2 < δ ^ 2) :
    0 < -2 * ((x - γ) ^ 2 - δ ^ 2) / ((x - γ) ^ 2 + δ ^ 2) ^ 2 := by
  have hd : 0 < δ ^ 2 := by positivity
  have hden : 0 < ((x - γ) ^ 2 + δ ^ 2) ^ 2 := by positivity
  apply div_pos _ hden
  linarith

end RhG1Lean
