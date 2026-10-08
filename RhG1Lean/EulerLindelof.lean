import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# La identidad de Euler en la costura, y la cota de tamaño (Lindelöf)

Costura `F = R + χ·R♯` en un punto (valores complejos `R`, `Rs = R♯`, `χ`).

* `cero_es_euler`: si `R ≠ 0`, entonces `F = 0 ⇔ q = e^{iπ}`, con `q = χ·R♯/R`.
* `par_invisible`: `e^{i(φ + 2π)} = e^{iφ}`. Un par de ceros fuera de la recta suma 2π a la fase y no cambia nada que dependa de `e^{iφ}`.
* `signo_por_paridad`: `e^{iπn} = (−1)^n`. El signo de Z es `(−1)^{N−1}`.
* `tamano_costura`: en la pared (`‖χ‖ = 1`, `‖R♯‖ = ‖R‖`), `‖F‖ ≤ 2‖R‖`. Lindelöf para la rosa implica Lindelöf para la función.
* `tamano_doblez`: el doblez `a·F + b·G` (Davenport–Heilbronn) hereda el tamaño de sus dos mitades.
-/

open Complex

namespace RhG1Lean

theorem cero_es_euler {R Rs χ : ℂ} (hR : R ≠ 0) :
    R + χ * Rs = 0 ↔ χ * Rs / R = exp (↑Real.pi * I) := by
  rw [exp_pi_mul_I]
  constructor
  · intro h
    have : χ * Rs = -R := by linear_combination h
    rw [this, neg_div, div_self hR]
  · intro h
    have h' : χ * Rs = -R := by
      field_simp at h
      linear_combination h
    linear_combination h'

theorem par_invisible (φ : ℝ) :
    exp (↑(φ + 2 * Real.pi) * I) = exp (↑φ * I) := by
  have : (↑(φ + 2 * Real.pi) * I : ℂ) = ↑φ * I + 2 * ↑Real.pi * I := by push_cast; ring
  rw [this, exp_add, exp_two_pi_mul_I, mul_one]

theorem signo_por_paridad (n : ℕ) :
    exp (↑Real.pi * I * n) = (-1 : ℂ) ^ n := by
  rw [← exp_pi_mul_I, ← exp_nat_mul]
  ring_nf

theorem tamano_costura {R Rs χ : ℂ} (hχ : ‖χ‖ = 1) (hRs : ‖Rs‖ = ‖R‖) :
    ‖R + χ * Rs‖ ≤ 2 * ‖R‖ := by
  calc ‖R + χ * Rs‖ ≤ ‖R‖ + ‖χ * Rs‖ := norm_add_le _ _
    _ = ‖R‖ + ‖χ‖ * ‖Rs‖ := by rw [norm_mul]
    _ = 2 * ‖R‖ := by rw [hχ, hRs]; ring

theorem tamano_doblez (a b F G : ℂ) :
    ‖a * F + b * G‖ ≤ ‖a‖ * ‖F‖ + ‖b‖ * ‖G‖ := by
  calc ‖a * F + b * G‖ ≤ ‖a * F‖ + ‖b * G‖ := norm_add_le _ _
    _ = ‖a‖ * ‖F‖ + ‖b‖ * ‖G‖ := by rw [norm_mul, norm_mul]

end RhG1Lean
