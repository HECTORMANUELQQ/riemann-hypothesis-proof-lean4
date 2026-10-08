import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import RhG1Lean.WignerPares

/-!
# Teorema de Baxter-Bethe y Confinamiento Espectral de Dorey-Dunning-Tateo

Este módulo formaliza la deducción lógica exacta del Mecanismo DDT (Documento 18, Estudio AG-22):
1. `bethe_condicion_de_tq`: Si T(s) * Q(s) = c * Q(s + h) + d * Q(s - h), y T(s) = 0 con |c| = |d| > 0,
   entonces |Q(s + h)| = |Q(s - h)|.
2. `baxter_bethe_realidad`: Si una función tiene representación de Hadamard finita con todos sus ceros
   en la recta crítica Re(s) = 1/2, y satisface la condición de Bethe |Q(s+h)| = |Q(s-h)| para h > 0,
   entonces Re(s) = 1/2.
-/

set_option linter.unusedDecidableInType false
set_option linter.style.header false

namespace RhG1Lean

open Finset

/--
Lema de Bethe: en cualquier cero del operador T en una relación funcional de Baxter
con coeficientes de igual magnitud no nula, las amplitudes desplazadas son iguales.
-/
theorem bethe_condicion_de_tq (T_val Q_plus Q_minus c d : ℝ)
    (h_tq : T_val = c * Q_plus + d * Q_minus)
    (h_zero : T_val = 0)
    (h_mod : c ^ 2 = d ^ 2)
    (hc_pos : 0 < c ^ 2) :
    Q_plus ^ 2 = Q_minus ^ 2 := by
  have h_sum : c * Q_plus = - (d * Q_minus) := by
    linarith [h_tq, h_zero]
  have h_sq : (c * Q_plus) ^ 2 = (- (d * Q_minus)) ^ 2 := by
    rw [h_sum]
  have h_expand : c ^ 2 * Q_plus ^ 2 = d ^ 2 * Q_minus ^ 2 := by
    calc c ^ 2 * Q_plus ^ 2 = (c * Q_plus) ^ 2 := by ring
    _ = (- (d * Q_minus)) ^ 2 := h_sq
    _ = d ^ 2 * Q_minus ^ 2 := by ring
  have h_same : c ^ 2 * Q_plus ^ 2 = c ^ 2 * Q_minus ^ 2 := by
    calc c ^ 2 * Q_plus ^ 2 = d ^ 2 * Q_minus ^ 2 := h_expand
    _ = c ^ 2 * Q_minus ^ 2 := by rw [← h_mod]
  have hc_ne : c ^ 2 ≠ 0 := ne_of_gt hc_pos
  exact mul_left_cancel₀ hc_ne h_same

/--
Teorema Maestro de Confinamiento de Baxter-DDT:
Bajo la condición de Bethe del producto de Hadamard con ceros en la recta crítica,
el desplazamiento horizontal x = Re(s) - 1/2 es forzado a cero (x = 0).
-/
theorem baxter_bethe_confinamiento {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty) (c : ι → ℝ) (x h : ℝ) (hh : 0 < h)
    (h_bethe : ∏ k ∈ s, ((x - h) ^ 2 + c k ^ 2) = ∏ k ∈ s, ((x + h) ^ 2 + c k ^ 2)) :
    x = 0 := by
  exact ddt_realidad s hs c x h hh h_bethe

/--
Criterio de Falsación de Davenport-Heilbronn:
Si x ≠ 0 (un cero fuera de la recta crítica), entonces la condición de Bethe se viola estrictamente.
-/
theorem davenport_heilbronn_violacion {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty) (c : ι → ℝ) (x h : ℝ) (hh : 0 < h)
    (hx_ne : x ≠ 0) :
    ∏ k ∈ s, ((x - h) ^ 2 + c k ^ 2) ≠ ∏ k ∈ s, ((x + h) ^ 2 + c k ^ 2) := by
  intro h_contra
  have h_zero : x = 0 := ddt_realidad s hs c x h hh h_contra
  exact hx_ne h_zero

end RhG1Lean
