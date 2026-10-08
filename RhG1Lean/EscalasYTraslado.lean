import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Ataque, ronda 1: monotonía por escalas y la costura trasladada

* `escala_par_crece`: para x, h > 0 y n ≥ 1, (x − h)^{2n} < (x + h)^{2n}. Con |ξ(½ + y + it)|² = Σ L_n y^{2n}, si todas
  las L_n ≥ 0 entonces |ξ| crece al alejarse de la pared a toda escala.
* `monotonia_finita`: versión con sumas finitas de coeficientes ≥ 0.
* `velocidad_traslado`: si w₋ = −conj w₊ (espejo), entonces (w₊ + w₋)/(w₊ − w₋) = i·Im w₊ / Re w₊. Es la velocidad de los
  ceros de ξ(s + h) + ξ(s − h) sobre la pared: dt/dh = −Im w₊ / Re w₊, y dos ceros solo chocan donde Re w₊ = 0 (borde de bahía).
-/

namespace RhG1Lean

open Complex

theorem escala_par_crece {x h : ℝ} (hx : 0 < x) (hh : 0 < h) {n : ℕ} (hn : 0 < n) :
    (x - h) ^ (2 * n) < (x + h) ^ (2 * n) := by
  have h2 : (x - h) ^ 2 < (x + h) ^ 2 := by nlinarith
  rw [pow_mul, pow_mul]
  exact pow_lt_pow_left₀ h2 (sq_nonneg _) hn.ne'

theorem monotonia_finita {x h : ℝ} (hx : 0 < x) (hh : 0 < h) (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (N : ℕ) :
    ∑ n ∈ Finset.range N, c n * (x - h) ^ (2 * n) ≤ ∑ n ∈ Finset.range N, c n * (x + h) ^ (2 * n) := by
  apply Finset.sum_le_sum
  intro n _
  apply mul_le_mul_of_nonneg_left _ (hc n)
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · simp [h0]
  · exact (escala_par_crece hx hh hpos).le

theorem velocidad_traslado (w : ℂ) (hre : w.re ≠ 0) :
    (w + -(starRingEnd ℂ) w) / (w - -(starRingEnd ℂ) w) = I * ((w.im / w.re : ℝ) : ℂ) := by
  have h1 : w + -(starRingEnd ℂ) w = ((2 * w.im : ℝ) : ℂ) * I := by
    rw [← sub_eq_add_neg, Complex.sub_conj]
  have h2 : w - -(starRingEnd ℂ) w = ((2 * w.re : ℝ) : ℂ) := by
    rw [sub_neg_eq_add, Complex.add_conj]
  have h3 : ((2 * w.re : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast mul_ne_zero two_ne_zero hre
  have h4 : (w.re : ℂ) ≠ 0 := by exact_mod_cast hre
  rw [h1, h2, div_eq_iff h3]
  push_cast
  field_simp

end RhG1Lean
