import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Docs 17–20: la barrera como momento de Wigner, la coherencia de signos y el producto de Hadamard

Para una suma finita Λ(x + iy) = Σⱼ φⱼ e^{(x+iy)uⱼ} (φ, u reales), con parte real A = Σ φⱼ e^{xuⱼ} cos(yuⱼ),
parte imaginaria B = Σ φⱼ e^{xuⱼ} sin(yuⱼ), y Λ′ con A′, B′ (los mismos con un factor uⱼ):

* `modulo_pares`: A² + B² = |Λ|² = Σⱼ Σₖ φⱼ φₖ e^{x(uⱼ+uₖ)} cos(y(uⱼ − uₖ)).
* `wigner_pares`: A′A + B′B = Re(Λ′·conj Λ) = Σⱼ Σₖ ½ φⱼ φₖ (uⱼ + uₖ) e^{x(uⱼ+uₖ)} cos(y(uⱼ − uₖ)).
  Es la versión discreta de Re(ξ′·conj ξ)(½+x+iy) = ½∫₀^∞ a·sinh(xa)·W(a,y) da (R19): la barrera es un momento de la Wigner.
* `coherencia_factor`, `coherencia_producto`: si x > 0 y h > 0, cada factor (x−h)² + c² es menor que (x+h)² + c²,
  y el producto también (para cualquier familia finita no vacía de c). Es el mecanismo de Dorey–Dunning–Tateo y de
  Hermite–Biehler.
* `ddt_realidad`: si los dos productos son iguales (h > 0, familia no vacía), entonces x = 0.
* `coef_prod_no_neg`, `hadamard_coef_no_neg`: el producto de polinomios con coeficientes ≥ 0 tiene coeficientes ≥ 0.
  En particular Πₖ (X² + cₖ²): bajo RH, x² ↦ |ξ(½+x+iy)|² tiene todos sus coeficientes ≥ 0 (docs 20, R20b).
-/

set_option linter.unusedDecidableInType false
set_option linter.style.header false

namespace RhG1Lean

open Finset

theorem modulo_pares {ι : Type*} (s : Finset ι) (φ u : ι → ℝ) (x y : ℝ) :
    (∑ j ∈ s, φ j * Real.exp (x * u j) * Real.cos (y * u j)) ^ 2
      + (∑ j ∈ s, φ j * Real.exp (x * u j) * Real.sin (y * u j)) ^ 2
      = ∑ j ∈ s, ∑ k ∈ s, φ j * φ k * Real.exp (x * (u j + u k)) * Real.cos (y * (u j - u k)) := by
  rw [sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro k _
  rw [mul_add, Real.exp_add, mul_sub, Real.cos_sub]
  ring

theorem wigner_pares {ι : Type*} (s : Finset ι) (φ u : ι → ℝ) (x y : ℝ) :
    (∑ j ∈ s, φ j * u j * Real.exp (x * u j) * Real.cos (y * u j))
        * (∑ k ∈ s, φ k * Real.exp (x * u k) * Real.cos (y * u k))
      + (∑ j ∈ s, φ j * u j * Real.exp (x * u j) * Real.sin (y * u j))
        * (∑ k ∈ s, φ k * Real.exp (x * u k) * Real.sin (y * u k))
      = ∑ j ∈ s, ∑ k ∈ s, (1 / 2 : ℝ) * φ j * φ k * (u j + u k) * Real.exp (x * (u j + u k))
          * Real.cos (y * (u j - u k)) := by
  set T : ι → ι → ℝ := fun j k =>
      φ j * u j * Real.exp (x * u j) * Real.cos (y * u j) * (φ k * Real.exp (x * u k) * Real.cos (y * u k))
      + φ j * u j * Real.exp (x * u j) * Real.sin (y * u j) * (φ k * Real.exp (x * u k) * Real.sin (y * u k)) with hT
  set R : ι → ι → ℝ := fun j k => (1 / 2 : ℝ) * φ j * φ k * (u j + u k) * Real.exp (x * (u j + u k))
      * Real.cos (y * (u j - u k)) with hR
  have key : ∀ j k, T j k + T k j = 2 * R j k := by
    intro j k
    simp only [hT, hR, mul_add, Real.exp_add, mul_sub, Real.cos_sub]
    ring
  have hL : (∑ j ∈ s, φ j * u j * Real.exp (x * u j) * Real.cos (y * u j))
        * (∑ k ∈ s, φ k * Real.exp (x * u k) * Real.cos (y * u k))
      + (∑ j ∈ s, φ j * u j * Real.exp (x * u j) * Real.sin (y * u j))
        * (∑ k ∈ s, φ k * Real.exp (x * u k) * Real.sin (y * u k)) = ∑ j ∈ s, ∑ k ∈ s, T j k := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _
    rw [← Finset.sum_add_distrib]
  have hsym : ∑ j ∈ s, ∑ k ∈ s, T j k = ∑ j ∈ s, ∑ k ∈ s, T k j := Finset.sum_comm
  have h2 : 2 * (∑ j ∈ s, ∑ k ∈ s, T j k) = 2 * ∑ j ∈ s, ∑ k ∈ s, R j k := by
    calc 2 * (∑ j ∈ s, ∑ k ∈ s, T j k) = ∑ j ∈ s, ∑ k ∈ s, T j k + ∑ j ∈ s, ∑ k ∈ s, T k j := by
          rw [← hsym]; ring
      _ = ∑ j ∈ s, ∑ k ∈ s, (T j k + T k j) := by
          rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _; rw [← Finset.sum_add_distrib]
      _ = ∑ j ∈ s, ∑ k ∈ s, 2 * R j k := by
          apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro k _; exact key j k
      _ = 2 * ∑ j ∈ s, ∑ k ∈ s, R j k := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; rw [Finset.mul_sum]
  rw [hL]
  linarith

theorem coherencia_factor (x h c : ℝ) (hx : 0 < x) (hh : 0 < h) :
    (x - h) ^ 2 + c ^ 2 < (x + h) ^ 2 + c ^ 2 := by
  nlinarith [mul_pos hx hh]

theorem coherencia_producto {ι : Type*} [DecidableEq ι] (s : Finset ι) (hs : s.Nonempty) (c : ι → ℝ) (x h : ℝ)
    (hx : 0 < x) (hh : 0 < h) :
    ∏ k ∈ s, ((x - h) ^ 2 + c k ^ 2) < ∏ k ∈ s, ((x + h) ^ 2 + c k ^ 2) := by
  obtain ⟨k, hk⟩ := hs
  have hxh : 0 < x + h := by linarith
  rw [← Finset.mul_prod_erase s (fun i => (x - h) ^ 2 + c i ^ 2) hk,
      ← Finset.mul_prod_erase s (fun i => (x + h) ^ 2 + c i ^ 2) hk]
  have hle : ∏ i ∈ s.erase k, ((x - h) ^ 2 + c i ^ 2) ≤ ∏ i ∈ s.erase k, ((x + h) ^ 2 + c i ^ 2) :=
    Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i _ => le_of_lt (coherencia_factor x h (c i) hx hh))
  have hpos : 0 < ∏ i ∈ s.erase k, ((x + h) ^ 2 + c i ^ 2) := Finset.prod_pos (fun i _ => by positivity)
  calc ((x - h) ^ 2 + c k ^ 2) * ∏ i ∈ s.erase k, ((x - h) ^ 2 + c i ^ 2)
        ≤ ((x - h) ^ 2 + c k ^ 2) * ∏ i ∈ s.erase k, ((x + h) ^ 2 + c i ^ 2) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
    _ < ((x + h) ^ 2 + c k ^ 2) * ∏ i ∈ s.erase k, ((x + h) ^ 2 + c i ^ 2) :=
          mul_lt_mul_of_pos_right (coherencia_factor x h (c k) hx hh) hpos

theorem ddt_realidad {ι : Type*} [DecidableEq ι] (s : Finset ι) (hs : s.Nonempty) (c : ι → ℝ) (x h : ℝ) (hh : 0 < h)
    (heq : ∏ k ∈ s, ((x - h) ^ 2 + c k ^ 2) = ∏ k ∈ s, ((x + h) ^ 2 + c k ^ 2)) : x = 0 := by
  rcases lt_trichotomy x 0 with hneg | h0 | hpos
  · exfalso
    have h1 := coherencia_producto s hs c (-x) h (by linarith) hh
    have e1 : ∏ k ∈ s, ((-x - h) ^ 2 + c k ^ 2) = ∏ k ∈ s, ((x + h) ^ 2 + c k ^ 2) := by
      apply Finset.prod_congr rfl; intro k _; ring
    have e2 : ∏ k ∈ s, ((-x + h) ^ 2 + c k ^ 2) = ∏ k ∈ s, ((x - h) ^ 2 + c k ^ 2) := by
      apply Finset.prod_congr rfl; intro k _; ring
    rw [e1, e2] at h1; linarith
  · exact h0
  · exfalso
    have h1 := coherencia_producto s hs c x h hpos hh
    linarith

theorem coef_mul_no_neg (p q : Polynomial ℝ) (hp : ∀ n, 0 ≤ p.coeff n) (hq : ∀ n, 0 ≤ q.coeff n) :
    ∀ n, 0 ≤ (p * q).coeff n := by
  intro n
  rw [Polynomial.coeff_mul]
  exact Finset.sum_nonneg (fun ij _ => mul_nonneg (hp ij.1) (hq ij.2))

theorem coef_prod_no_neg {ι : Type*} [DecidableEq ι] (s : Finset ι) (p : ι → Polynomial ℝ)
    (h : ∀ i ∈ s, ∀ n, 0 ≤ (p i).coeff n) : ∀ n, 0 ≤ (∏ i ∈ s, p i).coeff n := by
  induction s using Finset.induction_on with
  | empty => intro n; simp [Polynomial.coeff_one]; split_ifs <;> norm_num
  | insert a t ha ih =>
    rw [Finset.prod_insert ha]
    exact coef_mul_no_neg _ _ (h a (Finset.mem_insert_self a t))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem factor_coef_no_neg (c : ℝ) : ∀ n, 0 ≤ (Polynomial.X ^ 2 + Polynomial.C (c ^ 2)).coeff n := by
  intro n
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C]
  split_ifs <;> positivity

theorem hadamard_coef_no_neg {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℝ) :
    ∀ n, 0 ≤ (∏ k ∈ s, (Polynomial.X ^ 2 + Polynomial.C (c k ^ 2))).coeff n :=
  coef_prod_no_neg s _ (fun k _ => factor_coef_no_neg (c k))

end RhG1Lean
