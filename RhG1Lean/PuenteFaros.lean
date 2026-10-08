/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.

# El puente colgante de faros (idea de los faros de Euler / Basilea, 3Blue1Brown)

Puente colgante infinito: la cubierta es el pasillo (la recta crítica); cada huésped es un
FARO anclado a la cubierta; la cuerda principal es log|f|. Brillo de un faro a distancia d:
1/d² (ley del inverso del cuadrado, como en la prueba de los faros de π²/6).

Cantidad de Laguerre  L(f)(x) = f'(x)² − f(x) f''(x) = −f(x)² (log f)''(x).
"Brillo total en x" = L(f)(x) / f(x)².

* Pitágoras inverso (el truco de los faros): 1/a² + 1/b² = 1/h².
* El brillo se suma por tramos: L(fg) = g² L(f) + f² L(g).
* Un faro sobre la cubierta (factor x − a) aporta brillo 1/(x − a)² > 0.
* Un faro FUERA de la cubierta (factor (x − a)² + b²) es un faro oscuro: aporta
  2((x − a)² − b²)/((x − a)² + b²)², negativo justo debajo de él.
* Puente finito con todos sus faros sobre la cubierta: L > 0 fuera de los faros, luego en todo
  extremo f·f'' < 0: NUNCA un extremo al revés (la maqueta perfecta).
* Un faro oscuro produce un extremo al revés justo debajo de él.
-/
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Polynomial.Derivative

set_option linter.style.header false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false

open Polynomial

namespace RhG1Lean

/-- **Pitágoras inverso** (el truco central de los faros): dos faros en los extremos de los
catetos alumbran el ángulo recto igual que uno solo al pie de la altura. -/
theorem pitagoras_inverso {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    1 / a ^ 2 + 1 / b ^ 2 = 1 / (a * b / Real.sqrt (a ^ 2 + b ^ 2)) ^ 2 := by
  rw [div_pow, Real.sq_sqrt (by positivity)]
  field_simp
  ring

/-- Cantidad de Laguerre de un polinomio en x: L(p)(x) = p'(x)² − p(x) p''(x). -/
noncomputable def laguerreL (p : ℝ[X]) (x : ℝ) : ℝ :=
  (p.derivative.eval x) ^ 2 - p.eval x * p.derivative.derivative.eval x

/-- **El brillo se suma por tramos del puente:** L(f g) = g² L(f) + f² L(g). -/
theorem laguerreL_mul (f g : ℝ[X]) (x : ℝ) :
    laguerreL (f * g) x = (g.eval x) ^ 2 * laguerreL f x + (f.eval x) ^ 2 * laguerreL g x := by
  unfold laguerreL
  simp only [derivative_mul, derivative_add, eval_add, eval_mul]
  ring

/-- Un faro sobre la cubierta: L(x − a) = 1, es decir brillo 1/(x − a)². -/
theorem laguerreL_faro (a x : ℝ) : laguerreL (X - C a) x = 1 := by
  unfold laguerreL
  simp

/-- **Un faro fuera de la cubierta es un faro oscuro:** para Q = (x − a)² + b²,
L(Q)(x) = 2((x − a)² − b²), negativo cuando |x − a| < b. -/
theorem laguerreL_faro_oscuro (a b x : ℝ) :
    laguerreL ((X - C a) * (X - C a) + C (b ^ 2)) x = 2 * ((x - a) ^ 2 - b ^ 2) := by
  unfold laguerreL
  simp only [derivative_add, derivative_mul, derivative_sub, derivative_X, derivative_C,
    eval_add, eval_mul, eval_sub, eval_X, eval_C, eval_one, sub_zero, one_mul,
    mul_one, add_zero]
  ring

/-- El brillo de un puente finito con todos sus faros sobre la cubierta es ≥ 0. -/
theorem laguerreL_prod_nonneg {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℝ) (x : ℝ) :
    0 ≤ laguerreL (∏ j ∈ s, (X - C (a j))) x := by
  refine Finset.induction_on s ?_ ?_
  · simp [laguerreL]
  · intro j t hj ih
    rw [Finset.prod_insert hj, laguerreL_mul, laguerreL_faro]
    exact add_nonneg (mul_nonneg (sq_nonneg _) (le_of_eq rfl |>.trans (by norm_num)))
      (mul_nonneg (sq_nonneg _) ih)

/-- **Brillo estrictamente positivo** fuera de los faros (si hay al menos un faro). -/
theorem laguerreL_prod_pos {ι : Type*} [DecidableEq ι] (s : Finset ι) (hs : s.Nonempty)
    (a : ι → ℝ) (x : ℝ) (hx : ∀ j ∈ s, x ≠ a j) :
    0 < laguerreL (∏ j ∈ s, (X - C (a j))) x := by
  obtain ⟨j, hj⟩ := hs
  rw [← Finset.mul_prod_erase s _ hj, laguerreL_mul, laguerreL_faro]
  have hrest : (∏ k ∈ s.erase j, (X - C (a k))).eval x ≠ 0 := by
    rw [eval_prod, Finset.prod_ne_zero_iff]
    intro k hk
    simp only [eval_sub, eval_X, eval_C]
    exact sub_ne_zero.mpr (hx k (Finset.mem_of_mem_erase hk))
  have h1 : 0 < ((∏ k ∈ s.erase j, (X - C (a k))).eval x) ^ 2 * 1 := by
    rw [mul_one]; positivity
  have h2 := laguerreL_prod_nonneg (s.erase j) a x
  have h3 : 0 ≤ ((X - C (a j)).eval x) ^ 2 * laguerreL (∏ k ∈ s.erase j, (X - C (a k))) x :=
    mul_nonneg (sq_nonneg _) h2
  linarith

/-- **El puente finito nunca se voltea.** Si todos los faros están sobre la cubierta, en todo
extremo (p'(x) = 0, fuera de los faros) se cumple p(x)·p''(x) < 0: el extremo es normal. -/
theorem puente_finito_sin_volteo {ι : Type*} [DecidableEq ι] (s : Finset ι) (hs : s.Nonempty)
    (a : ι → ℝ) (x : ℝ) (hx : ∀ j ∈ s, x ≠ a j)
    (hext : (∏ j ∈ s, (X - C (a j))).derivative.eval x = 0) :
    (∏ j ∈ s, (X - C (a j))).eval x * (∏ j ∈ s, (X - C (a j))).derivative.derivative.eval x
      < 0 := by
  have h := laguerreL_prod_pos s hs a x hx
  unfold laguerreL at h
  rw [hext] at h
  nlinarith [h]

/-- La misma ley con derivadas reales (`deriv`) de la función x ↦ p(x). -/
theorem puente_finito_sin_volteo_deriv {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (hs : s.Nonempty) (a : ι → ℝ) (x : ℝ) (hx : ∀ j ∈ s, x ≠ a j)
    (hext : deriv (fun y => (∏ j ∈ s, (X - C (a j))).eval y) x = 0) :
    (∏ j ∈ s, (X - C (a j))).eval x *
      deriv (deriv (fun y => (∏ j ∈ s, (X - C (a j))).eval y)) x < 0 := by
  set p := ∏ j ∈ s, (X - C (a j)) with hp
  have hd : deriv (fun y => p.eval y) = fun y => p.derivative.eval y := by
    funext y; exact Polynomial.deriv p
  rw [hd] at hext ⊢
  rw [Polynomial.deriv]
  exact puente_finito_sin_volteo s hs a x hx hext

/-- **Un faro oscuro produce un extremo al revés justo debajo de él.** Para
Q = (x − a)² + b² con b ≠ 0: Q'(a) = 0 y Q(a)·Q''(a) = 2b² > 0. -/
theorem faro_oscuro_volteo (a b : ℝ) (hb : b ≠ 0) :
    ((X - C a) * (X - C a) + C (b ^ 2)).derivative.eval a = 0 ∧
      0 < ((X - C a) * (X - C a) + C (b ^ 2)).eval a *
        ((X - C a) * (X - C a) + C (b ^ 2)).derivative.derivative.eval a := by
  simp only [derivative_add, derivative_mul, derivative_sub, derivative_X, derivative_C,
    eval_add, eval_mul, eval_sub, eval_X, eval_C, eval_one, sub_zero, one_mul,
    mul_one, zero_add, add_zero, sub_self, mul_zero]
  refine ⟨trivial, ?_⟩
  have : 0 < b ^ 2 := by positivity
  linarith

end RhG1Lean
