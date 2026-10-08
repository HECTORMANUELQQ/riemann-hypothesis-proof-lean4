import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Ronda 2: la convexidad de |ξ|² y su forma de Riccati

* `re_sq_add_normSq`: Re(z²) + |z|² = 2(Re z)². Con ξ″/ξ = w′ + w², la convexidad de σ ↦ |ξ(σ + it)|² es
  Re w′ + 2(Re w)² ≥ 0 (forma de Riccati a lo largo de cada horizontal).
* `cruzados_suman`: si todos los aᵢ ≥ 0, entonces Σ aᵢ² ≤ (Σ aᵢ)². Es la razón por la que la convexidad vale sin hipótesis
  en σ ≥ 1: allí todos los ceros "empujan del mismo lado".
* `convexa_par_crece`: una función convexa y par crece a partir del centro. Por eso convexidad + espejo ⇒ monotonía en σ.
-/

namespace RhG1Lean

theorem re_sq_add_normSq (z : ℂ) : (z ^ 2).re + Complex.normSq z = 2 * z.re ^ 2 := by
  simp [sq, Complex.normSq_apply]
  ring

theorem cruzados_suman {ι : Type*} (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) :
    ∑ i ∈ s, a i ^ 2 ≤ (∑ i ∈ s, a i) ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    have hs : 0 ≤ ∑ i ∈ s, a i := Finset.sum_nonneg (fun i hi => ha i (Finset.mem_insert_of_mem hi))
    have haj : 0 ≤ a j := ha j (Finset.mem_insert_self j s)
    have ih' := ih (fun i hi => ha i (Finset.mem_insert_of_mem hi))
    nlinarith [mul_nonneg haj hs]

theorem convexa_par_crece {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) (hpar : ∀ x, f (-x) = f x)
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : f x ≤ f y := by
  rcases eq_or_lt_of_le (hx.trans hxy) with hy0 | hy
  · have hx0 : x = 0 := le_antisymm (hy0 ▸ hxy) hx
    rw [hx0, ← hy0]
  · set l := (y - x) / (2 * y) with hl
    have hl0 : 0 ≤ l := div_nonneg (by linarith) (by linarith)
    have hl1 : 0 ≤ 1 - l := by
      rw [hl, sub_nonneg, div_le_one (by linarith)]; linarith
    have hcomb : l • (-y) + (1 - l) • y = x := by
      simp only [smul_eq_mul]
      rw [hl]; field_simp; ring
    have key := hf.2 (Set.mem_univ (-y)) (Set.mem_univ y) hl0 hl1 (by ring)
    rw [hcomb] at key
    simp only [smul_eq_mul, hpar] at key
    linarith

end RhG1Lean
