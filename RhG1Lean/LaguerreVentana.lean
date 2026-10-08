import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Ronda 5 (II): la Laguerre en la ventana de Riemann–Siegel, término a término

Con Z = Σ aᵢ cos φᵢ, Z′ = −Σ aᵢ ωᵢ sin φᵢ y Z″ = −Σ aᵢ ωᵢ² cos φᵢ (fases con φ″ = 0):

* `laguerre_pares`: Z′² − Z·Z″ = ¼ Σᵢ Σⱼ aᵢ aⱼ [(ωᵢ + ωⱼ)² cos(φᵢ − φⱼ) + (ωᵢ − ωⱼ)² cos(φᵢ + φⱼ)].
  La diagonal (i = j) da Σ aᵢ² ωᵢ² ≥ 0 (el presupuesto). La parte "lenta" lleva las fases de las razones (cos(φᵢ − φⱼ)) y
  la "rápida" la portadora del espejo (cos(φᵢ + φⱼ)).
-/

namespace RhG1Lean

theorem laguerre_pares {ι : Type*} (s : Finset ι) (a ω φ : ι → ℝ) :
    (∑ i ∈ s, a i * ω i * Real.sin (φ i)) ^ 2 + (∑ i ∈ s, a i * Real.cos (φ i)) * (∑ i ∈ s, a i * ω i ^ 2 * Real.cos (φ i))
      = ∑ i ∈ s, ∑ j ∈ s, (1 / 4 : ℝ) * a i * a j *
          ((ω i + ω j) ^ 2 * Real.cos (φ i - φ j) + (ω i - ω j) ^ 2 * Real.cos (φ i + φ j)) := by
  set T : ι → ι → ℝ := fun i j => a i * ω i * Real.sin (φ i) * (a j * ω j * Real.sin (φ j))
      + a i * Real.cos (φ i) * (a j * ω j ^ 2 * Real.cos (φ j)) with hT
  set R : ι → ι → ℝ := fun i j => (1 / 4 : ℝ) * a i * a j *
      ((ω i + ω j) ^ 2 * Real.cos (φ i - φ j) + (ω i - ω j) ^ 2 * Real.cos (φ i + φ j)) with hR
  have key : ∀ i j, T i j + T j i = 2 * R i j := by
    intro i j
    simp only [hT, hR, Real.cos_sub, Real.cos_add]
    ring
  have hL : (∑ i ∈ s, a i * ω i * Real.sin (φ i)) ^ 2 + (∑ i ∈ s, a i * Real.cos (φ i)) * (∑ i ∈ s, a i * ω i ^ 2 * Real.cos (φ i))
      = ∑ i ∈ s, ∑ j ∈ s, T i j := by
    rw [sq, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib]
  have hsym : ∑ i ∈ s, ∑ j ∈ s, T i j = ∑ i ∈ s, ∑ j ∈ s, T j i := Finset.sum_comm
  have h2 : 2 * (∑ i ∈ s, ∑ j ∈ s, T i j) = 2 * ∑ i ∈ s, ∑ j ∈ s, R i j := by
    calc 2 * (∑ i ∈ s, ∑ j ∈ s, T i j) = ∑ i ∈ s, ∑ j ∈ s, T i j + ∑ i ∈ s, ∑ j ∈ s, T j i := by
          rw [← hsym]; ring
      _ = ∑ i ∈ s, ∑ j ∈ s, (T i j + T j i) := by
          rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _; rw [← Finset.sum_add_distrib]
      _ = ∑ i ∈ s, ∑ j ∈ s, 2 * R i j := by
          apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; exact key i j
      _ = 2 * ∑ i ∈ s, ∑ j ∈ s, R i j := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum]
  rw [hL]
  linarith

end RhG1Lean
