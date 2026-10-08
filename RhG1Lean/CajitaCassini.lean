/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.

# La Cajita deformada: el óvalo de Cassini (incondicional)

La cota de `CajitaUnconditional` sobre la integral de Mellin,

    ‖mellin f_modif w‖ ≤ 3/4 + 3/π      para  -1/2 ≤ Re w ≤ 1,

NO depende de Im w. Así ‖Λ₀(z)‖ ≤ K/2 con K = 3/4 + 3/π en toda la franja
vertical -1 ≤ Re z ≤ 2, a cualquier altura. Lo que limita la Cajita no es Λ₀
sino el factor polinomial de ξ - 1/2 = (z(z-1)/2)·Λ₀(z). Por tanto la forma
natural de la Cajita "deformada hasta su límite" es el óvalo de Cassini

    ‖z‖·‖z - 1‖ · K < 2      (focos 0 y 1, simétrico bajo z ↦ 1 - z),

que corta la recta crítica en |t| < 0.96 (la Cajita original: |t| ≤ 1/2).
La condición de franja se deduce del propio óvalo (fuera de ella ‖z(z-1)‖ > 2).
-/
import RhG1Lean.CajitaUnconditional
import RhG1Lean.XiEntire
import RhG1Lean.StripReduction

open Complex Real

namespace RhG1Lean

/-- Λ₀ acotada en toda la franja vertical -1 ≤ Re z ≤ 2, sin restricción en Im z. -/
theorem zeta₀_norm_le_on_vertical_strip {z : ℂ} (h1 : -1 ≤ z.re) (h2 : z.re ≤ 2) :
    ‖completedRiemannZeta₀ z‖ ≤ (3 / 4 + 3 / π) / 2 := by
  have hre : (z / 2).re = z.re / 2 := by simp
  have hb := norm_mellin_f_modif_le (w := z / 2) (by rw [hre]; linarith) (by rw [hre]; linarith)
  rw [completedRiemannZeta₀_eq_half_mellin, norm_div]
  have h2n : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2n]
  linarith

/-- 1 < K = 3/4 + 3/π < 7/4. -/
theorem cassini_const_bounds : 1 < 3 / 4 + 3 / π ∧ 3 / 4 + 3 / π < 7 / 4 := by
  have hpi : 3 / π < 1 := (div_lt_one Real.pi_pos).mpr Real.pi_gt_three
  have hpi' : 1 / 4 < 3 / π := by
    rw [lt_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_four]
  constructor <;> linarith

/-- El óvalo de Cassini cae dentro de la franja -1 ≤ Re z ≤ 2. -/
theorem re_mem_strip_of_cassini {z : ℂ} (h : ‖z * (z - 1)‖ * (3 / 4 + 3 / π) < 2) :
    -1 ≤ z.re ∧ z.re ≤ 2 := by
  obtain ⟨hK1, _⟩ := cassini_const_bounds
  have hN : ‖z * (z - 1)‖ < 2 := by
    have h0 : 0 ≤ ‖z * (z - 1)‖ := norm_nonneg _
    nlinarith
  rw [norm_mul] at hN
  have ha : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
  have hb : |z.re - 1| ≤ ‖z - 1‖ := by
    have := Complex.abs_re_le_norm (z - 1); simpa using this
  have hprod : |z.re| * |z.re - 1| ≤ ‖z‖ * ‖z - 1‖ :=
    mul_le_mul ha hb (abs_nonneg _) (norm_nonneg _)
  constructor
  · by_contra hlt0
    have hlt := not_le.mp hlt0
    have e1 : |z.re| = -z.re := abs_of_neg (by linarith)
    have e2 : |z.re - 1| = -(z.re - 1) := abs_of_neg (by linarith)
    rw [e1, e2] at hprod
    nlinarith
  · by_contra hlt0
    have hlt := not_le.mp hlt0
    have e1 : |z.re| = z.re := abs_of_pos (by linarith)
    have e2 : |z.re - 1| = z.re - 1 := abs_of_pos (by linarith)
    rw [e1, e2] at hprod
    nlinarith

/-- **Cajita de Cassini.** ‖z(z-1)‖·(3/4 + 3/π) < 2  ⇒  ξ(z) ≠ 0. Sin hipótesis. -/
theorem entireXi_ne_zero_of_cassini {z : ℂ} (h : ‖z * (z - 1)‖ * (3 / 4 + 3 / π) < 2) :
    entireXi z ≠ 0 := by
  obtain ⟨hs1, hs2⟩ := re_mem_strip_of_cassini h
  have hL := zeta₀_norm_le_on_vertical_strip hs1 hs2
  apply entireXi_ne_zero_of_sub_half_lt
  have heq : entireXi z - 1 / 2 = (z * (z - 1) / 2) * completedRiemannZeta₀ z := by
    unfold entireXi; ring
  rw [heq, norm_mul, norm_div]
  have h2n : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2n]
  have hN0 : 0 ≤ ‖z * (z - 1)‖ := norm_nonneg _
  calc ‖z * (z - 1)‖ / 2 * ‖completedRiemannZeta₀ z‖
      ≤ ‖z * (z - 1)‖ / 2 * ((3 / 4 + 3 / π) / 2) :=
        mul_le_mul_of_nonneg_left hL (by positivity)
    _ = (‖z * (z - 1)‖ * (3 / 4 + 3 / π)) / 4 := by ring
    _ < 2 / 4 := by linarith
    _ = 1 / 2 := by norm_num

/-- Corolario: el óvalo ‖z(z-1)‖ ≤ 1 (más simple) es libre de ceros. -/
theorem entireXi_ne_zero_of_norm_mul_le_one {z : ℂ} (h : ‖z * (z - 1)‖ ≤ 1) :
    entireXi z ≠ 0 := by
  obtain ⟨_, hK⟩ := cassini_const_bounds
  apply entireXi_ne_zero_of_cassini
  have h0 : 0 ≤ ‖z * (z - 1)‖ := norm_nonneg _
  nlinarith

/-- Corolario en la recta crítica: |t| ≤ 9/10 ⇒ ξ(1/2 + i t) ≠ 0 (antes: |t| ≤ 1/2). -/
theorem entireXi_ne_zero_critical_segment {z : ℂ} (hre : z.re = 1 / 2) (him : |z.im| ≤ 9 / 10) :
    entireXi z ≠ 0 := by
  obtain ⟨_, hK⟩ := cassini_const_bounds
  apply entireXi_ne_zero_of_cassini
  -- z(z-1) = -(1/4 + t²) en la recta crítica
  have hprod : z * (z - 1) = ((-(1 / 4 + z.im ^ 2) : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [Complex.mul_re, hre, sq]; ring
    · simp [Complex.mul_im, hre, sq]; ring
  rw [hprod, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
  have ht2 : z.im ^ 2 ≤ 81 / 100 := by
    have := sq_abs z.im; nlinarith [abs_nonneg z.im]
  have hpos : 0 < 3 / 4 + 3 / π := by positivity
  calc (1 / 4 + z.im ^ 2) * (3 / 4 + 3 / π) ≤ (1 / 4 + 81 / 100) * (3 / 4 + 3 / π) :=
        mul_le_mul_of_nonneg_right (by linarith) hpos.le
    _ < 2 := by nlinarith

/-- Corolario: el rectángulo ampliado [1/2, 1] × [-3/4, 3/4] es libre de ceros de ξ. -/
theorem entireXi_ne_zero_big_box {z : ℂ} (h1 : 1 / 2 ≤ z.re) (h2 : z.re ≤ 1)
    (him : |z.im| ≤ 3 / 4) : entireXi z ≠ 0 := by
  obtain ⟨_, hK⟩ := cassini_const_bounds
  apply entireXi_ne_zero_of_cassini
  have ht2 : z.im ^ 2 ≤ 9 / 16 := by
    have := sq_abs z.im; nlinarith [abs_nonneg z.im]
  -- ‖z‖² ≤ 1 + 9/16 y ‖z-1‖² ≤ 1/4 + 9/16, luego ‖z(z-1)‖² ≤ (25/16)(13/16) ≤ (57/50)²
  have hA : ‖z‖ ^ 2 ≤ 25 / 16 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; nlinarith
  have hB : ‖z - 1‖ ^ 2 ≤ 13 / 16 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; nlinarith
  have hP : ‖z * (z - 1)‖ ≤ 57 / 50 := by
    rw [norm_mul]
    have hsq : (‖z‖ * ‖z - 1‖) ^ 2 ≤ (57 / 50) ^ 2 := by
      rw [mul_pow]
      calc ‖z‖ ^ 2 * ‖z - 1‖ ^ 2 ≤ 25 / 16 * (13 / 16) :=
            mul_le_mul hA hB (sq_nonneg _) (by norm_num)
        _ ≤ (57 / 50) ^ 2 := by norm_num
    have hab : 0 ≤ ‖z‖ * ‖z - 1‖ := mul_nonneg (norm_nonneg z) (norm_nonneg (z - 1))
    nlinarith [hsq, hab]
  have h0 : 0 ≤ ‖z * (z - 1)‖ := norm_nonneg _
  -- 57/50 · 7/4 = 399/200 < 2
  nlinarith

/-- ζ ≠ 0 en el óvalo de Cassini dentro de la franja crítica. -/
theorem riemannZeta_ne_zero_of_cassini {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (h : ‖s * (s - 1)‖ * (3 / 4 + 3 / π) < 2) : riemannZeta s ≠ 0 := fun hz =>
  entireXi_ne_zero_of_cassini h ((entireXi_eq_zero_iff_zeta_of_mem_strip h0 h1).mpr hz)

end RhG1Lean
