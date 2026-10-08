/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.

# Los faros del video (Basilea, 3Blue1Brown / Wästlund), tal cual, sobre el puente

1. Pitágoras inverso en el círculo:   1/sin²y + 1/cos²y = 4/sin²(2y).
2. Duplicación (el corazón del video): Σ_{k<2^m} 1/sin²(x + kπ/2^m) = 4^m / sin²(2^m x).
3. Brillo invariante: 2^m faros en un círculo de circunferencia 2^{m+1} (espaciados 2), visto
   desde el punto opuesto a la mitad de un hueco, alumbran SIEMPRE π²/4, a toda duplicación
   (el límite son los faros en los impares de la recta).
4. Cada primo es un puente perfecto del video: los ceros de 1 - p^{-s} forman una fila perfecta
   de faros en la pared Re s = 0, separados 2π/log p.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Log

set_option linter.style.header false
set_option linter.unusedVariables false

open Real Finset

namespace RhG1Lean

/-- **Pitágoras inverso en el círculo** (el paso clave del video). -/
theorem pitagoras_circulo {y : ℝ} (hs : Real.sin y ≠ 0) (hc : Real.cos y ≠ 0) :
    1 / Real.sin y ^ 2 + 1 / Real.cos y ^ 2 = 4 / Real.sin (2 * y) ^ 2 := by
  rw [Real.sin_two_mul]
  have h := Real.sin_sq_add_cos_sq y
  field_simp
  linear_combination 4 * h

/-- Si sin z = 0, entonces sin(n z) = 0. -/
theorem sin_nat_mul_eq_zero {z : ℝ} (h : Real.sin z = 0) (n : ℕ) : Real.sin (n * z) = 0 := by
  obtain ⟨j, hj⟩ := Real.sin_eq_zero_iff.mp h
  rw [← hj, show (n : ℝ) * (j * π) = ((n * j : ℤ) : ℝ) * π by push_cast; ring]
  exact Real.sin_int_mul_pi _

/-- **La duplicación de los faros** (el teorema central del video):
Σ_{k<2^m} 1/sin²(x + kπ/2^m) = 4^m / sin²(2^m x), si sin(2^m x) ≠ 0. -/
theorem duplicacion_faros (m : ℕ) : ∀ x : ℝ, Real.sin ((2 : ℝ) ^ m * x) ≠ 0 →
    ∑ k ∈ range (2 ^ m), 1 / Real.sin (x + k * π / (2 : ℝ) ^ m) ^ 2 =
      4 ^ m / Real.sin ((2 : ℝ) ^ m * x) ^ 2 := by
  induction m with
  | zero => intro x _; simp
  | succ m ih =>
    intro x hx
    have hsplit : (2 : ℕ) ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [pow_succ]; ring
    rw [hsplit, Finset.sum_range_add, ← Finset.sum_add_distrib]
    -- cada pareja (k, 2^m + k) es un triángulo rectángulo inscrito
    have hpair : ∀ k ∈ range (2 ^ m),
        1 / Real.sin (x + k * π / (2 : ℝ) ^ (m + 1)) ^ 2 +
          1 / Real.sin (x + ((2 ^ m + k : ℕ) : ℝ) * π / (2 : ℝ) ^ (m + 1)) ^ 2 =
        4 / Real.sin (2 * x + k * π / (2 : ℝ) ^ m) ^ 2 := by
      intro k _
      set y := x + k * π / (2 : ℝ) ^ (m + 1) with hy
      have h2m : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
      have hshift : x + ((2 ^ m + k : ℕ) : ℝ) * π / (2 : ℝ) ^ (m + 1) = y + π / 2 := by
        rw [hy]; push_cast; field_simp; ring
      have hdouble : 2 * x + k * π / (2 : ℝ) ^ m = 2 * y := by
        rw [hy]; field_simp; ring
      -- sin(2y) ≠ 0, porque sin(2^m · 2y) = ± sin(2^{m+1} x)
      have h2y : Real.sin (2 * y) ≠ 0 := by
        intro h0
        have h1 := sin_nat_mul_eq_zero h0 (2 ^ m)
        have h3 : ((2 ^ m : ℕ) : ℝ) * (2 * y) = (2 : ℝ) ^ (m + 1) * x + (k : ℕ) * π := by
          rw [hy]; push_cast; field_simp; ring
        rw [h3, Real.sin_add_nat_mul_pi] at h1
        have : Real.sin ((2 : ℝ) ^ (m + 1) * x) = 0 := by
          rcases neg_one_pow_eq_or ℝ k with h | h <;> rw [h] at h1 <;> linarith
        exact hx this
      have hsy : Real.sin y ≠ 0 := by
        intro h0; apply h2y; rw [Real.sin_two_mul, h0]; ring
      have hcy : Real.cos y ≠ 0 := by
        intro h0; apply h2y; rw [Real.sin_two_mul, h0]; ring
      rw [hshift, Real.sin_add_pi_div_two, hdouble]
      exact pitagoras_circulo hsy hcy
    rw [Finset.sum_congr rfl hpair]
    have hx' : Real.sin ((2 : ℝ) ^ m * (2 * x)) ≠ 0 := by
      rw [show (2 : ℝ) ^ m * (2 * x) = (2 : ℝ) ^ (m + 1) * x by ring]; exact hx
    have hih := ih (2 * x) hx'
    have hsum : ∑ k ∈ range (2 ^ m), 1 / Real.sin (2 * x + k * π / (2 : ℝ) ^ m) ^ 2 =
        4 ^ m / Real.sin ((2 : ℝ) ^ m * (2 * x)) ^ 2 := hih
    rw [show (∑ k ∈ range (2 ^ m), 4 / Real.sin (2 * x + k * π / (2 : ℝ) ^ m) ^ 2) =
        4 * ∑ k ∈ range (2 ^ m), 1 / Real.sin (2 * x + k * π / (2 : ℝ) ^ m) ^ 2 by
      rw [Finset.mul_sum]; congr 1; funext k; ring]
    rw [hsum, show (2 : ℝ) ^ m * (2 * x) = (2 : ℝ) ^ (m + 1) * x by ring, pow_succ]
    ring

/-- **El brillo no cambia al duplicar** (el video): 2^m faros espaciados en un círculo de radio
2^m/π, vistos desde el punto a mitad de un hueco, alumbran siempre π²/4. -/
theorem brillo_invariante (m : ℕ) :
    ∑ k ∈ range (2 ^ m),
      1 / ((2 : ℝ) ^ (m + 1) / π * Real.sin ((2 * k + 1) * π / (2 : ℝ) ^ (m + 1))) ^ 2 =
      π ^ 2 / 4 := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (m + 1) := by positivity
  have hx : Real.sin ((2 : ℝ) ^ m * (π / (2 : ℝ) ^ (m + 1))) ≠ 0 := by
    rw [show (2 : ℝ) ^ m * (π / (2 : ℝ) ^ (m + 1)) = π / 2 by rw [pow_succ]; field_simp]
    rw [Real.sin_pi_div_two]; norm_num
  have hd := duplicacion_faros m (π / (2 : ℝ) ^ (m + 1)) hx
  have hval : Real.sin ((2 : ℝ) ^ m * (π / (2 : ℝ) ^ (m + 1))) = 1 := by
    rw [show (2 : ℝ) ^ m * (π / (2 : ℝ) ^ (m + 1)) = π / 2 by rw [pow_succ]; field_simp]
    exact Real.sin_pi_div_two
  rw [hval] at hd
  have hterm : ∀ k ∈ range (2 ^ m),
      1 / ((2 : ℝ) ^ (m + 1) / π * Real.sin ((2 * k + 1) * π / (2 : ℝ) ^ (m + 1))) ^ 2 =
      (π ^ 2 / ((2 : ℝ) ^ (m + 1)) ^ 2) *
        (1 / Real.sin (π / (2 : ℝ) ^ (m + 1) + k * π / (2 : ℝ) ^ m) ^ 2) := by
    intro k _
    have harg : (2 * (k : ℝ) + 1) * π / (2 : ℝ) ^ (m + 1) =
        π / (2 : ℝ) ^ (m + 1) + k * π / (2 : ℝ) ^ m := by
      rw [pow_succ]; field_simp; ring
    rw [harg]
    have hpi : π ≠ 0 := Real.pi_ne_zero
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hd, pow_succ, one_pow]
  have h4 : (4 : ℝ) ^ m = 2 ^ (m * 2) := by rw [pow_mul']; norm_num
  field_simp
  rw [h4]
  ring

/-- **Cada primo es un puente perfecto del video:** los ceros de 1 - p^{-s} son exactamente
s = 2πik/log p, una fila perfecta de faros en la pared Re s = 0. -/
theorem faros_del_primo {p : ℝ} (hp : 1 < p) (s : ℂ) :
    1 - (p : ℂ) ^ (-s) = 0 ↔ ∃ k : ℤ, s = 2 * π * Complex.I * k / Real.log p := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (by linarith : p ≠ 0)
  have hlog : Complex.log (p : ℂ) = (Real.log p : ℂ) := (Complex.ofReal_log (by linarith)).symm
  have hlogpos : 0 < Real.log p := Real.log_pos hp
  have hlogne : (Real.log p : ℂ) ≠ 0 := by exact_mod_cast hlogpos.ne'
  rw [Complex.cpow_def_of_ne_zero hp0, hlog, sub_eq_zero, eq_comm, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    field_simp
    push_cast
    linear_combination -hn
  · rintro ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    rw [hk]
    field_simp
    push_cast
    ring

end RhG1Lean
