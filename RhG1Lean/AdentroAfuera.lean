/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.

# Adentro hacia afuera y afuera hacia adentro (Partida 3)

**De adentro hacia afuera** (desde el pasillo Re s = 1/2):
* **Ley del dipolo**: cada apagón `a` y su imagen en el espejo `a* = 1 − conj a` forman un dipolo;
  `‖s − a*‖² − ‖s − a‖² = (2·Re s − 1)(2·Re a − 1)`. En el ala, un apagón derecho está más cerca
  que su imagen (el reflejo gana a su lado); en la pared las dos distancias son iguales.
* **El jalón en la pared**: en Re s = 1/2, `Re (1/(s − a)) = (1/2 − Re a)/‖s − a‖²`: un apagón a la derecha
  jala la rosa hacia atrás (negativo) y uno a la izquierda la empuja hacia adelante (positivo).
* **Espejo unitario**: el cociente q = E♯/E cumple q · q♯ = 1.

**De afuera hacia adentro** (desde el ala lejana):
* **Muralla de Euler**: para Re s ≥ 2, toda suma parcial `∑_{n ≤ N} n^{−s}` mide al menos `2 − π²/6`:
  la luz de las ventanas no se apaga allá afuera, para ningún número de ventanas.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.NumberTheory.ZetaValues
import RhG1Lean.RutaCostura

open Complex Finset ComplexConjugate

namespace RhG1Lean

/-- La imagen de un punto en el gran espejo del pasillo. -/
def imagenPasillo (a : ℂ) : ℂ := 1 - conj a

/-- **Ley del dipolo.** -/
theorem ley_dipolo (s a : ℂ) :
    ‖s - imagenPasillo a‖ ^ 2 - ‖s - a‖ ^ 2 = (2 * s.re - 1) * (2 * a.re - 1) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [imagenPasillo, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.conj_re, Complex.conj_im]
  ring

/-- En el ala, un apagón derecho está más cerca que su imagen. -/
theorem dipolo_gana_en_ala {s a : ℂ} (hs : 1 / 2 < s.re) (ha : 1 / 2 < a.re) :
    ‖s - a‖ < ‖s - imagenPasillo a‖ := by
  have h := ley_dipolo s a
  have hpos : 0 < (2 * s.re - 1) * (2 * a.re - 1) := mul_pos (by linarith) (by linarith)
  have h2 : ‖s - a‖ ^ 2 < ‖s - imagenPasillo a‖ ^ 2 := by linarith
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h2

/-- En la pared, un apagón y su imagen están a la misma distancia. -/
theorem dipolo_pared {s a : ℂ} (hs : s.re = 1 / 2) : ‖s - imagenPasillo a‖ = ‖s - a‖ := by
  have h := ley_dipolo s a
  rw [hs] at h
  have h2 : ‖s - imagenPasillo a‖ ^ 2 = ‖s - a‖ ^ 2 := by nlinarith
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

/-- **El jalón en la pared**: la contribución de un apagón a la rapidez de la rosa. -/
theorem jalon_pared {s a : ℂ} (hs : s.re = 1 / 2) :
    ((s - a)⁻¹).re = (1 / 2 - a.re) / Complex.normSq (s - a) := by
  rw [Complex.inv_re, Complex.sub_re, hs]

/-- Un apagón a la derecha de la pared jala la rosa hacia atrás. -/
theorem jalon_derecho_negativo {s a : ℂ} (hs : s.re = 1 / 2) (ha : 1 / 2 < a.re) :
    ((s - a)⁻¹).re < 0 := by
  rw [jalon_pared hs]
  have hne : s - a ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; simp [Complex.sub_re, hs] at this; linarith
  exact div_neg_of_neg_of_pos (by linarith) (Complex.normSq_pos.mpr hne)

/-- Un apagón a la izquierda de la pared empuja la rosa hacia adelante. -/
theorem empuje_izquierdo_positivo {s a : ℂ} (hs : s.re = 1 / 2) (ha : a.re < 1 / 2) :
    0 < ((s - a)⁻¹).re := by
  rw [jalon_pared hs]
  have hne : s - a ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; simp [Complex.sub_re, hs] at this; linarith
  exact div_pos (by linarith) (Complex.normSq_pos.mpr hne)

/-- El espejo es una involución: reflejar dos veces deja todo igual. -/
theorem reflejo_reflejo (E : ℂ → ℂ) : reflejo (reflejo E) = E := by
  funext s
  simp [reflejo]

/-- **Espejo unitario**: el cociente q = E♯/E y su reflejo se multiplican a 1. -/
theorem espejo_unitario {E : ℂ → ℂ} {s : ℂ} (h1 : E s ≠ 0) (h2 : reflejo E s ≠ 0) :
    (reflejo E s / E s) * reflejo (fun z => reflejo E z / E z) s = 1 := by
  have hr : reflejo (fun z => reflejo E z / E z) s = E s / reflejo E s := by
    simp [reflejo]
  rw [hr]
  field_simp

/-- Una ventana lejana pesa poco: para Re s ≥ 2, ‖(n+2)^(−s)‖ ≤ 1/(n+2)². -/
theorem norm_ventana_le (s : ℂ) (hs : 2 ≤ s.re) (n : ℕ) :
    ‖((n : ℂ) + 2) ^ (-s)‖ ≤ 1 / ((n : ℝ) + 2) ^ 2 := by
  have hcast : ((n : ℂ) + 2) = ((n + 2 : ℕ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.norm_natCast_cpow_of_pos (by omega)]
  simp only [Complex.neg_re]
  push_cast
  have hx : (1 : ℝ) ≤ (n : ℝ) + 2 := by have := n.cast_nonneg (α := ℝ); linarith
  calc ((n : ℝ) + 2) ^ (-s.re) ≤ ((n : ℝ) + 2) ^ (-(2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hx (by linarith)
    _ = 1 / ((n : ℝ) + 2) ^ 2 := by
        rw [Real.rpow_neg (by linarith), one_div]
        norm_cast

/-- La cola de Basilea: ∑_{n ≥ 0} 1/(n+2)² = π²/6 − 1. -/
theorem cola_basilea : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 2) ^ 2) (Real.pi ^ 2 / 6 - 1) := by
  have h := (hasSum_nat_add_iff' 2).mpr hasSum_zeta_two
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one] at h
  convert h using 2
  · push_cast; ring_nf
  · norm_num

/-- **Muralla de Euler.** Para Re s ≥ 2, toda suma parcial de la serie de Dirichlet de ζ mide al menos
2 − π²/6 (≈ 0.355): allá afuera la luz de las ventanas no se apaga, con ninguna cantidad de ventanas. -/
theorem muralla_euler (s : ℂ) (hs : 2 ≤ s.re) (N : ℕ) :
    2 - Real.pi ^ 2 / 6 ≤ ‖∑ n ∈ range (N + 1), ((n : ℂ) + 1) ^ (-s)‖ := by
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_add, Complex.one_cpow]
  have hcola : ‖∑ n ∈ range N, (((n + 1 : ℕ) : ℂ) + 1) ^ (-s)‖ ≤ Real.pi ^ 2 / 6 - 1 := by
    calc ‖∑ n ∈ range N, (((n + 1 : ℕ) : ℂ) + 1) ^ (-s)‖
        ≤ ∑ n ∈ range N, ‖(((n + 1 : ℕ) : ℂ) + 1) ^ (-s)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ range N, 1 / ((n : ℝ) + 2) ^ 2 := by
          apply Finset.sum_le_sum; intro n _
          have := norm_ventana_le s hs n
          have e : (((n + 1 : ℕ) : ℂ) + 1) = (n : ℂ) + 2 := by push_cast; ring
          rw [e]; exact this
      _ ≤ Real.pi ^ 2 / 6 - 1 := sum_le_hasSum _ (fun i _ => by positivity) cola_basilea
  have htri : 1 - ‖∑ n ∈ range N, (((n + 1 : ℕ) : ℂ) + 1) ^ (-s)‖
      ≤ ‖∑ n ∈ range N, (((n + 1 : ℕ) : ℂ) + 1) ^ (-s) + 1‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-(∑ n ∈ range N, (((n + 1 : ℕ) : ℂ) + 1) ^ (-s)))
    rw [norm_neg, norm_one, sub_neg_eq_add, add_comm] at this
    linarith
  linarith

/-- La muralla es positiva: 2 − π²/6 > 0. -/
theorem muralla_positiva : 0 < 2 - Real.pi ^ 2 / 6 := by
  have := Real.pi_lt_d2
  nlinarith [Real.pi_pos]

end RhG1Lean
