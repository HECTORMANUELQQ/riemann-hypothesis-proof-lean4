/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.

# Mosaicos, círculos de Ford y la geometría de las bahías

* **Círculos de Ford** (Farey): el círculo de p/q tiene centro (p/q, 1/(2q²)) y radio 1/(2q²), y toca la recta.
  La distancia al cuadrado entre centros menos el cuadrado de la suma de radios es ((ps − qr)² − 1)/(q²s²):
  nunca se enciman (|ps − qr| ≥ 1 para fracciones distintas) y se tocan exactamente los vecinos de Farey.
* **Bahía y pared** (curvatura hiperbólica k = d/r): un disco de radio r con centro a distancia d > 0 de la pared
  la alcanza si y solo si d ≤ r; con r² = d/c eso es d·c ≤ 1. Los extremos del retroceso, a altura ±h con
  h² + d² = r², están en el círculo. La lente de la bahía con su reflejo tiene cos φ = 1 − 2dc.
* **Dos círculos tangentes entre sí y a una recta** (Descartes con curvatura 0): sus puntos de apoyo distan 2√(r₁r₂).
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace RhG1Lean

/-- **Distancia entre círculos de Ford.** -/
theorem ford_distancia (p q r s : ℝ) (hq : q ≠ 0) (hs : s ≠ 0) :
    (p / q - r / s) ^ 2 + (1 / (2 * q ^ 2) - 1 / (2 * s ^ 2)) ^ 2 - (1 / (2 * q ^ 2) + 1 / (2 * s ^ 2)) ^ 2
      = ((p * s - q * r) ^ 2 - 1) / (q ^ 2 * s ^ 2) := by
  field_simp
  ring

/-- Dos círculos de Ford se tocan exactamente cuando las fracciones son vecinas de Farey (|ps − qr| = 1). -/
theorem ford_tangentes_iff (p q r s : ℝ) (hq : q ≠ 0) (hs : s ≠ 0) :
    (p / q - r / s) ^ 2 + (1 / (2 * q ^ 2) - 1 / (2 * s ^ 2)) ^ 2 = (1 / (2 * q ^ 2) + 1 / (2 * s ^ 2)) ^ 2
      ↔ (p * s - q * r) ^ 2 = 1 := by
  have h := ford_distancia p q r s hq hs
  have hpos : 0 < q ^ 2 * s ^ 2 := by positivity
  constructor
  · intro he
    have h0 : ((p * s - q * r) ^ 2 - 1) / (q ^ 2 * s ^ 2) = 0 := by linarith
    rcases div_eq_zero_iff.mp h0 with h1 | h1
    · linarith
    · exact absurd h1 hpos.ne'
  · intro he
    rw [he, sub_self, zero_div] at h
    linarith

/-- Los círculos de Ford de dos fracciones distintas (|ps − qr| ≥ 1) nunca se enciman. -/
theorem ford_no_se_enciman (p q r s : ℝ) (hq : q ≠ 0) (hs : s ≠ 0) (h1 : 1 ≤ (p * s - q * r) ^ 2) :
    (1 / (2 * q ^ 2) + 1 / (2 * s ^ 2)) ^ 2 ≤ (p / q - r / s) ^ 2 + (1 / (2 * q ^ 2) - 1 / (2 * s ^ 2)) ^ 2 := by
  have h := ford_distancia p q r s hq hs
  have hpos : 0 < q ^ 2 * s ^ 2 := by positivity
  have : 0 ≤ ((p * s - q * r) ^ 2 - 1) / (q ^ 2 * s ^ 2) := div_nonneg (by linarith) hpos.le
  linarith

/-- **La bahía toca la pared ⇔ curvatura hiperbólica ≤ 1**: con r² = d/c (d, c > 0), d ≤ r ⇔ d·c ≤ 1. -/
theorem bahia_toca_pared_iff {d c : ℝ} (hd : 0 < d) (hc : 0 < c) :
    d ≤ Real.sqrt (d / c) ↔ d * c ≤ 1 := by
  rw [Real.le_sqrt hd.le (by positivity), le_div_iff₀ hc]
  constructor <;> intro h <;> nlinarith

/-- Un disco de radio r con centro a distancia d de la pared la alcanza (hay un punto con x = 0 a distancia ≤ r)
si y solo si d ≤ r. -/
theorem disco_alcanza_pared_iff {d r : ℝ} (_hd : 0 ≤ d) :
    (∃ y : ℝ, d ^ 2 + y ^ 2 ≤ r ^ 2) ↔ d ^ 2 ≤ r ^ 2 := by
  constructor
  · rintro ⟨y, hy⟩; nlinarith [sq_nonneg y]
  · intro h; exact ⟨0, by simpa using h⟩

/-- Los extremos del retroceso (0, ±h) están en el círculo de la bahía cuando h² + d² = r². -/
theorem extremos_retroceso {d h r : ℝ} (hr : h ^ 2 + d ^ 2 = r ^ 2) :
    (0 - d) ^ 2 + (h - 0) ^ 2 = r ^ 2 ∧ (0 - d) ^ 2 + (-h - 0) ^ 2 = r ^ 2 := by
  constructor <;> nlinarith

/-- **El ángulo de la lente**: dos círculos de radio r con centros a ±d (la bahía y su reflejo) se cortan con
cos φ = 1 − 2d²/r² (ley de cosenos), es decir 1 − 2dc cuando r² = d/c. -/
theorem angulo_lente {d c r cosφ : ℝ} (hd : 0 < d) (hc : 0 < c) (hr : r ^ 2 = d / c)
    (hcos : (2 * d) ^ 2 = r ^ 2 + r ^ 2 - 2 * r ^ 2 * cosφ) : cosφ = 1 - 2 * d * c := by
  have hr0 : r ^ 2 ≠ 0 := by rw [hr]; positivity
  have h2 : r ^ 2 * cosφ = r ^ 2 - 2 * d ^ 2 := by nlinarith [hcos]
  have h3 : cosφ = (r ^ 2 - 2 * d ^ 2) / r ^ 2 := by rw [eq_div_iff hr0]; linarith
  rw [h3, hr]
  field_simp

/-- **Descartes con una recta**: dos círculos de radios r₁, r₂ tangentes entre sí y a la recta tienen sus puntos
de apoyo a distancia x con x² = 4 r₁ r₂. -/
theorem apoyos_tangentes {r₁ r₂ x : ℝ} (h : x ^ 2 + (r₁ - r₂) ^ 2 = (r₁ + r₂) ^ 2) : x ^ 2 = 4 * r₁ * r₂ := by
  nlinarith

end RhG1Lean
