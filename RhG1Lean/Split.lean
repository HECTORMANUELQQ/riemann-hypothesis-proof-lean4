/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under CC-BY 4.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.NumberTheory.LSeries.Nonvanishing
import RhG1Lean.Leftover
import RhG1Lean.LeftoverCompact
import RhG1Lean.MouthA

/-!
# Partición de la franja (el plan, en Lean)

En 0 < σ < 1 se tiene |δ| < 1/2. Entonces, comparando |t| y |δ|:

* |t| < |δ|  →  stripO1Small (cajita; Re u > 0)
* |t| = |δ|  →  Re u = 0 (diámetro en el plano u)
* |t| > |δ|  →  Re u < 0 (boca A)

No hay una cuarta habitación. RH es: δ=0, o vaciar las otras dos.

Borde derecho de leftoverRect (Re s = 1, s ≠ 1): ζ ≠ 0 (mathlib).
El interior Re s < 1 de la cajita sigue OPEN.
A por bandas: finitos; uniforme en T sigue OPEN.
-/

open Complex Real

namespace RhG1Lean

/-- Re u = 0 ⇔ |t| = |δ|. -/
theorem re_u_eq_zero_iff (δ t : ℝ) :
    (((δ : ℂ) + I * t) ^ 2).re = 0 ↔ |t| = |δ| := by
  rw [re_w_sq, ← sq δ, ← sq t, ← sq_abs δ, ← sq_abs t]
  constructor
  · intro h
    have : |t| ^ 2 = |δ| ^ 2 := by linarith
    exact (sq_eq_sq₀ (abs_nonneg t) (abs_nonneg δ)).mp this
  · intro h
    simp [h]

theorem re_u_pos_iff (δ t : ℝ) :
    0 < (((δ : ℂ) + I * t) ^ 2).re ↔ |t| < |δ| := by
  rw [re_w_sq, ← sq δ, ← sq t]
  constructor
  · intro h
    have : t ^ 2 < δ ^ 2 := by nlinarith
    exact sq_lt_sq.mp this
  · intro h
    have : |t| ^ 2 < |δ| ^ 2 :=
      pow_lt_pow_left₀ h (abs_nonneg t) (by norm_num : (2 : ℕ) ≠ 0)
    rw [sq_abs, sq_abs] at this
    nlinarith

/-- **Partición.** En la franja |δ| ≤ 1/2, el punto está en
    O₁-chica, o en el diámetro Re u=0, o en A. -/
theorem strip_trichotomy {δ t : ℝ} (hδ : |δ| ≤ 1 / 2) :
    stripO1Small δ t ∨
      (((δ : ℂ) + I * t) ^ 2).re = 0 ∨
      0 < |t| - |δ| := by
  rcases lt_trichotomy |t| |δ| with h | h | h
  · exact Or.inl ⟨h, hδ⟩
  · exact Or.inr (Or.inl ((re_u_eq_zero_iff δ t).mpr h))
  · exact Or.inr (Or.inr (sub_pos.mpr h))

/-- El tercer caso es boca A (Re u < 0). -/
theorem trichotomy_third_is_A {δ t : ℝ} (h : |δ| < |t|) :
    (((δ : ℂ) + I * t) ^ 2).re < 0 :=
  bocaA_re_neg h

/-- Borde derecho de la caja: Re s = 1, s ≠ 1 ⇒ ζ ≠ 0. -/
theorem leftoverRect_right_edge_zeta_ne_zero {s : ℂ}
    (_hs : s ∈ leftoverRect) (hre : 1 ≤ s.re) :
    riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hre

end RhG1Lean
