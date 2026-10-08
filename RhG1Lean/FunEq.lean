/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under CC-BY 4.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import RhG1Lean.Leftover
import RhG1Lean.Majorant
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-!
# Ecuación funcional y la caja chica

Mapa AX-C10 / mathlib: `completedRiemannZeta₀ (1-s) = completedRiemannZeta₀ s`.

w = s − 1/2 = δ + i t  se va a  −w  al hacer s ↦ 1−s.
Luego stripO1Small (δ,t) ↔ stripO1Small (−δ,−t): **un lado basta**.

No se usa Pick aquí. La monografía ya dio las γ altas; FE es el pliegue
del mapa, ya en mathlib.
-/

open Complex Real

namespace RhG1Lean

theorem stripO1Small_neg (δ t : ℝ) :
    stripO1Small δ t ↔ stripO1Small (-δ) (-t) := by
  unfold stripO1Small
  simp [abs_neg]

/-- s = 1/2 + δ + i t  ⇒  1−s = 1/2 − δ − i t. -/
theorem one_sub_half_delta (δ t : ℝ) :
    1 - ((1 : ℂ) / 2 + δ + I * t) = (1 : ℂ) / 2 + (-δ : ℝ) + I * (-t : ℝ) := by
  simp
  ring

/-- Mathlib: Λ₀(1−s)=Λ₀(s). Ceros de Λ₀ simétricos. -/
theorem completedRiemannZeta₀_symmetric (s : ℂ) :
    completedRiemannZeta₀ (1 - s) = completedRiemannZeta₀ s :=
  completedRiemannZeta₀_one_sub s

/-- En la caja, s ≠ 1 (Re s = 1/2+δ ≤ 1, y =1 solo si δ=1/2 y t=0). -/
theorem stripO1Small_ne_one {δ t : ℝ} (_h : stripO1Small δ t)
    (ht : t ≠ 0 ∨ δ ≠ 1 / 2) :
    ((1 : ℂ) / 2 + δ + I * t) ≠ 1 := by
  intro hs
  have hr : ((1 : ℂ) / 2 + δ + I * t).re = 1 := by rw [hs]; simp
  have hi : ((1 : ℂ) / 2 + δ + I * t).im = 0 := by rw [hs]; simp
  have hre : (1 : ℝ) / 2 + δ = 1 := by
    simpa using hr
  have him : t = 0 := by
    simpa using hi
  have hδ : δ = 1 / 2 := by linarith
  rcases ht with ht | hδ'
  · exact ht him
  · exact hδ' hδ

/-! ### N1 / J4 board: ξ ↔ Λ and ξ(1 − s) = ξ(s) (identity; not N=0) -/

/-- Away from `s = 0` with `Gammaℝ s ≠ 0`: map ξ = classical prefactor times completed Λ. -/
theorem riemannXi_eq_mul_completedRiemannZeta {s : ℂ} (hs : s ≠ 0)
    (hG : Gammaℝ s ≠ 0) :
    riemannXi s = (s * (s - 1) / 2) * completedRiemannZeta s := by
  unfold riemannXi
  have hΓ : (π : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) = Gammaℝ s :=
    (Gammaℝ_def s).symm
  have hz := riemannZeta_def_of_ne_zero hs
  calc
    s * (s - 1) / 2 * (π : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) * riemannZeta s
        = s * (s - 1) / 2 * ((π : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)) *
            riemannZeta s := by
          ring
    _ = s * (s - 1) / 2 * Gammaℝ s * riemannZeta s := by
          rw [hΓ]
    _ = s * (s - 1) / 2 * Gammaℝ s * (completedRiemannZeta s / Gammaℝ s) := by
          rw [hz]
    _ = s * (s - 1) / 2 * completedRiemannZeta s := by
          field

/-- Prefactor invariant under `s ↦ 1 - s`. -/
theorem prefactor_xi_one_sub (s : ℂ) :
    ((1 - s) * ((1 - s) - 1) / 2) = s * (s - 1) / 2 := by
  ring

/-- **N1 / J4.** `ξ(1 - s) = ξ(s)` when both sides are related to Λ
(`s ≠ 0,1` and `Gammaℝ` non-vanishing at `s` and `1-s`). Does not claim N=0. -/
theorem riemannXi_one_sub {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hG : Gammaℝ s ≠ 0) (hG' : Gammaℝ (1 - s) ≠ 0) :
    riemannXi (1 - s) = riemannXi s := by
  have h10 : (1 - s) ≠ 0 := by
    intro h
    exact hs1 (sub_eq_zero.mp h).symm
  rw [riemannXi_eq_mul_completedRiemannZeta h10 hG',
      riemannXi_eq_mul_completedRiemannZeta hs0 hG, prefactor_xi_one_sub,
      completedRiemannZeta_one_sub]

/-- Module symmetry of `‖ξ‖` (mapa N1-B). -/
theorem norm_riemannXi_one_sub {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hG : Gammaℝ s ≠ 0) (hG' : Gammaℝ (1 - s) ≠ 0) :
    ‖riemannXi (1 - s)‖ = ‖riemannXi s‖ := by
  rw [riemannXi_one_sub hs0 hs1 hG hG']


end RhG1Lean
