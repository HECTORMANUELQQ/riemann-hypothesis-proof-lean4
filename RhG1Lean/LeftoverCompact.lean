/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under CC-BY 4.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Complex.Basic
import RhG1Lean.Leftover
import RhG1Lean.G5Interior
import RhG1Lean.G5
import RhG1Lean.GammaBound

/-!
# La caja |t|≤1/2 es compacta ⇒ finitos ceros de ζ

No es N=0. Es: no puede haber infinitos ceros en leftoverRect.
G5Interior ya tenía finitos en cualquier compacto; aquí el compacto es
la caja de O₁.

Rosas/Pick: sus γ≥14 no están en esta caja (ya Leftover).
-/

open Complex Real Set

namespace RhG1Lean

/-- Rectángulo que contiene leftoverHard: 1/2 ≤ Re s ≤ 1, |Im s| ≤ 1/2. -/
def leftoverRect : Set ℂ :=
  {s | (2 : ℝ)⁻¹ ≤ s.re ∧ s.re ≤ 1 ∧ |s.im| ≤ (2 : ℝ)⁻¹}

theorem leftoverHard_mem_rect {w : ℂ} (h : leftoverHard w) :
    (1 / 2 + w : ℂ) ∈ leftoverRect := by
  refine ⟨?_, ?_, ?_⟩
  · have : (1 / 2 + w : ℂ).re = 1 / 2 + w.re := by simp
    rw [this]
    linarith [le_trans (abs_nonneg w.im) h.1]
  · have : (1 / 2 + w : ℂ).re = 1 / 2 + w.re := by simp
    rw [this]
    linarith [h.2]
  · have : (1 / 2 + w : ℂ).im = w.im := by simp
    rw [this]
    have : (1 : ℝ) / 2 = (2 : ℝ)⁻¹ := by norm_num
    rw [← this]
    exact leftoverHard_im_le_half h

/-- El rectángulo es imagen continua de [1/2,1] × [-1/2,1/2], luego compacto. -/
theorem isCompact_leftoverRect : IsCompact leftoverRect := by
  let f : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) + (p.2 : ℂ) * I
  have hf : Continuous f :=
    (continuous_ofReal.comp continuous_fst).add
      ((continuous_ofReal.comp continuous_snd).mul continuous_const)
  have hK : IsCompact (Icc ((2 : ℝ)⁻¹) 1 ×ˢ Icc (-(2 : ℝ)⁻¹) (2 : ℝ)⁻¹) :=
    (isCompact_Icc).prod isCompact_Icc
  have himg : f '' (Icc ((2 : ℝ)⁻¹) 1 ×ˢ Icc (-(2 : ℝ)⁻¹) (2 : ℝ)⁻¹) = leftoverRect := by
    ext s
    constructor
    · rintro ⟨⟨x, y⟩, hxy, rfl⟩
      have hx := hxy.1
      have hy := hxy.2
      simp [leftoverRect, f]
      exact ⟨hx.1, hx.2, abs_le.mpr hy⟩
    · intro hs
      refine ⟨(s.re, s.im), ⟨⟨hs.1, hs.2.1⟩, abs_le.mp hs.2.2⟩, Complex.re_add_im s⟩
  rw [← himg]
  exact hK.image hf

/-- **G5 en la caja:** finitos ceros de ζ en leftoverRect. No es N=0. -/
theorem finite_zeta_zeros_leftoverRect :
    (leftoverRect ∩ riemannZetaZeros).Finite :=
  isCompact_leftoverRect.inter_riemannZetaZeros_finite

/-- Boca A en la franja: |δ| < |t| (Re u < 0), 0 < σ < 1. -/
def stripA (s : ℂ) : Prop :=
  0 < s.re ∧ s.re < 1 ∧ |s.re - 1 / 2| < |s.im|

theorem stripA_of_bocaA_in_strip {δ t : ℝ}
    (hσ0 : 0 < (1 : ℝ) / 2 + δ) (hσ1 : (1 : ℝ) / 2 + δ < 1)
    (hA : |δ| < |t|) :
    stripA ((1 : ℂ) / 2 + δ + I * t) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using hσ0
  · simpa using hσ1
  · have : |((1 : ℂ) / 2 + δ + I * t).re - 1 / 2| = |δ| := by
      simp
    have : |((1 : ℂ) / 2 + δ + I * t).im| = |t| := by
      simp
    simpa [this] using hA

/-- En leftoverRect, Re(s/2) > 0. -/
theorem leftoverRect_re_half_pos {s : ℂ} (hs : s ∈ leftoverRect) :
    0 < (s / 2).re := by
  have hre : (2 : ℝ)⁻¹ ≤ s.re := hs.1
  have : (s / 2).re = s.re / 2 := re_div_two s
  rw [this]
  have : (0 : ℝ) < (2 : ℝ)⁻¹ / 2 := by norm_num
  linarith

/-- Plan caja: ξ holomorfa en leftoverRect salvo el polo s=1. -/
theorem differentiableAt_riemannXi_leftoverRect {s : ℂ}
    (hs : s ∈ leftoverRect) (h1 : s ≠ 1) :
    DifferentiableAt ℂ riemannXi s :=
  differentiableAt_riemannXi_of h1 (leftoverRect_re_half_pos hs)

/-- Banda de A: franja 0≤σ≤1, altura entre T y H. Compacta. -/
def aBand (T H : ℝ) : Set ℂ :=
  {s | 0 ≤ s.re ∧ s.re ≤ 1 ∧ T ≤ s.im ∧ s.im ≤ H}

theorem isCompact_aBand (T H : ℝ) : IsCompact (aBand T H) := by
  let f : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) + (p.2 : ℂ) * I
  have hf : Continuous f :=
    (continuous_ofReal.comp continuous_fst).add
      ((continuous_ofReal.comp continuous_snd).mul continuous_const)
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc T H) :=
    (isCompact_Icc).prod isCompact_Icc
  have himg : f '' (Icc (0 : ℝ) 1 ×ˢ Icc T H) = aBand T H := by
    ext s
    constructor
    · rintro ⟨⟨x, y⟩, hxy, rfl⟩
      have hx := hxy.1
      have hy := hxy.2
      simp [aBand, f]
      exact ⟨hx.1, hx.2, hy.1, hy.2⟩
    · intro hs
      refine ⟨(s.re, s.im), ⟨⟨hs.1, hs.2.1⟩, ⟨hs.2.2.1, hs.2.2.2⟩⟩, Complex.re_add_im s⟩
  rw [← himg]
  exact hK.image hf

/-- Plan A: en cada banda de altura [T,H], finitos ceros de ζ. No es T→∞. -/
theorem finite_zeta_zeros_aBand (T H : ℝ) :
    (aBand T H ∩ riemannZetaZeros).Finite :=
  (isCompact_aBand T H).inter_riemannZetaZeros_finite

end RhG1Lean
