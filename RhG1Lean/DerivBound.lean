/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Basic.NNReal.Basic
import RhG1Lean.Lip

/-!
# H1 / H2 — compact leftoverLeftSlab + ∃C bound on ‖ξ'‖₊

No numeric L. No CERT_* axioms. No RH.
Slab is closed → enlarge to an open U ⊂ {s ≠ 1 ∧ 0 < (s/2).re}, then
DifferentiableOn → AnalyticOnNhd → ContinuousOn deriv → compact bound.
-/

open Complex Real Set
open scoped NNReal

namespace RhG1Lean

/-! ### H1: leftoverLeftSlab is compact (image of Icc × Icc, or empty) -/

/-- **H1.** Continuous image of `[1/2, 1-ε] × [-1/2, 1/2]`, hence compact.
When `1 - ε < 1/2` the product is empty and so is the slab. -/
theorem isCompact_leftoverLeftSlab (ε : ℝ) : IsCompact (leftoverLeftSlab ε) := by
  let f : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) + (p.2 : ℂ) * I
  have hf : Continuous f :=
    (continuous_ofReal.comp continuous_fst).add
      ((continuous_ofReal.comp continuous_snd).mul continuous_const)
  have hK :
      IsCompact (Icc ((2 : ℝ)⁻¹) (1 - ε) ×ˢ Icc (-(2 : ℝ)⁻¹) (2 : ℝ)⁻¹) :=
    (isCompact_Icc).prod isCompact_Icc
  have himg :
      f '' (Icc ((2 : ℝ)⁻¹) (1 - ε) ×ˢ Icc (-(2 : ℝ)⁻¹) (2 : ℝ)⁻¹) =
        leftoverLeftSlab ε := by
    ext s
    constructor
    · rintro ⟨⟨x, y⟩, hxy, rfl⟩
      simp [leftoverLeftSlab, f, abs_le]
      exact ⟨hxy.1.1, hxy.1.2, hxy.2.1, hxy.2.2⟩
    · intro hs
      refine ⟨(s.re, s.im), ?_, Complex.re_add_im s⟩
      simp [leftoverLeftSlab, abs_le] at hs
      exact ⟨⟨hs.1, hs.2.1⟩, ⟨hs.2.2.1, hs.2.2.2⟩⟩
  rw [← himg]
  exact hK.image hf

/-! ### Open fattening of the slab (for ContinuousOn of deriv) -/

/-- Open rectangle strictly containing `leftoverLeftSlab ε` when `δ > 0`. -/
def leftoverLeftSlabOpen (ε δ : ℝ) : Set ℂ :=
  {s | (2 : ℝ)⁻¹ - δ < s.re ∧ s.re < 1 - ε + δ ∧
    |s.im| < (2 : ℝ)⁻¹ + δ}

theorem isOpen_leftoverLeftSlabOpen (ε δ : ℝ) : IsOpen (leftoverLeftSlabOpen ε δ) := by
  have h₁ : IsOpen {s : ℂ | (2 : ℝ)⁻¹ - δ < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have h₂ : IsOpen {s : ℂ | s.re < 1 - ε + δ} :=
    isOpen_lt Complex.continuous_re continuous_const
  have h₃ : IsOpen {s : ℂ | |s.im| < (2 : ℝ)⁻¹ + δ} := by
    have ha : IsOpen {s : ℂ | -((2 : ℝ)⁻¹ + δ) < s.im} :=
      isOpen_lt continuous_const Complex.continuous_im
    have hb : IsOpen {s : ℂ | s.im < (2 : ℝ)⁻¹ + δ} :=
      isOpen_lt Complex.continuous_im continuous_const
    have : {s : ℂ | |s.im| < (2 : ℝ)⁻¹ + δ} =
        {s : ℂ | -((2 : ℝ)⁻¹ + δ) < s.im} ∩ {s : ℂ | s.im < (2 : ℝ)⁻¹ + δ} := by
      ext s; simp [abs_lt]
    rw [this]
    exact ha.inter hb
  have : leftoverLeftSlabOpen ε δ =
      {s : ℂ | (2 : ℝ)⁻¹ - δ < s.re} ∩ {s : ℂ | s.re < 1 - ε + δ} ∩
        {s : ℂ | |s.im| < (2 : ℝ)⁻¹ + δ} := by
    ext s; simp [leftoverLeftSlabOpen, and_assoc]
  rw [this]
  exact (h₁.inter h₂).inter h₃

theorem leftoverLeftSlab_subset_open {ε δ : ℝ} (hδ : 0 < δ) :
    leftoverLeftSlab ε ⊆ leftoverLeftSlabOpen ε δ := by
  intro s hs
  have h := hs
  -- hs gives 1/2 ≤ re ≤ 1-ε and |im| ≤ 1/2
  refine ⟨?_, ?_, ?_⟩
  · -- (2)⁻¹ - δ < re
    have : (2 : ℝ)⁻¹ ≤ s.re := by simpa [leftoverLeftSlab] using h.1
    linarith
  · -- re < 1 - ε + δ
    have : s.re ≤ 1 - ε := by simpa [leftoverLeftSlab] using h.2.1
    linarith
  · -- |im| < 1/2 + δ
    have : |s.im| ≤ (2 : ℝ)⁻¹ := by simpa [leftoverLeftSlab] using h.2.2
    linarith

/-- For `0 < ε` and `δ = ε/2`, the open fattening stays in `{s ≠ 1 ∧ 0 < (s/2).re}`. -/
theorem leftoverLeftSlabOpen_subset_xi_domain
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    leftoverLeftSlabOpen ε (ε / 2) ⊆
      {s : ℂ | s ≠ 1 ∧ 0 < (s / 2).re} := by
  intro s hs
  have hre₁ : (2 : ℝ)⁻¹ - ε / 2 < s.re := hs.1
  have hre₂ : s.re < 1 - ε + ε / 2 := hs.2.1
  have hre₂' : s.re < 1 - ε / 2 := by linarith
  have hre_pos : (0 : ℝ) < s.re := by
    -- 1/2 - ε/2 ≥ 1/2 - 1/4 = 1/4 > 0 when ε ≤ 1/2
    have : (2 : ℝ)⁻¹ - ε / 2 ≥ (2 : ℝ)⁻¹ - (1 / 2) / 2 := by
      have : ε / 2 ≤ (1 / 2) / 2 := by linarith
      linarith
    have : (2 : ℝ)⁻¹ - (1 / 2) / 2 = (4 : ℝ)⁻¹ := by norm_num
    nlinarith
  refine ⟨?_, ?_⟩
  · -- s ≠ 1 because re < 1
    intro h1
    have : s.re = 1 := by simp [h1]
    linarith
  · -- 0 < (s/2).re
    have : (s / 2).re = s.re / 2 := re_div_two s
    rw [this]
    linarith

theorem differentiableOn_riemannXi_leftoverLeftSlabOpen
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    DifferentiableOn ℂ riemannXi (leftoverLeftSlabOpen ε (ε / 2)) := by
  intro z hz
  have hz' := leftoverLeftSlabOpen_subset_xi_domain hε hε2 hz
  exact (differentiableAt_riemannXi_of hz'.1 hz'.2).differentiableWithinAt

theorem continuousOn_deriv_riemannXi_leftoverLeftSlabOpen
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ContinuousOn (deriv riemannXi) (leftoverLeftSlabOpen ε (ε / 2)) := by
  set U := leftoverLeftSlabOpen ε (ε / 2)
  have hUo : IsOpen U := isOpen_leftoverLeftSlabOpen ε (ε / 2)
  have hdiff : DifferentiableOn ℂ riemannXi U :=
    differentiableOn_riemannXi_leftoverLeftSlabOpen hε hε2
  -- Open in ℂ: DifferentiableOn → AnalyticOnNhd (CauchyIntegral)
  have hAnalNhd : AnalyticOnNhd ℂ riemannXi U := hdiff.analyticOnNhd hUo
  have hderiv : AnalyticOnNhd ℂ (deriv riemannXi) U :=
    hAnalNhd.deriv_of_isOpen hUo
  exact hderiv.continuousOn

/-! ### H2: ∃ C : NNReal bound on ‖ξ'‖₊ on the slab -/

/-- **H2.** Existence only — no numeric L, no m. -/
theorem exists_nnnorm_deriv_riemannXi_le_leftoverLeftSlab
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ∃ C : NNReal, ∀ z ∈ leftoverLeftSlab ε, ‖deriv riemannXi z‖₊ ≤ C := by
  set U := leftoverLeftSlabOpen ε (ε / 2)
  have hsub : leftoverLeftSlab ε ⊆ U :=
    leftoverLeftSlab_subset_open (ε := ε) (δ := ε / 2) (half_pos hε)
  have hcontU : ContinuousOn (deriv riemannXi) U :=
    continuousOn_deriv_riemannXi_leftoverLeftSlabOpen hε hε2
  have hcont : ContinuousOn (deriv riemannXi) (leftoverLeftSlab ε) :=
    hcontU.mono hsub
  obtain ⟨C0, hC0⟩ :=
    (isCompact_leftoverLeftSlab ε).exists_bound_of_continuousOn hcont
  refine ⟨Real.toNNReal C0, fun z hz => ?_⟩
  have hle : ‖deriv riemannXi z‖ ≤ C0 := hC0 z hz
  exact NNReal.coe_le_coe.mp <| by
    simpa [coe_nnnorm', Real.coe_toNNReal'] using hle.trans (le_max_left C0 0)


/-! ### H1/H2 for leftoverUpSlab and leftoverDnSlab -/

theorem isCompact_leftoverUpSlab (ε : ℝ) : IsCompact (leftoverUpSlab ε) := by
  let f : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) + (p.2 : ℂ) * I
  have hf : Continuous f :=
    (continuous_ofReal.comp continuous_fst).add
      ((continuous_ofReal.comp continuous_snd).mul continuous_const)
  have hK : IsCompact (Icc (1 - ε) 1 ×ˢ Icc ε ((2 : ℝ)⁻¹)) :=
    isCompact_Icc.prod isCompact_Icc
  have himg : f '' (Icc (1 - ε) 1 ×ˢ Icc ε ((2 : ℝ)⁻¹)) = leftoverUpSlab ε := by
    ext s
    constructor
    · rintro ⟨⟨x, y⟩, hxy, rfl⟩
      simp [leftoverUpSlab, f]
      exact ⟨by linarith [hxy.1.1], hxy.1.2, hxy.2.1, hxy.2.2⟩
    · intro hs
      refine ⟨(s.re, s.im), ?_, Complex.re_add_im s⟩
      simp [leftoverUpSlab] at hs
      exact ⟨⟨by linarith [hs.1], hs.2.1⟩, ⟨hs.2.2.1, hs.2.2.2⟩⟩
  rw [← himg]
  exact hK.image hf

def leftoverUpSlabOpen (ε δ : ℝ) : Set ℂ :=
  {s : ℂ | 1 - ε - δ < s.re ∧ s.re < 1 + δ ∧ ε - δ < s.im ∧ s.im < (2 : ℝ)⁻¹ + δ}

theorem isOpen_leftoverUpSlabOpen (ε δ : ℝ) : IsOpen (leftoverUpSlabOpen ε δ) := by
  have h₁ : IsOpen {s : ℂ | 1 - ε - δ < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have h₂ : IsOpen {s : ℂ | s.re < 1 + δ} :=
    isOpen_lt Complex.continuous_re continuous_const
  have h₃ : IsOpen {s : ℂ | ε - δ < s.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have h₄ : IsOpen {s : ℂ | s.im < (2 : ℝ)⁻¹ + δ} :=
    isOpen_lt Complex.continuous_im continuous_const
  have : leftoverUpSlabOpen ε δ =
      {s : ℂ | 1 - ε - δ < s.re} ∩ {s : ℂ | s.re < 1 + δ} ∩
        {s : ℂ | ε - δ < s.im} ∩ {s : ℂ | s.im < (2 : ℝ)⁻¹ + δ} := by
    ext s; simp [leftoverUpSlabOpen, and_assoc]
  rw [this]
  exact ((h₁.inter h₂).inter h₃).inter h₄

theorem leftoverUpSlab_subset_open {ε δ : ℝ} (hδ : 0 < δ) :
    leftoverUpSlab ε ⊆ leftoverUpSlabOpen ε δ := by
  intro s hs
  refine ⟨by linarith [hs.1], by linarith [hs.2.1], by linarith [hs.2.2.1], by linarith [hs.2.2.2]⟩

theorem leftoverUpSlabOpen_subset_xi_domain
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    leftoverUpSlabOpen ε (ε / 2) ⊆ {s : ℂ | s ≠ 1 ∧ 0 < (s / 2).re} := by
  intro s hs
  refine ⟨?_, ?_⟩
  · intro h1
    have : (1 : ℂ).im > ε - ε / 2 := by
      have : (1 : ℂ) ∈ leftoverUpSlabOpen ε (ε / 2) := by simpa [h1] using hs
      exact this.2.2.1
    have : (1 : ℂ).im = 0 := rfl
    linarith
  · have : (s / 2).re = s.re / 2 := re_div_two s
    rw [this]
    have : s.re > 1 - ε - ε / 2 := hs.1
    have : 1 - ε - ε / 2 ≥ 1 - (1/2) - (1/4) := by linarith
    linarith

theorem differentiableOn_riemannXi_leftoverUpSlabOpen
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    DifferentiableOn ℂ riemannXi (leftoverUpSlabOpen ε (ε / 2)) := by
  intro z hz
  have hz' := leftoverUpSlabOpen_subset_xi_domain hε hε2 hz
  exact (differentiableAt_riemannXi_of hz'.1 hz'.2).differentiableWithinAt

theorem continuousOn_deriv_riemannXi_leftoverUpSlabOpen
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ContinuousOn (deriv riemannXi) (leftoverUpSlabOpen ε (ε / 2)) := by
  set U := leftoverUpSlabOpen ε (ε / 2)
  have hUo : IsOpen U := isOpen_leftoverUpSlabOpen ε (ε / 2)
  have hdiff : DifferentiableOn ℂ riemannXi U :=
    differentiableOn_riemannXi_leftoverUpSlabOpen hε hε2
  have hAnalNhd : AnalyticOnNhd ℂ riemannXi U := hdiff.analyticOnNhd hUo
  have hderiv : AnalyticOnNhd ℂ (deriv riemannXi) U :=
    hAnalNhd.deriv_of_isOpen hUo
  exact hderiv.continuousOn

theorem exists_nnnorm_deriv_riemannXi_le_leftoverUpSlab
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ∃ C : NNReal, ∀ z ∈ leftoverUpSlab ε, ‖deriv riemannXi z‖₊ ≤ C := by
  set U := leftoverUpSlabOpen ε (ε / 2)
  have hsub : leftoverUpSlab ε ⊆ U :=
    leftoverUpSlab_subset_open (ε := ε) (δ := ε / 2) (half_pos hε)
  have hcontU : ContinuousOn (deriv riemannXi) U :=
    continuousOn_deriv_riemannXi_leftoverUpSlabOpen hε hε2
  have hcont : ContinuousOn (deriv riemannXi) (leftoverUpSlab ε) :=
    hcontU.mono hsub
  obtain ⟨C0, hC0⟩ :=
    (isCompact_leftoverUpSlab ε).exists_bound_of_continuousOn hcont
  refine ⟨Real.toNNReal C0, fun z hz => ?_⟩
  have hle : ‖deriv riemannXi z‖ ≤ C0 := hC0 z hz
  exact NNReal.coe_le_coe.mp <| by
    simpa [coe_nnnorm', Real.coe_toNNReal'] using hle.trans (le_max_left C0 0)

theorem isCompact_leftoverDnSlab (ε : ℝ) : IsCompact (leftoverDnSlab ε) := by
  let f : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) + (p.2 : ℂ) * I
  have hf : Continuous f :=
    (continuous_ofReal.comp continuous_fst).add
      ((continuous_ofReal.comp continuous_snd).mul continuous_const)
  have hK : IsCompact (Icc (1 - ε) 1 ×ˢ Icc (-(2 : ℝ)⁻¹) (-ε)) :=
    isCompact_Icc.prod isCompact_Icc
  have himg : f '' (Icc (1 - ε) 1 ×ˢ Icc (-(2 : ℝ)⁻¹) (-ε)) = leftoverDnSlab ε := by
    ext s
    constructor
    · rintro ⟨⟨x, y⟩, hxy, rfl⟩
      simp [leftoverDnSlab, f]
      exact ⟨by linarith [hxy.1.1], hxy.1.2, hxy.2.1, hxy.2.2⟩
    · intro hs
      refine ⟨(s.re, s.im), ?_, Complex.re_add_im s⟩
      simp [leftoverDnSlab] at hs
      exact ⟨⟨by linarith [hs.1], hs.2.1⟩, ⟨hs.2.2.1, hs.2.2.2⟩⟩
  rw [← himg]
  exact hK.image hf

def leftoverDnSlabOpen (ε δ : ℝ) : Set ℂ :=
  {s : ℂ | 1 - ε - δ < s.re ∧ s.re < 1 + δ ∧ -(2 : ℝ)⁻¹ - δ < s.im ∧ s.im < -ε + δ}

theorem isOpen_leftoverDnSlabOpen (ε δ : ℝ) : IsOpen (leftoverDnSlabOpen ε δ) := by
  have h₁ : IsOpen {s : ℂ | 1 - ε - δ < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have h₂ : IsOpen {s : ℂ | s.re < 1 + δ} :=
    isOpen_lt Complex.continuous_re continuous_const
  have h₃ : IsOpen {s : ℂ | -(2 : ℝ)⁻¹ - δ < s.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have h₄ : IsOpen {s : ℂ | s.im < -ε + δ} :=
    isOpen_lt Complex.continuous_im continuous_const
  have : leftoverDnSlabOpen ε δ =
      {s : ℂ | 1 - ε - δ < s.re} ∩ {s : ℂ | s.re < 1 + δ} ∩
        {s : ℂ | -(2 : ℝ)⁻¹ - δ < s.im} ∩ {s : ℂ | s.im < -ε + δ} := by
    ext s; simp [leftoverDnSlabOpen, and_assoc]
  rw [this]
  exact ((h₁.inter h₂).inter h₃).inter h₄

theorem leftoverDnSlab_subset_open {ε δ : ℝ} (hδ : 0 < δ) :
    leftoverDnSlab ε ⊆ leftoverDnSlabOpen ε δ := by
  intro s hs
  refine ⟨by linarith [hs.1], by linarith [hs.2.1], by linarith [hs.2.2.1], by linarith [hs.2.2.2]⟩

theorem leftoverDnSlabOpen_subset_xi_domain
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    leftoverDnSlabOpen ε (ε / 2) ⊆ {s : ℂ | s ≠ 1 ∧ 0 < (s / 2).re} := by
  intro s hs
  refine ⟨?_, ?_⟩
  · intro h1
    have : (1 : ℂ).im < -ε + ε / 2 := by
      have : (1 : ℂ) ∈ leftoverDnSlabOpen ε (ε / 2) := by simpa [h1] using hs
      exact this.2.2.2
    have : (1 : ℂ).im = 0 := rfl
    linarith
  · have : (s / 2).re = s.re / 2 := re_div_two s
    rw [this]
    have : s.re > 1 - ε - ε / 2 := hs.1
    have : 1 - ε - ε / 2 ≥ 1 - (1/2) - (1/4) := by linarith
    linarith

theorem differentiableOn_riemannXi_leftoverDnSlabOpen
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    DifferentiableOn ℂ riemannXi (leftoverDnSlabOpen ε (ε / 2)) := by
  intro z hz
  have hz' := leftoverDnSlabOpen_subset_xi_domain hε hε2 hz
  exact (differentiableAt_riemannXi_of hz'.1 hz'.2).differentiableWithinAt

theorem continuousOn_deriv_riemannXi_leftoverDnSlabOpen
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ContinuousOn (deriv riemannXi) (leftoverDnSlabOpen ε (ε / 2)) := by
  set U := leftoverDnSlabOpen ε (ε / 2)
  have hUo : IsOpen U := isOpen_leftoverDnSlabOpen ε (ε / 2)
  have hdiff : DifferentiableOn ℂ riemannXi U :=
    differentiableOn_riemannXi_leftoverDnSlabOpen hε hε2
  have hAnalNhd : AnalyticOnNhd ℂ riemannXi U := hdiff.analyticOnNhd hUo
  have hderiv : AnalyticOnNhd ℂ (deriv riemannXi) U :=
    hAnalNhd.deriv_of_isOpen hUo
  exact hderiv.continuousOn

theorem exists_nnnorm_deriv_riemannXi_le_leftoverDnSlab
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ∃ C : NNReal, ∀ z ∈ leftoverDnSlab ε, ‖deriv riemannXi z‖₊ ≤ C := by
  set U := leftoverDnSlabOpen ε (ε / 2)
  have hsub : leftoverDnSlab ε ⊆ U :=
    leftoverDnSlab_subset_open (ε := ε) (δ := ε / 2) (half_pos hε)
  have hcontU : ContinuousOn (deriv riemannXi) U :=
    continuousOn_deriv_riemannXi_leftoverDnSlabOpen hε hε2
  have hcont : ContinuousOn (deriv riemannXi) (leftoverDnSlab ε) :=
    hcontU.mono hsub
  obtain ⟨C0, hC0⟩ :=
    (isCompact_leftoverDnSlab ε).exists_bound_of_continuousOn hcont
  refine ⟨Real.toNNReal C0, fun z hz => ?_⟩
  have hle : ‖deriv riemannXi z‖ ≤ C0 := hC0 z hz
  exact NNReal.coe_le_coe.mp <| by
    simpa [coe_nnnorm', Real.coe_toNNReal'] using hle.trans (le_max_left C0 0)

end RhG1Lean
