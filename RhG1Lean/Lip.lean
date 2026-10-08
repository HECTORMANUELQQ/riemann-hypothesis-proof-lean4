/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under CC-BY 4.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Convex
import Mathlib.Basic.NNReal.Basic
import RhG1Lean.LeftoverCore
import RhG1Lean.Majorant
import RhG1Lean.G5

/-!
# G — Lipschitz skeleton for ξ on convex sets (board for covering attack)

Uses mathlib Convex.lipschitzOnWith_of_nnnorm_deriv_le
(Mathlib.Analysis.Calculus.MeanValue).

Does **not** supply a numerical bound on ‖deriv ξ‖, nor m>0 on the core.
leftoverRect \\ ball(1,ε) is not convex; cover with convex pieces (left slab, …).
-/

open Complex Metric Set
open scoped NNReal

namespace RhG1Lean

/-- **G.** If ‖deriv ξ‖₊ ≤ C on a convex set U where ξ is differentiable,
then ξ is C-Lipschitz on U. -/
theorem riemannXi_lipschitz_on_convex
    {U : Set ℂ} (hU : Convex ℝ U)
    (hdiff : ∀ z ∈ U, DifferentiableAt ℂ riemannXi z)
    {C : NNReal} (hC : ∀ z ∈ U, ‖deriv riemannXi z‖₊ ≤ C) :
    LipschitzOnWith C riemannXi U :=
  hU.lipschitzOnWith_of_nnnorm_deriv_le hdiff hC

/-- The leftover box is an intersection of closed half-spaces, hence convex. -/
theorem convex_leftoverRect : Convex ℝ leftoverRect := by
  have : leftoverRect =
      {c : ℂ | (2 : ℝ)⁻¹ ≤ c.re} ∩ {c : ℂ | c.re ≤ 1} ∩
        {c : ℂ | -(2 : ℝ)⁻¹ ≤ c.im} ∩ {c : ℂ | c.im ≤ (2 : ℝ)⁻¹} := by
    ext s
    simp [leftoverRect, abs_le, and_assoc]
  rw [this]
  exact (((convex_halfSpace_re_ge _).inter (convex_halfSpace_re_le _)).inter
    (convex_halfSpace_im_ge _)).inter (convex_halfSpace_im_le _)

/-- Left slab: Re ≤ 1−ε inside the box. Convex piece of the core cut. -/
def leftoverLeftSlab (ε : ℝ) : Set ℂ :=
  {s : ℂ | (2 : ℝ)⁻¹ ≤ s.re ∧ s.re ≤ 1 - ε ∧ |s.im| ≤ (2 : ℝ)⁻¹}

theorem convex_leftoverLeftSlab (ε : ℝ) : Convex ℝ (leftoverLeftSlab ε) := by
  have : leftoverLeftSlab ε =
      {c : ℂ | (2 : ℝ)⁻¹ ≤ c.re} ∩ {c : ℂ | c.re ≤ 1 - ε} ∩
        {c : ℂ | -(2 : ℝ)⁻¹ ≤ c.im} ∩ {c : ℂ | c.im ≤ (2 : ℝ)⁻¹} := by
    ext s
    simp [leftoverLeftSlab, abs_le, and_assoc]
  rw [this]
  exact (((convex_halfSpace_re_ge _).inter (convex_halfSpace_re_le _)).inter
    (convex_halfSpace_im_ge _)).inter (convex_halfSpace_im_le _)

theorem leftoverLeftSlab_subset_leftoverRect {ε : ℝ} (hε : 0 ≤ ε) :
    leftoverLeftSlab ε ⊆ leftoverRect := by
  intro s hs
  refine ⟨hs.1, ?_, hs.2.2⟩
  have : s.re ≤ 1 - ε := hs.2.1
  linarith

/-- If ε > 0, the left slab misses all(1,ε): dist to 1 is at least ε. -/
theorem leftoverLeftSlab_subset_sdiff_ball {ε : ℝ} (hε : 0 < ε) :
    leftoverLeftSlab ε ⊆ leftoverRect \ ball (1 : ℂ) ε := by
  intro s hs
  refine ⟨leftoverLeftSlab_subset_leftoverRect hε.le hs, ?_⟩
  intro hb
  have hdist : dist s (1 : ℂ) < ε := hb
  have hnorm : ‖s - (1 : ℂ)‖ < ε := by simpa [dist_eq_norm] using hdist
  have habs : |s.re - 1| ≤ ‖s - (1 : ℂ)‖ := abs_re_le_norm (s - 1)
  have hlt : |s.re - 1| < ε := lt_of_le_of_lt habs hnorm
  have hre : s.re ≤ 1 - ε := hs.2.1
  have habs' : |s.re - 1| = 1 - s.re := by
    rw [abs_sub_comm, abs_of_nonneg]
    linarith
  linarith

/-- Differentiability of ξ on the left slab (s=1 is outside when ε>0). -/
theorem differentiableAt_riemannXi_leftoverLeftSlab {ε : ℝ} (hε : 0 < ε)
    {s : ℂ} (hs : s ∈ leftoverLeftSlab ε) :
    DifferentiableAt ℂ riemannXi s := by
  have hR := leftoverLeftSlab_subset_leftoverRect hε.le hs
  have h1 : s ≠ 1 := by
    intro heq
    have : (1 : ℂ) ∈ leftoverLeftSlab ε := by simpa [heq] using hs
    have : (1 : ℝ) ≤ 1 - ε := this.2.1
    linarith
  exact differentiableAt_riemannXi_leftoverRect hR h1

/-- Lipschitz of ξ on the left slab, given a bound on ‖deriv ξ‖₊. -/
theorem riemannXi_lipschitz_on_leftoverLeftSlab {ε : ℝ} (hε : 0 < ε)
    {C : NNReal} (hC : ∀ z ∈ leftoverLeftSlab ε, ‖deriv riemannXi z‖₊ ≤ C) :
    LipschitzOnWith C riemannXi (leftoverLeftSlab ε) :=
  riemannXi_lipschitz_on_convex (convex_leftoverLeftSlab ε)
    (fun _z hz => differentiableAt_riemannXi_leftoverLeftSlab hε hz) hC


/-! ### Up and down slabs (convex pieces around ball(1,ε)) -/

/-- Up slab: 1-ε ≤ Re s ≤ 1 and ε ≤ Im s ≤ 1/2. Convex piece above ball(1,ε). -/
def leftoverUpSlab (ε : ℝ) : Set ℂ :=
  {s : ℂ | 1 - ε ≤ s.re ∧ s.re ≤ 1 ∧ ε ≤ s.im ∧ s.im ≤ (2 : ℝ)⁻¹}

theorem convex_leftoverUpSlab (ε : ℝ) : Convex ℝ (leftoverUpSlab ε) := by
  have : leftoverUpSlab ε =
      {c : ℂ | 1 - ε ≤ c.re} ∩ {c : ℂ | c.re ≤ 1} ∩
        {c : ℂ | ε ≤ c.im} ∩ {c : ℂ | c.im ≤ (2 : ℝ)⁻¹} := by
    ext s
    simp [leftoverUpSlab, and_assoc]
  rw [this]
  exact (((convex_halfSpace_re_ge _).inter (convex_halfSpace_re_le _)).inter
    (convex_halfSpace_im_ge _)).inter (convex_halfSpace_im_le _)

theorem leftoverUpSlab_subset_leftoverRect {ε : ℝ} (hε : 0 ≤ ε) (hε2 : ε ≤ (2 : ℝ)⁻¹) :
    leftoverUpSlab ε ⊆ leftoverRect := by
  intro s hs
  refine ⟨by linarith [hs.1], hs.2.1, ?_⟩
  rw [abs_le]
  refine ⟨by linarith [hs.2.2.1], hs.2.2.2⟩

theorem leftoverUpSlab_subset_sdiff_ball {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ (2 : ℝ)⁻¹) :
    leftoverUpSlab ε ⊆ leftoverRect \ ball (1 : ℂ) ε := by
  intro s hs
  refine ⟨leftoverUpSlab_subset_leftoverRect hε.le hε2 hs, ?_⟩
  intro hb
  have hdist : dist s (1 : ℂ) < ε := hb
  have hnorm : ‖s - (1 : ℂ)‖ < ε := by simpa [dist_eq_norm] using hdist
  have habs : |s.im| ≤ ‖s - (1 : ℂ)‖ := by simpa using abs_im_le_norm (s - 1)
  have hle : s.im ≤ |s.im| := le_abs_self s.im
  have hpos : ε ≤ s.im := hs.2.2.1
  linarith

theorem differentiableAt_riemannXi_leftoverUpSlab {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ (2 : ℝ)⁻¹)
    {s : ℂ} (hs : s ∈ leftoverUpSlab ε) :
    DifferentiableAt ℂ riemannXi s := by
  have hR := leftoverUpSlab_subset_leftoverRect hε.le hε2 hs
  have h1 : s ≠ 1 := by
    intro heq
    have h_one_mem : (1 : ℂ) ∈ leftoverUpSlab ε := by simpa [heq] using hs
    have : ε ≤ (0 : ℝ) := by simpa using h_one_mem.2.2.1
    linarith
  exact differentiableAt_riemannXi_leftoverRect hR h1

theorem riemannXi_lipschitz_on_leftoverUpSlab {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ (2 : ℝ)⁻¹)
    {C : NNReal} (hC : ∀ z ∈ leftoverUpSlab ε, ‖deriv riemannXi z‖₊ ≤ C) :
    LipschitzOnWith C riemannXi (leftoverUpSlab ε) :=
  riemannXi_lipschitz_on_convex (convex_leftoverUpSlab ε)
    (fun _z hz => differentiableAt_riemannXi_leftoverUpSlab hε hε2 hz) hC

/-- Down slab: 1-ε ≤ Re s ≤ 1 and -1/2 ≤ Im s ≤ -ε. Convex piece below ball(1,ε). -/
def leftoverDnSlab (ε : ℝ) : Set ℂ :=
  {s : ℂ | 1 - ε ≤ s.re ∧ s.re ≤ 1 ∧ -(2 : ℝ)⁻¹ ≤ s.im ∧ s.im ≤ -ε}

theorem convex_leftoverDnSlab (ε : ℝ) : Convex ℝ (leftoverDnSlab ε) := by
  have : leftoverDnSlab ε =
      {c : ℂ | 1 - ε ≤ c.re} ∩ {c : ℂ | c.re ≤ 1} ∩
        {c : ℂ | -(2 : ℝ)⁻¹ ≤ c.im} ∩ {c : ℂ | c.im ≤ -ε} := by
    ext s
    simp [leftoverDnSlab, and_assoc]
  rw [this]
  exact (((convex_halfSpace_re_ge _).inter (convex_halfSpace_re_le _)).inter
    (convex_halfSpace_im_ge _)).inter (convex_halfSpace_im_le _)

theorem leftoverDnSlab_subset_leftoverRect {ε : ℝ} (hε : 0 ≤ ε) (hε2 : ε ≤ (2 : ℝ)⁻¹) :
    leftoverDnSlab ε ⊆ leftoverRect := by
  intro s hs
  refine ⟨by linarith [hs.1], hs.2.1, ?_⟩
  rw [abs_le]
  refine ⟨hs.2.2.1, by linarith [hs.2.2.2]⟩

theorem leftoverDnSlab_subset_sdiff_ball {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ (2 : ℝ)⁻¹) :
    leftoverDnSlab ε ⊆ leftoverRect \ ball (1 : ℂ) ε := by
  intro s hs
  refine ⟨leftoverDnSlab_subset_leftoverRect hε.le hε2 hs, ?_⟩
  intro hb
  have hdist : dist s (1 : ℂ) < ε := hb
  have hnorm : ‖s - (1 : ℂ)‖ < ε := by simpa [dist_eq_norm] using hdist
  have habs : |s.im| ≤ ‖s - (1 : ℂ)‖ := by simpa using abs_im_le_norm (s - 1)
  have hneg : -s.im ≤ |s.im| := neg_le_abs s.im
  have hle : ε ≤ -s.im := by
    have : s.im ≤ -ε := hs.2.2.2
    linarith
  linarith

theorem differentiableAt_riemannXi_leftoverDnSlab {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ (2 : ℝ)⁻¹)
    {s : ℂ} (hs : s ∈ leftoverDnSlab ε) :
    DifferentiableAt ℂ riemannXi s := by
  have hR := leftoverDnSlab_subset_leftoverRect hε.le hε2 hs
  have h1 : s ≠ 1 := by
    intro heq
    have h_one_mem : (1 : ℂ) ∈ leftoverDnSlab ε := by simpa [heq] using hs
    have : (0 : ℝ) ≤ -ε := by simpa using h_one_mem.2.2.2
    linarith
  exact differentiableAt_riemannXi_leftoverRect hR h1

theorem riemannXi_lipschitz_on_leftoverDnSlab {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ (2 : ℝ)⁻¹)
    {C : NNReal} (hC : ∀ z ∈ leftoverDnSlab ε, ‖deriv riemannXi z‖₊ ≤ C) :
    LipschitzOnWith C riemannXi (leftoverDnSlab ε) :=
  riemannXi_lipschitz_on_convex (convex_leftoverDnSlab ε)
    (fun _z hz => differentiableAt_riemannXi_leftoverDnSlab hε hε2 hz) hC

end RhG1Lean
