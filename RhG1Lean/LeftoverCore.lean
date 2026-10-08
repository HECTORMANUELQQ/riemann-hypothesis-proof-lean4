/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.NumberTheory.LSeries.ZetaZeros
import RhG1Lean.LeftoverNonvanishing
import RhG1Lean.G5Interior
import RhG1Lean.FunEq
import RhG1Lean.Eta

/-!
# Gap 5.1 board — compact core and metric ball at s=1

After LeftoverNonvanishing (right face + open cut U around 1):

* leftoverRect \\ U is compact and has finitely many zeta zeros.
* There is a metric ball around 1 on which zeta does not vanish in leftoverRect.

Does not empty leftoverInterior. Does not declare RH.
-/

open Complex Real Filter Topology Set Metric

namespace RhG1Lean

/-! ### C1b — compact board for the remaining OPEN of 5.1 -/

/-- Removing an open set from the leftover box keeps it compact. -/
theorem isCompact_leftoverRect_sdiff_open {U : Set ℂ} (hU : IsOpen U) :
    IsCompact (leftoverRect \ U) :=
  isCompact_leftoverRect.diff hU

/-- Finitely many zeta zeros on leftoverRect \\ U. Not N=0. -/
theorem finite_zeta_zeros_leftoverRect_sdiff_open {U : Set ℂ} (hU : IsOpen U) :
    ((leftoverRect \ U) ∩ riemannZetaZeros).Finite :=
  (isCompact_leftoverRect_sdiff_open hU).inter_riemannZetaZeros_finite

/--
With the open cut U from exists_open_nhds_one_leftoverRect_zeta_ne_zero,
every zeta zero of leftoverRect lies in the compact set leftoverRect \\ U
(and already in leftoverInterior \\ U by LeftoverNonvanishing).
-/
theorem zeta_zero_mem_leftoverRect_sdiff_open_cut
    {U : Set ℂ}
    (hne : ∀ s ∈ U ∩ leftoverRect, riemannZeta s ≠ 0)
    {s : ℂ} (hs : s ∈ leftoverRect) (hz : riemannZeta s = 0) :
    s ∈ leftoverRect \ U := by
  refine ⟨hs, ?_⟩
  exact zeta_zero_leftoverInterior_notMem_nhds_one hne
    (zeta_zero_mem_leftoverRect_imp_leftoverInterior hs hz) hz

/-! ### C1a — metric ball around 1 (size existential, from nhds) -/

/--
There is a positive radius ε such that zeta has no zeros in the metric ball
of radius ε about 1, inside leftoverRect. This is the metric form of the open cut;
it does **not** give a full vertical slab |Im| ≤ 1/2.
-/
theorem exists_ball_one_leftoverRect_zeta_ne_zero :
    ∃ ε > (0 : ℝ), ∀ s ∈ ball (1 : ℂ) ε ∩ leftoverRect, riemannZeta s ≠ 0 := by
  obtain ⟨U, hOpen, h1, hne⟩ := exists_open_nhds_one_leftoverRect_zeta_ne_zero
  rw [Metric.isOpen_iff] at hOpen
  obtain ⟨ε, hε, hsub⟩ := hOpen 1 h1
  refine ⟨ε, hε, ?_⟩
  intro s hs
  exact hne s ⟨hsub hs.1, hs.2⟩

/-- Same fact: zeros of leftoverRect miss some ball about 1. -/
theorem exists_ball_one_cut_leftoverInterior_zeros :
    ∃ ε > (0 : ℝ),
      ∀ s ∈ leftoverRect, riemannZeta s = 0 → s ∉ ball (1 : ℂ) ε := by
  obtain ⟨ε, hε, hne⟩ := exists_ball_one_leftoverRect_zeta_ne_zero
  refine ⟨ε, hε, ?_⟩
  intro s hs hz hsBall
  exact hne s ⟨hsBall, hs⟩ hz

/-! ### Bridge ξ ↔ ζ on the leftover box (needed before |ξ|-attacks) -/

theorem ne_zero_of_mem_leftoverRect {s : ℂ} (hs : s ∈ leftoverRect) : s ≠ 0 := by
  intro h
  have hre : (2 : ℝ)⁻¹ ≤ s.re := hs.1
  simp [h] at hre
  norm_num at hre

theorem ne_one_of_mem_leftoverInterior {s : ℂ} (hs : s ∈ leftoverInterior) : s ≠ 1 := by
  intro h
  have : s.re < 1 := hs.2
  simp [h] at this

/-- On leftoverRect, away from the pole s=1: ξ(s)=0 ↔ ζ(s)=0.
Same pattern as `riemannXi_eq_zero_iff_zeta_sOnDiameter` in Nonvanishing. -/
theorem riemannXi_eq_zero_iff_zeta_leftoverRect {s : ℂ}
    (hs : s ∈ leftoverRect) (h1 : s ≠ 1) :
    riemannXi s = 0 ↔ riemannZeta s = 0 := by
  unfold riemannXi
  constructor
  · intro h
    have hπ := pi_cpow_neg_half_ne_zero s
    have hG := Complex.Gamma_ne_zero_of_re_pos (leftoverRect_re_half_pos hs)
    have hp : s * (s - 1) / 2 ≠ 0 := by
      intro hp
      have hn : s * (s - 1) = 0 := (div_eq_zero_iff.mp hp).resolve_right two_ne_zero
      rcases mul_eq_zero.mp hn with hz | h1'
      · exact (ne_zero_of_mem_leftoverRect hs) hz
      · exact h1 (sub_eq_zero.mp h1')
    have : s * (s - 1) / 2 * (π : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) *
        riemannZeta s = 0 := h
    simp only [mul_eq_zero] at this
    tauto
  · intro h
    simp [h]

/-- Compact leftover core outside a ball about 1; every zeta zero of the box lands there. -/
theorem exists_compact_leftoverCore_cut :
    ∃ ε > (0 : ℝ),
      IsCompact (leftoverRect \ ball (1 : ℂ) ε) ∧
        ∀ s ∈ leftoverRect, riemannZeta s = 0 → s ∈ leftoverRect \ ball (1 : ℂ) ε := by
  obtain ⟨ε, hε, hmiss⟩ := exists_ball_one_cut_leftoverInterior_zeros
  refine ⟨ε, hε, isCompact_leftoverRect_sdiff_open isOpen_ball, ?_⟩
  intro s hs hz
  exact ⟨hs, hmiss s hs hz⟩

/-! ### Continuity of ‖ξ‖ on the compact core (board for |ξ|-attack; not N=0) -/

/-- If `1 ∈ U`, then every point of `leftoverRect \\ U` avoids the pole. -/
theorem ne_one_of_mem_leftoverRect_sdiff {U : Set ℂ} (h1 : (1 : ℂ) ∈ U)
    {s : ℂ} (hs : s ∈ leftoverRect \ U) : s ≠ 1 := by
  intro heq
  subst heq
  exact hs.2 h1

/-- ξ is differentiable on leftoverRect \\ U when 1 ∈ U.
Uses `differentiableAt_riemannXi_leftoverRect` (LeftoverCompact). -/
theorem differentiableOn_riemannXi_leftoverRect_sdiff
    {U : Set ℂ} (h1 : (1 : ℂ) ∈ U) :
    DifferentiableOn ℂ riemannXi (leftoverRect \ U) := by
  intro s hs
  exact (differentiableAt_riemannXi_leftoverRect hs.1
    (ne_one_of_mem_leftoverRect_sdiff h1 hs)).differentiableWithinAt

/-- Continuity of ‖ξ‖ on leftoverRect \\ U. Does **not** claim ‖ξ‖ > 0 or N=0. -/
theorem continuousOn_norm_riemannXi_leftoverRect_sdiff
    {U : Set ℂ} (_hU : IsOpen U) (h1 : (1 : ℂ) ∈ U) :
    ContinuousOn (fun s => ‖riemannXi s‖) (leftoverRect \ U) :=
  (differentiableOn_riemannXi_leftoverRect_sdiff h1).continuousOn.norm

/-- Minimum of ‖ξ‖ on a nonempty compact leftoverRect \\ U.
Still does **not** claim the minimum is positive. -/
theorem exists_isMinOn_norm_riemannXi_leftoverRect_sdiff
    {U : Set ℂ} (hU : IsOpen U) (h1 : (1 : ℂ) ∈ U)
    (hne : (leftoverRect \ U).Nonempty) :
    ∃ s₀ ∈ leftoverRect \ U,
      IsMinOn (fun s => ‖riemannXi s‖) (leftoverRect \ U) s₀ :=
  (isCompact_leftoverRect_sdiff_open hU).exists_isMinOn hne
    (continuousOn_norm_riemannXi_leftoverRect_sdiff hU h1)

/-! ### Specialize N1/J4 FE of ξ to leftoverInterior -/

theorem Gammaℝ_ne_zero_of_mem_leftoverRect {s : ℂ} (hs : s ∈ leftoverRect) :
    Gammaℝ s ≠ 0 := by
  rw [Gammaℝ_def]
  refine mul_ne_zero ?_ ?_
  · exact (cpow_eq_zero_iff _ _).not.mpr (by simp [ofReal_eq_zero, Real.pi_ne_zero])
  · exact Complex.Gamma_ne_zero_of_re_pos (leftoverRect_re_half_pos hs)

theorem Gammaℝ_one_sub_ne_zero_of_re_lt_one {s : ℂ} (hre : s.re < 1) :
    Gammaℝ (1 - s) ≠ 0 := by
  rw [Gammaℝ_def]
  refine mul_ne_zero ?_ ?_
  · exact (cpow_eq_zero_iff _ _).not.mpr (by simp [ofReal_eq_zero, Real.pi_ne_zero])
  · have hre2 : ((1 - s) / 2).re = (1 - s.re) / 2 := by
      simp [sub_re, one_re]
    have : 0 < ((1 - s) / 2).re := by
      rw [hre2]; linarith [sub_pos.mpr hre]
    exact Complex.Gamma_ne_zero_of_re_pos this

/-- On leftoverInterior: ξ(1-s)=ξ(s). Identity only; not N=0. -/
theorem riemannXi_one_sub_of_mem_leftoverInterior {s : ℂ}
    (hs : s ∈ leftoverInterior) :
    riemannXi (1 - s) = riemannXi s := by
  have hR : s ∈ leftoverRect := (mem_leftoverInterior.mp hs).1
  have hre : s.re < 1 := (mem_leftoverInterior.mp hs).2
  exact riemannXi_one_sub (ne_zero_of_mem_leftoverRect hR)
    (ne_one_of_mem_leftoverInterior hs)
    (Gammaℝ_ne_zero_of_mem_leftoverRect hR)
    (Gammaℝ_one_sub_ne_zero_of_re_lt_one hre)

theorem norm_riemannXi_one_sub_of_mem_leftoverInterior {s : ℂ}
    (hs : s ∈ leftoverInterior) :
    ‖riemannXi (1 - s)‖ = ‖riemannXi s‖ := by
  rw [riemannXi_one_sub_of_mem_leftoverInterior hs]

/-- Geometric glue (no ZF): O₁-small with δ ∈ [0, 1/2) lands in leftoverInterior. -/
theorem mem_leftoverInterior_of_stripO1Small {δ t : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (h : stripO1Small δ t) :
    ((1 : ℂ) / 2 + (δ : ℂ) + I * t) ∈ leftoverInterior := by
  have hreσ : ((1 : ℂ) / 2 + (δ : ℂ) + I * t).re = 1 / 2 + δ := by simp
  have himσ : ((1 : ℂ) / 2 + (δ : ℂ) + I * t).im = t := by simp
  have htlt : |t| < δ := by
    simpa [abs_of_nonneg hδ0] using h.1
  have ht_le : |t| ≤ (2 : ℝ)⁻¹ := by
    have : |t| < (1 : ℝ) / 2 := lt_trans htlt hδ1
    simpa [one_div] using this.le
  have hrect : ((1 : ℂ) / 2 + (δ : ℂ) + I * t) ∈ leftoverRect := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hreσ]; linarith
    · rw [hreσ]; linarith
    · rw [himσ]; exact ht_le
  refine mem_leftoverInterior.mpr ⟨hrect, ?_⟩
  rw [hreσ]; linarith

/-! ### B — zeros of ξ ↔ zeros of completed Λ on leftoverRect (not N=0) -/

theorem riemannXi_eq_zero_iff_completedRiemannZeta_leftoverRect {s : ℂ}
    (hs : s ∈ leftoverRect) (h1 : s ≠ 1) :
    riemannXi s = 0 ↔ completedRiemannZeta s = 0 := by
  have hs0 := ne_zero_of_mem_leftoverRect hs
  have hG := Gammaℝ_ne_zero_of_mem_leftoverRect hs
  have hpref : s * (s - 1) / 2 ≠ 0 := by
    intro hp
    have hn : s * (s - 1) = 0 := (div_eq_zero_iff.mp hp).resolve_right two_ne_zero
    rcases mul_eq_zero.mp hn with hz | h1'
    · exact hs0 hz
    · exact h1 (sub_eq_zero.mp h1')
  constructor
  · intro hxi
    have : (s * (s - 1) / 2) * completedRiemannZeta s = 0 := by
      rw [← riemannXi_eq_mul_completedRiemannZeta hs0 hG]; exact hxi
    exact (mul_eq_zero.mp this).resolve_left hpref
  · intro hL
    rw [riemannXi_eq_mul_completedRiemannZeta hs0 hG, hL, mul_zero]

/-! ### E — Conditional attack on 5.1: positive lower bound on ‖ξ‖ ⇒ ζ≠0 -/

/-- If ‖ξ‖ ≥ m > 0 on leftoverRect \ ball(1,ε), then ζ ≠ 0 on
leftoverInterior \ ball(1,ε). Does **not** produce m; that remains OPEN. -/
theorem leftoverCore_zeta_ne_zero_of_xi_min_pos
    {ε m : ℝ} (_hε : 0 < ε) (hm : 0 < m)
    (hmin : ∀ s ∈ leftoverRect \ ball (1 : ℂ) ε, m ≤ ‖riemannXi s‖) :
    ∀ s ∈ leftoverInterior \ ball (1 : ℂ) ε, riemannZeta s ≠ 0 := by
  intro s hs
  have hInt : s ∈ leftoverInterior := hs.1
  have hR : s ∈ leftoverRect := (mem_leftoverInterior.mp hInt).1
  have h1 : s ≠ 1 := ne_one_of_mem_leftoverInterior hInt
  have hxi_ge : m ≤ ‖riemannXi s‖ := hmin s ⟨hR, hs.2⟩
  have hxi0 : riemannXi s ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hxi_ge
    linarith
  intro hz
  exact hxi0 ((riemannXi_eq_zero_iff_zeta_leftoverRect hR h1).mpr hz)


/-! ### F2 — positive lower bound of ‖ξ‖ on the right edge cut (not the core) -/

theorem isCompact_leftoverRectRight : IsCompact leftoverRectRight := by
  simpa [leftoverRectRight] using
    isCompact_leftoverRect.inter_right (isClosed_le continuous_const continuous_re)

theorem isCompact_leftoverRectRight_sdiff_ball {ε : ℝ} :
    IsCompact (leftoverRectRight \ ball (1 : ℂ) ε) :=
  isCompact_leftoverRectRight.diff isOpen_ball

theorem mem_leftoverRectRight_one_add_half_I :
    (1 : ℂ) + I * (1 / 2 : ℝ) ∈ leftoverRectRight := by
  have hrect : (1 : ℂ) + I * (1 / 2 : ℝ) ∈ leftoverRect := by
    simp [leftoverRect]
    norm_num
  exact ⟨hrect, by simp⟩

theorem dist_one_add_half_I_one :
    dist ((1 : ℂ) + I * (1 / 2 : ℝ)) (1 : ℂ) = (1 : ℝ) / 2 := by
  simp [dist_eq_norm]

theorem nonempty_leftoverRectRight_sdiff_ball {ε : ℝ}
    (_hε : 0 < ε) (hε' : ε ≤ (1 : ℝ) / 2) :
    (leftoverRectRight \ ball (1 : ℂ) ε).Nonempty := by
  refine ⟨(1 : ℂ) + I * (1 / 2 : ℝ), mem_leftoverRectRight_one_add_half_I, ?_⟩
  intro hb
  have : dist ((1 : ℂ) + I * (1 / 2 : ℝ)) (1 : ℂ) < ε := hb
  rw [dist_one_add_half_I_one] at this
  linarith

/-- **F2.** On leftoverRectRight \ ball(1,ε) with `0 < ε ≤ 1/2`,
there is m > 0 with ‖ξ‖ ≥ m. Not the core m of E. -/
theorem exists_norm_riemannXi_min_pos_right_edge {ε : ℝ}
    (hε : 0 < ε) (hε' : ε ≤ (1 : ℝ) / 2) :
    ∃ m > (0 : ℝ),
      ∀ s ∈ leftoverRectRight \ ball (1 : ℂ) ε, m ≤ ‖riemannXi s‖ := by
  set K := leftoverRectRight \ ball (1 : ℂ) ε
  have hK : IsCompact K := isCompact_leftoverRectRight_sdiff_ball
  have hne : K.Nonempty := nonempty_leftoverRectRight_sdiff_ball hε hε'
  have h1U : (1 : ℂ) ∈ ball (1 : ℂ) ε := mem_ball_self hε
  have hcont : ContinuousOn (fun s => ‖riemannXi s‖) K := by
    refine (continuousOn_norm_riemannXi_leftoverRect_sdiff (U := ball (1 : ℂ) ε)
      isOpen_ball h1U).mono ?_
    intro s hs
    exact ⟨hs.1.1, hs.2⟩
  obtain ⟨s₀, hs₀, hmin⟩ := hK.exists_isMinOn hne hcont
  refine ⟨‖riemannXi s₀‖, ?_, ?_⟩
  · have hs0 : s₀ ≠ 0 := ne_zero_of_mem_leftoverRect hs₀.1.1
    have hs1 : s₀ ≠ 1 := by
      intro h
      exact hs₀.2 (h ▸ h1U)
    exact norm_pos_iff.mpr (leftoverRect_right_xi_ne_zero hs₀.1 hs1 hs0)
  · intro s hs
    exact hmin hs

/-! ### F1.6 specialized to leftoverInterior real axis -/

/-- On the real segment of `leftoverInterior`, `s.re ∈ Ioo 0 1`. -/
theorem leftoverInterior_real_mem_Ioo {s : ℂ}
    (hs : s ∈ leftoverInterior) (_him : s.im = 0) :
    s.re ∈ Ioo (0 : ℝ) 1 := by
  have h := mem_leftoverInterior.mp hs
  refine ⟨by linarith [h.1.1], h.2⟩

/-- **F1.6 (specialized to leftoverInterior)**: If `dirichletEta` agrees with
the alternating series limit on `(0, 1)`, then `riemannZeta` does not vanish
on the real axis inside `leftoverInterior`. -/
theorem leftoverInterior_real_zeta_ne_zero_of_eta_eq {s : ℂ}
    (hs : s ∈ leftoverInterior) (him : s.im = 0) {l : ℝ}
    (hl : Filter.Tendsto
      (fun n ↦ ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * ((i + 1 : ℝ) ^ s.re)⁻¹)
      Filter.atTop (nhds l))
    (heta : dirichletEta (s.re : ℂ) = (l : ℂ)) :
    riemannZeta s ≠ 0 := by
  have hIoo := leftoverInterior_real_mem_Ioo hs him
  have h_ne := riemannZeta_ne_zero_of_dirichletEta_eq_alternating hIoo hl heta
  have hs_eq : (s.re : ℂ) = s := by
    apply Complex.ext
    · simp
    · simp [him]
  rwa [hs_eq] at h_ne

end RhG1Lean
