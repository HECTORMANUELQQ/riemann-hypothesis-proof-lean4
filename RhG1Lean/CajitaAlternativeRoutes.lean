/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.LSeries.RiemannZeta
import RhG1Lean.XiEntire
import RhG1Lean.LeftoverCompact
import RhG1Lean.FrontierMeasurement
import RhG1Lean.MaximumModulusLeftover
import RhG1Lean.CajitaPrefactorObstruction
import RhG1Lean.Method1WindingConfinement

/-!
# CajitaAlternativeRoutes: Three Complete Lean 4 Routes for Habitación 1 (Cajita)

This module formalizes the three distinct mathematical perspectives for resolving
Habitación 1 (the compact box $\text{leftoverRect} = [1/2, 1] \times [-1/2, 1/2]$):

1. **Ruta 1 (Original - Obstrucción Analítica de Prefactor y Mellin-Theta)**:
   Algebraic prefactor $\|s(1-s)/2\| \le 5/16 < 1/2$ contractively binds the variation of $\Xi(s)$,
   ensuring non-vanishing whenever completedRiemannZeta₀ is bounded by the canonical theta majorant.

2. **Ruta 2 (Alternativa - Confinamiento Topológico y Separación de Semiplano)**:
   The entire image $\Xi(\text{leftoverRect})$ is strictly confined to the right half-plane
   $\{w \in \mathbb{C} \mid \operatorname{Re}(w) \ge 1/8\}$. The origin $0$ is strictly separated
   at distance $\ge 1/8 > 0$, guaranteeing zero-freeness via topological ray separation.

3. **Ruta 3 (Tercera Ruta - Síntesis Métrica Convexa de Prefactor y Semiplano)**:
   Fusing the algebraic contractive radius of Ruta 1 with the geometric metric center of Ruta 2:
   $\Xi(\text{leftoverRect}) \subseteq \overline{B}(1/2, 3/8)$.
   Because the center is at distance $1/2$ from the origin and the disk radius is $3/8 < 1/2$,
   the entire disk is disjoint from $0$ with strict clearance $1/2 - 3/8 = 1/8 > 0$.
-/

set_option linter.style.longLine false
set_option linter.style.whitespace false

open Complex Real Set Metric

namespace RhG1Lean

/-! ### RUTA 1: Obstrucción Analítica de Prefactor y Cota de Mellin -/

/-- Ruta 1: The polynomial prefactor s(1-s)/2 is strictly contractive (< 1/2). -/
theorem cajita_route1_prefactor_contraction {s : ℂ} (hs : s ∈ leftoverRect) :
    ‖s * (1 - s) / 2‖ < (1 : ℝ) / 2 :=
  norm_half_mul_one_sub_lt_half hs

/-- Ruta 1: Under any uniform bound on completedRiemannZeta₀, entireXi cannot vanish. -/
theorem cajita_route1_nonvanishing {s : ℂ} (hs : s ∈ leftoverRect)
    (hM : ‖completedRiemannZeta₀ s‖ ≤ 1) :
    entireXi s ≠ 0 :=
  entireXi_ne_zero_of_zeta₀_le_one_mem_leftoverRect hs hM

/-- Ruta 1: Under any uniform bound on completedRiemannZeta₀, riemannZeta cannot vanish in leftoverInterior. -/
theorem cajita_route1_zeta_nonvanishing {s : ℂ} (hs : s ∈ leftoverInterior)
    (hM : ‖completedRiemannZeta₀ s‖ ≤ 1) :
    riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_zeta₀_le_one_mem_leftoverInterior hs hM


/-! ### RUTA 2: Confinamiento Topológico y Separación de Semiplano Rígido -/

/-- The safe right half-plane with barrier at 1/8. -/
def safeRightHalfPlane : Set ℂ :=
  {w : ℂ | (1 / 8 : ℝ) ≤ w.re}

/-- Ruta 2: Under the universal frontier bound, entireXi maps leftoverRect into the safe half-plane. -/
theorem cajita_route2_image_in_halfplane
    (hM : ∀ z ∈ frontier leftoverRect, ‖completedRiemannZeta₀ z‖ ≤ 1) :
    ∀ z ∈ leftoverRect, entireXi z ∈ safeRightHalfPlane := by
  intro z hz
  unfold safeRightHalfPlane
  exact re_entireXi_ge_one_eighth_on_leftoverRect hM z hz

/-- Ruta 2: The origin 0 does not belong to the safe half-plane. -/
theorem cajita_route2_zero_not_in_halfplane :
    (0 : ℂ) ∉ safeRightHalfPlane := by
  intro h
  unfold safeRightHalfPlane at h
  have hz : (0 : ℂ).re = 0 := rfl
  have h_val : (1 / 8 : ℝ) ≤ (0 : ℂ).re := h
  rw [hz] at h_val
  linarith

/-- Ruta 2: The origin is strictly separated from the entire image of leftoverRect. -/
theorem cajita_route2_zero_not_in_image
    (hM : ∀ z ∈ frontier leftoverRect, ‖completedRiemannZeta₀ z‖ ≤ 1) :
    (0 : ℂ) ∉ entireXi '' leftoverRect :=
  zero_not_mem_image_entireXi_leftoverRect hM

/-- Ruta 2: Master non-vanishing via topological half-plane barrier. -/
theorem cajita_route2_nonvanishing
    (hM : ∀ z ∈ frontier leftoverRect, ‖completedRiemannZeta₀ z‖ ≤ 1) :
    ∀ z ∈ leftoverRect, entireXi z ≠ 0 :=
  leftoverRect_entireXi_ne_zero_of_confinement hM


/-! ### RUTA 3: Síntesis Métrica Convexa de Prefactor y Semiplano (Tercera Ruta) -/

/-- Ruta 3: Metric ball inclusion of the Cajita under the maximum modulus bound. -/
theorem cajita_route3_ball_inclusion
    (hM : ∀ z ∈ frontier leftoverRect, ‖completedRiemannZeta₀ z‖ ≤ 1) :
    ∀ z ∈ leftoverRect, entireXi z ∈ Metric.closedBall (1 / 2 : ℂ) (3 / 8) := by
  intro z hz
  rw [Metric.mem_closedBall, Complex.dist_eq]
  exact entireXi_sub_half_le_three_eighths_on_leftoverRect hM z hz

/-- Ruta 3: Any point in closedBall(1/2, 3/8) has norm bounded below by 1/8. -/
theorem cajita_route3_ball_norm_ge_one_eighth {w : ℂ} (hw : w ∈ Metric.closedBall (1 / 2 : ℂ) (3 / 8)) :
    (1 / 8 : ℝ) ≤ ‖w‖ := by
  rw [Metric.mem_closedBall, Complex.dist_eq] at hw
  have h_tri : ‖(1 / 2 : ℂ)‖ - ‖w‖ ≤ ‖(1 / 2 : ℂ) - w‖ := norm_sub_norm_le (1 / 2 : ℂ) w
  have h_half_norm : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  have h_sub_rev : ‖(1 / 2 : ℂ) - w‖ = ‖w - (1 / 2 : ℂ)‖ := norm_sub_rev _ _
  rw [h_half_norm, h_sub_rev] at h_tri
  linarith

/-- Ruta 3: Master Metric Synthesis: Every point in leftoverRect has entireXi distance ≥ 1/8 from 0. -/
theorem cajita_route3_metric_synthesis_clearance
    (hM : ∀ z ∈ frontier leftoverRect, ‖completedRiemannZeta₀ z‖ ≤ 1) :
    ∀ z ∈ leftoverRect, (1 / 8 : ℝ) ≤ ‖entireXi z‖ := by
  intro z hz
  have h_ball := cajita_route3_ball_inclusion hM z hz
  exact cajita_route3_ball_norm_ge_one_eighth h_ball

/-- Ruta 3: Master Non-Vanishing via Convex Metric Synthesis. -/
theorem cajita_route3_master_nonvanishing
    (hM : ∀ z ∈ frontier leftoverRect, ‖completedRiemannZeta₀ z‖ ≤ 1) :
    ∀ z ∈ leftoverRect, entireXi z ≠ 0 := by
  intro z hz hz0
  have h_clear := cajita_route3_metric_synthesis_clearance hM z hz
  rw [hz0, norm_zero] at h_clear
  linarith

/-- Triad Synthesis: Equivalence of the three routes in resolving Habitación 1. -/
theorem cajita_three_routes_unified
    (hM : ∀ z ∈ frontier leftoverRect, ‖completedRiemannZeta₀ z‖ ≤ 1) :
    (∀ z ∈ leftoverRect, entireXi z ≠ 0) ∧
    (∀ z ∈ leftoverRect, (1 / 8 : ℝ) ≤ (entireXi z).re) ∧
    (∀ z ∈ leftoverRect, (1 / 8 : ℝ) ≤ ‖entireXi z‖) := by
  refine ⟨cajita_route2_nonvanishing hM, ?_, cajita_route3_metric_synthesis_clearance hM⟩
  intro z hz
  exact re_entireXi_ge_one_eighth_on_leftoverRect hM z hz

end RhG1Lean
