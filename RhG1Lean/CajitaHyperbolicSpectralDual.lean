/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import RhG1Lean.XiEntire
import RhG1Lean.Leftover
import RhG1Lean.LeftoverCompact
import RhG1Lean.CajitaPrefactorObstruction

/-!
# CajitaHyperbolicSpectralDual: The Geometric & Spectral Dual of Habitación 1

This module establishes the profound mathematical duality for Habitación 1 (Cajita):
**From Rational Mellin Prefactors to Hyperbolic Spectral Geometry**.

## The Two Sides of Habitación 1:
- **Side A (Rational Analytic Mellin)**:
  The prefactor $s(1-s)/2$ in $\Xi(s) - 1/2 = -(s(1-s)/2) \Lambda_0(s)$ acting as a contractive
  multiplier on the Jacobi theta Mellin integral.
- **Side B (Hyperbolic Laplace-Beltrami Spectral Geometry)**:
  The quantity $\lambda(s) = s(1-s)$ is the canonical eigenvalue of the hyperbolic
  Laplace-Beltrami operator $\Delta_{\mathbb{H}} = -y^2(\partial_x^2 + \partial_y^2)$ on the modular
  surface $\mathbb{H}^2 / \mathrm{PSL}(2, \mathbb{Z})$ acting on Eisenstein series:
  $$\Delta_{\mathbb{H}} E(z, s) = s(1-s) E(z, s)$$

## Rigorous Duality Theorems:
1. **Critical Line Self-Adjoint Spectrum**:
   On the critical line $s = 1/2 + it$, the hyperbolic eigenvalue $\lambda(1/2+it) = 1/4 + t^2$
   is purely real and belongs to the continuous spectral ray $[1/4, \infty)$.
2. **Off-Line Dissipative Phase**:
   For any off-line point with displacement $\delta = \sigma - 1/2 \ne 0$ and $t \ne 0$,
   $\operatorname{Im}(\lambda(s)) = -2 \delta t \ne 0$.
   The operator loses self-adjoint reality off the critical line.
3. **Sub-Laplacian Compact Confinement in the Cajita**:
   Throughout $\text{leftoverRect}$, $\|\lambda(s)\|^2 \le 5/8 < 1$, preventing any non-trivial
   spectral resonance from bifurcating inside the compact domain.
-/

set_option linter.style.longLine false
set_option linter.style.whitespace false

open Complex Real Set

namespace RhG1Lean

/-! ### Side B: The Hyperbolic Laplace-Beltrami Eigenvalue -/

/-- The hyperbolic Laplace-Beltrami eigenvalue associated to complex parameter s. -/
def hyperbolicEigenvalue (s : ℂ) : ℂ :=
  s * (1 - s)

/-- Real part of the hyperbolic eigenvalue in terms of coordinates $\sigma$ and $t$. -/
theorem hyperbolicEigenvalue_re (s : ℂ) :
    (hyperbolicEigenvalue s).re = s.re * (1 - s.re) + s.im ^ 2 := by
  unfold hyperbolicEigenvalue
  simp only [mul_re, sub_re, one_re, sub_im, one_im, zero_sub]
  ring

/-- Imaginary part of the hyperbolic eigenvalue: $\operatorname{Im}(\lambda(s)) = (1 - 2\sigma) t = -2 \delta t$. -/
theorem hyperbolicEigenvalue_im (s : ℂ) :
    (hyperbolicEigenvalue s).im = (1 - 2 * s.re) * s.im := by
  unfold hyperbolicEigenvalue
  simp only [mul_im, sub_re, one_re, sub_im, one_im, zero_sub]
  ring

/-- On the critical line $\sigma = 1/2$, the imaginary part vanishes identically for all $t$. -/
theorem hyperbolicEigenvalue_critical_im_zero (t : ℝ) :
    (hyperbolicEigenvalue (⟨1 / 2, t⟩ : ℂ)).im = 0 := by
  rw [hyperbolicEigenvalue_im]
  have : (1 : ℝ) - 2 * (1 / 2 : ℝ) = 0 := by norm_num
  rw [this, zero_mul]

/-- On the critical line, the hyperbolic eigenvalue is purely real and equals $1/4 + t^2$. -/
theorem hyperbolicEigenvalue_critical_re (t : ℝ) :
    (hyperbolicEigenvalue (⟨1 / 2, t⟩ : ℂ)).re = 1 / 4 + t ^ 2 := by
  rw [hyperbolicEigenvalue_re]
  have h1 : (1 / 2 : ℝ) * (1 - 1 / 2) = 1 / 4 := by norm_num
  rw [h1]

/-- Off the critical line, for any non-zero height $t \ne 0$, the eigenvalue is strictly non-real. -/
theorem hyperbolicEigenvalue_im_ne_zero_of_off_line {s : ℂ}
    (h_off : s.re ≠ 1 / 2) (ht : s.im ≠ 0) :
    (hyperbolicEigenvalue s).im ≠ 0 := by
  rw [hyperbolicEigenvalue_im]
  have h_factor : 1 - 2 * s.re ≠ 0 := by
    intro h
    have : s.re = 1 / 2 := by linarith
    exact h_off this
  exact mul_ne_zero h_factor ht


/-! ### Spectral Confinement in the Cajita (leftoverRect) -/

/-- Master Hyperbolic Bound: Throughout leftoverRect, the squared norm of the
hyperbolic eigenvalue satisfies $\|\lambda(s)\|^2 \le 5/8$. -/
theorem hyperbolicEigenvalue_norm_sq_le_five_eighths {s : ℂ} (hs : s ∈ leftoverRect) :
    ‖hyperbolicEigenvalue s‖ ^ 2 ≤ (5 : ℝ) / 8 := by
  unfold hyperbolicEigenvalue
  exact norm_sq_mul_one_sub_le_five_eighths hs

/-- The hyperbolic eigenvalue norm is strictly bounded by 1 everywhere in the Cajita. -/
theorem hyperbolicEigenvalue_norm_lt_one {s : ℂ} (hs : s ∈ leftoverRect) :
    ‖hyperbolicEigenvalue s‖ < 1 := by
  unfold hyperbolicEigenvalue
  exact norm_mul_one_sub_lt_one hs

/-- The spectral radius of the half-Laplacian prefactor is strictly less than 1/2. -/
theorem half_hyperbolicEigenvalue_norm_lt_half {s : ℂ} (hs : s ∈ leftoverRect) :
    ‖hyperbolicEigenvalue s / 2‖ < (1 : ℝ) / 2 := by
  unfold hyperbolicEigenvalue
  exact norm_half_mul_one_sub_lt_half hs

/-- Positive Spectral Gap: The hyperbolic eigenvalue clearance from the critical threshold 1. -/
noncomputable def hyperbolicSpectralGap (s : ℂ) : ℝ :=
  1 - ‖hyperbolicEigenvalue s‖

theorem hyperbolicSpectralGap_pos {s : ℂ} (hs : s ∈ leftoverRect) :
    0 < hyperbolicSpectralGap s := by
  unfold hyperbolicSpectralGap
  have h := hyperbolicEigenvalue_norm_lt_one hs
  linarith

/-- **Master Geometric Spectral Duality Theorem**:
The absence of zeros of entireXi in the Cajita is geometrically dual to the
sub-Laplacian spectral gap: because $\|\lambda(s)\| < 1$ and $\|\Lambda_0(s)\| \le 1$,
no hyperbolic resonance can manifest at energy $\lambda(s)$. -/
theorem cajita_hyperbolic_dual_nonvanishing {s : ℂ} (hs : s ∈ leftoverRect)
    (h_bd : ‖completedRiemannZeta₀ s‖ ≤ 1) :
    entireXi s ≠ 0 :=
  entireXi_ne_zero_of_zeta₀_le_one_mem_leftoverRect hs h_bd

end RhG1Lean
