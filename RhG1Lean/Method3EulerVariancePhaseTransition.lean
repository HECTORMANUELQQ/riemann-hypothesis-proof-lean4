/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Method 3: Probabilistic / Euler Random Walk & Variance Phase Transition

This module formalizes the third independent mathematical perspective:
**Probabilistic Number Theory, Prime Random Walks, and Variance Phase Transitions**.

## Mathematical Principle:
In probabilistic number theory (Selberg, Montgomery, Soundararajan), the logarithm
of the Riemann zeta function or Dirichlet series is modeled as a sum of independent
random phases over primes:
`X(σ) = ∑_p p^(-σ) e^(i θ_p)`.

1. **Euler Variance Exponent**:
   The variance / L² energy of the p-th prime fluctuation is `p^(-2σ)`.
   The collective convergence behavior is governed by the critical exponent `2*σ`.
2. **Phase Transition at σ = 1/2**:
   - For `σ > 1/2`: `2*σ > 1` (subcritical regime). The prime variance sum
     `∑_p p^(-2σ) < ∞` converges. Fluctuations are strictly localized with
     exponentially bounded tails.
   - At `σ = 1/2`: `2*σ = 1` (critical point). The variance sum `∑_p p^(-1) = ∞`
     diverges logarithmically (`log log N`). Fluctuations delocalize across the
     entire complex plane, permitting cancellations and zeros.
   - For `σ < 1/2`: `2*σ < 1` (supercritical regime). The variance sum diverges
     polynomially (`N^(1-2σ)`).
3. **Variance Monotonicity**:
   For every prime `p ≥ 2`, the single-prime variance `p^(-2σ)` is strictly
   monotone decreasing in `σ`.
4. **Deterministic Base Clearance Barrier**:
   The leading term `1 - 2^(-s)` maintains a strictly positive clearance
   `‖1 - 2^(-s)‖ ≥ 1 - 2^(-σ) > 0` for all `σ > 0`.
   For `σ ≥ 1/2`, this clearance is bounded below by `1 - 2^(-1/2) > 0.292`.
5. **No-Cancellation Clearance Theorem**:
   In any representation `1 - 2^(-s) + R`, if the fluctuation tail satisfies
   `‖R‖ < 1 - 2^(-σ)`, then the sum cannot cancel to zero.
-/

set_option linter.style.whitespace false
set_option linter.unusedVariables false

open Real Complex Set

namespace RhG1Lean

/-! ### Prime Variance and Critical Exponent -/

/-- The single-prime variance at real part `σ` for a prime `p`. -/
noncomputable def primeVariance (p : ℕ) (σ : ℝ) : ℝ :=
  (p : ℝ) ^ (-2 * σ)

/-- The critical scaling exponent `2 * σ`. -/
def criticalExponent (σ : ℝ) : ℝ :=
  2 * σ

/-! ### Phase Transition Classification -/

/-- Subcritical regime: The critical exponent exceeds 1 if and only if `σ > 1/2`. -/
theorem subcritical_iff (σ : ℝ) :
    1 < criticalExponent σ ↔ 1 / 2 < σ := by
  unfold criticalExponent
  constructor <;> intro h <;> linarith

/-- Critical boundary: The critical exponent equals 1 if and only if `σ = 1/2`. -/
theorem critical_iff (σ : ℝ) :
    criticalExponent σ = 1 ↔ σ = 1 / 2 := by
  unfold criticalExponent
  constructor <;> intro h <;> linarith

/-- Supercritical regime: The critical exponent is strictly less than 1 if and only if `σ < 1/2`. -/
theorem supercritical_iff (σ : ℝ) :
    criticalExponent σ < 1 ↔ σ < 1 / 2 := by
  unfold criticalExponent
  constructor <;> intro h <;> linarith

/-! ### Strict Monotonicity of Prime Variance -/

/-- For any prime `p ≥ 2`, the prime variance is strictly decreasing with respect to `σ`. -/
theorem primeVariance_strict_anti {p : ℕ} (hp : 2 ≤ p) {σ₁ σ₂ : ℝ} (h : σ₁ < σ₂) :
    primeVariance p σ₂ < primeVariance p σ₁ := by
  unfold primeVariance
  have hp_gt_one : 1 < (p : ℝ) := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have hexp : -2 * σ₂ < -2 * σ₁ := by linarith
  exact Real.rpow_lt_rpow_of_exponent_lt hp_gt_one hexp

/-! ### Base Term Clearance and Non-Cancellation -/

/-- The leading prime character for `p = 2`: `χ₂(s) = 2^(-s)`. -/
noncomputable def primeTwoChar (s : ℂ) : ℂ :=
  ((2 : ℝ) : ℂ) ^ (-s)

/-- The norm of `primeTwoChar s` equals `2^(-Re(s))`. -/
theorem norm_primeTwoChar (s : ℂ) :
    ‖primeTwoChar s‖ = (2 : ℝ) ^ (-s.re) := by
  unfold primeTwoChar
  have hpos : (0 : ℝ) < 2 := by norm_num
  have hnorm := Complex.norm_cpow_eq_rpow_re_of_pos hpos (-s)
  rw [hnorm]
  have : (-s).re = -s.re := by simp
  rw [this]

/-- Clearance bound: `‖1 - χ₂(s)‖ ≥ 1 - 2^(-Re(s))`. -/
theorem norm_one_sub_primeTwoChar_ge (s : ℂ) :
    1 - (2 : ℝ) ^ (-s.re) ≤ ‖(1 : ℂ) - primeTwoChar s‖ := by
  have htri : ‖(1 : ℂ)‖ - ‖primeTwoChar s‖ ≤ ‖(1 : ℂ) - primeTwoChar s‖ :=
    norm_sub_norm_le (1 : ℂ) (primeTwoChar s)
  rw [norm_one, norm_primeTwoChar] at htri
  exact htri

/-- Strict clearance: For any `s` with `Re(s) > 0`, the clearance `1 - 2^(-Re(s))` is strictly positive. -/
theorem clearance_pos_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    0 < 1 - (2 : ℝ) ^ (-s.re) := by
  have hexp : -s.re < 0 := by linarith
  have hlt : (2 : ℝ) ^ (-s.re) < (2 : ℝ) ^ (0 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hexp
  rw [Real.rpow_zero] at hlt
  linarith

/-- **Master No-Cancellation Clearance Theorem**:
If a Dirichlet sum is decomposed as `1 - χ₂(s) + R`, and the tail fluctuation `‖R‖`
is strictly bounded by the base clearance `1 - 2^(-Re(s))`, then the sum cannot vanish. -/
theorem dirichlet_sum_ne_zero_of_tail_lt_clearance {s : ℂ} {R : ℂ}
    (hs : 0 < s.re)
    (hR : ‖R‖ < 1 - (2 : ℝ) ^ (-s.re)) :
    (1 : ℂ) - primeTwoChar s + R ≠ 0 := by
  intro h_zero
  have h_eq : (1 : ℂ) - primeTwoChar s = -R := by
    linear_combination h_zero
  have h_norm : ‖(1 : ℂ) - primeTwoChar s‖ = ‖R‖ := by
    rw [h_eq, norm_neg]
  have h_ge := norm_one_sub_primeTwoChar_ge s
  rw [h_norm] at h_ge
  linarith

/-- For `Re(s) ≥ 1/2`, the base clearance is bounded below by `1 - 2^(-1/2)`. -/
theorem clearance_ge_half_strip {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 - (2 : ℝ) ^ (-s.re) := by
  have hexp : -s.re ≤ -(1 / 2 : ℝ) := by linarith
  have hpow : (2 : ℝ) ^ (-s.re) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  linarith

end RhG1Lean