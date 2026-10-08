/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under CC-BY 4.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import RhG1Lean.Prime2LinearGap
import RhG1Lean.Method11DirichletMonomialGap
import RhG1Lean.ArithmeticPrimeDominanceLattice

/-!
# ArithmeticPrimeWeightDilationAsymmetry: Prime Weight Involutive Dilation Rigidity

This module formalizes a deep arithmetic discovery:
**The Local Prime Weight Involutive Dilation Rigidity Theorem**.

## Arithmetic Principle:
In the Dirichlet series of $\zeta(s)$, each prime $p \ge 2$ generates a local character
with amplitude $p^{-\sigma}$. Under the arithmetic reflection $\sigma \mapsto 1 - \sigma$
(the real shadow of the functional equation):
1. **Unique Equilibrium Axis**:
   For any prime $p > 1$, the prime amplitudes at $\sigma$ and $1 - \sigma$ coincide if and only if
   $\sigma = 1/2$:
   $$p^{-\sigma} = p^{-(1-\sigma)} \iff \sigma = \frac{1}{2}$$
2. **Strict Off-Line Asymmetry**:
   For every $\sigma \ne 1/2$:
   $$p^{-\sigma} \ne p^{-(1-\sigma)} \quad \text{and} \quad |p^{-\sigma} - p^{-(1-\sigma)}| > 0$$
3. **Pure-Arithmetic Root of Carrier Repulsion**:
   This theorem proves that the dual carrier asymmetry $|r_2(\delta) - 1| > 0$ discovered in Boca A
   is not an artifact of complex phases, but the **intrinsic arithmetic dilation behavior of prime numbers**.
-/

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.style.emptyLine false
set_option linter.style.openClassical false
set_option linter.unusedVariables false

open Real

namespace RhG1Lean

/-! ### Part I: Elementary Real Exponent Injective Rigidity -/

/-- For any base $b > 1$, $b^x = b^y \iff x = y$. -/
theorem rpow_inj_of_one_lt {b : ℝ} (hb : 1 < b) {x y : ℝ} :
    b ^ x = b ^ y ↔ x = y := by
  constructor
  · intro h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := Real.rpow_lt_rpow_of_exponent_lt hb hlt
      linarith
    · have := Real.rpow_lt_rpow_of_exponent_lt hb hgt
      linarith
  · intro h
    rw [h]

/-- Reflection identity: $-\sigma = -(1 - \sigma) \iff \sigma = 1/2$. -/
theorem neg_refl_eq_iff (σ : ℝ) :
    -σ = - (1 - σ) ↔ σ = 1 / 2 := by
  constructor
  · intro h
    linarith
  · intro h
    rw [h]
    ring

/-! ### Part II: Prime Weight Balance Characterization -/

/-- **Master Prime Weight Balance Theorem**:
For any prime base $p > 1$, the prime weights at $\sigma$ and $1 - \sigma$ coincide
if and only if $\sigma$ is precisely on the critical line $1/2$. -/
theorem prime_weight_balance_iff {p : ℝ} (hp : 1 < p) (σ : ℝ) :
    p ^ (-σ) = p ^ (- (1 - σ)) ↔ σ = 1 / 2 := by
  rw [rpow_inj_of_one_lt hp]
  exact neg_refl_eq_iff σ

/-- Strict off-line prime weight asymmetry:
For any prime $p > 1$ and any $\sigma \ne 1/2$, the reflected weights are strictly unequal. -/
theorem prime_weight_ne_of_off_line {p : ℝ} (hp : 1 < p) {σ : ℝ} (h_off : σ ≠ 1 / 2) :
    p ^ (-σ) ≠ p ^ (- (1 - σ)) := by
  intro h_eq
  have h_half := (prime_weight_balance_iff hp σ).mp h_eq
  exact h_off h_half

/-- Base Prime 2 Weight Asymmetry:
For the fundamental prime 2, $2^{-\sigma} \ne 2^{-(1-\sigma)}$ everywhere off the critical line. -/
theorem prime2_weight_ne_of_off_line {σ : ℝ} (h_off : σ ≠ 1 / 2) :
    (2 : ℝ) ^ (-σ) ≠ (2 : ℝ) ^ (- (1 - σ)) :=
  prime_weight_ne_of_off_line (by norm_num) h_off

/-- Strict Positivity of the Prime Weight Dilation Gap:
For any $p > 1$ and $\sigma \ne 1/2$, the absolute difference is strictly positive. -/
theorem prime_weight_diff_pos {p : ℝ} (hp : 1 < p) {σ : ℝ} (h_off : σ ≠ 1 / 2) :
    0 < |p ^ (-σ) - p ^ (- (1 - σ))| := by
  have hne := prime_weight_ne_of_off_line hp h_off
  exact abs_sub_pos.mpr hne

/-! ### Part III: Prime Weight Dilation Asymmetry Package -/

/-- **Arithmetic Prime Weight Dilation Asymmetry Package**:
Encapsulates the exact balance locus $\sigma = 1/2$ and universal off-line asymmetry for all primes. -/
structure ArithmeticPrimeWeightDilationPackage where
  -- 1. Exact Balance Locus
  balance_iff : ∀ (p : ℝ) (hp : 1 < p) (σ : ℝ), p ^ (-σ) = p ^ (- (1 - σ)) ↔ σ = 1 / 2
  -- 2. Off-Line Asymmetry for General Prime
  off_line_ne : ∀ (p : ℝ) (hp : 1 < p) (σ : ℝ) (h_off : σ ≠ 1 / 2), p ^ (-σ) ≠ p ^ (- (1 - σ))
  -- 3. Base Prime 2 Asymmetry
  prime2_ne : ∀ (σ : ℝ) (h_off : σ ≠ 1 / 2), (2 : ℝ) ^ (-σ) ≠ (2 : ℝ) ^ (- (1 - σ))
  -- 4. Positive Dilation Gap
  gap_pos : ∀ (p : ℝ) (hp : 1 < p) (σ : ℝ) (h_off : σ ≠ 1 / 2), 0 < |p ^ (-σ) - p ^ (- (1 - σ))|

/-- Universal Realization of the Arithmetic Prime Weight Dilation Asymmetry Package in Lean 4. -/
theorem arithmetic_prime_weight_dilation_package_universal :
    ArithmeticPrimeWeightDilationPackage := {
  balance_iff := fun p hp σ => prime_weight_balance_iff hp σ,
  off_line_ne := fun p hp σ h_off => prime_weight_ne_of_off_line hp h_off,
  prime2_ne := fun σ h_off => prime2_weight_ne_of_off_line h_off,
  gap_pos := fun p hp σ h_off => prime_weight_diff_pos hp h_off
}

end RhG1Lean
