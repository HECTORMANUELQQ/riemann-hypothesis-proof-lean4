/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under CC-BY 4.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic
import RhG1Lean.ArithmeticPrimeDominanceLattice

/-!
# ArithmeticEulerTotientMultiplicativeFloor: Euler Totient Multiplicative Positivity

This module formalizes the tenth foundational, purely arithmetic master pillar:
**The Euler Totient Multiplicative Floor and Local Factor Positivity**.

## Arithmetic Principle:
Euler's totient function $\phi(n) = n \prod_{p \mid n} (1 - p^{-1})$ satisfies the
fundamental Dirichlet convolution identity:
$$\mathbf{1} * \phi = \mathrm{id} \iff \sum_{d \mid n} \phi(d) = n$$
In terms of Dirichlet series:
$$\sum_{n=1}^\infty \frac{\phi(n)}{n^s} = \frac{\zeta(s-1)}{\zeta(s)}$$

Key arithmetic structures established here:
1. **Universal Integer Positivity Floor**:
   For every $n \ge 1$, $\phi(n) \ge 1$. The coefficients of $\frac{\zeta(s-1)}{\zeta(s)}$
   are strictly positive integers everywhere on $\mathbb{N}_{\ge 1}$.
2. **Minimal Local Prime Ratio at Base 2**:
   For $n = 2$, $\phi(2) = 1$, giving the exact floor ratio:
   $$\frac{\phi(2)}{2} = \frac{1}{2} > 0$$
3. **Local Prime Factor Boundedness**:
   For any prime $p \ge 2$, the local quotient satisfies:
   $$\frac{1}{2} \le 1 - \frac{1}{p} < 1$$
   precluding any local Euler factor from collapsing to zero on the critical boundary.
-/

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.style.emptyLine false
set_option linter.style.openClassical false
set_option linter.unusedVariables false

open Real Complex Set

namespace RhG1Lean

/-! ### Part I: Totient Counting & Normalized Ratio Floor -/

/-- Euler totient ratio $\phi(n)/n$ for positive integers. -/
noncomputable def totientRatio (n : ℕ) : ℝ :=
  (n.totient : ℝ) / (n : ℝ)

/-- Strict positivity of the totient counting function for any $n \ge 1$. -/
theorem totient_pos_of_pos {n : ℕ} (hn : 0 < n) : 0 < n.totient :=
  Nat.totient_pos.mpr hn

/-- Real cast positivity of the totient count for $n \ge 1$. -/
theorem totient_real_pos {n : ℕ} (hn : 1 ≤ n) : 0 < (n.totient : ℝ) := by
  have : 0 < n := by linarith
  exact Nat.cast_pos.mpr (totient_pos_of_pos this)

/-- Grounding the base totient count at 2: $\phi(2) = 1$. -/
theorem totient_two : Nat.totient 2 = 1 := by
  decide

/-- Strict positivity of the normalized totient ratio for $n \ge 1$. -/
theorem totientRatio_pos {n : ℕ} (hn : 1 ≤ n) : 0 < totientRatio n := by
  unfold totientRatio
  have h_num : 0 < (n.totient : ℝ) := totient_real_pos hn
  have h_den : 0 < (n : ℝ) := by
    have : 0 < n := by linarith
    exact Nat.cast_pos.mpr this
  exact div_pos h_num h_den

/-- Exact base floor value of the totient ratio at $n = 2$: $\phi(2)/2 = 1/2$. -/
theorem totientRatio_two : totientRatio 2 = 1 / 2 := by
  unfold totientRatio
  rw [totient_two]
  norm_num

/-- Universal upper bound: $\phi(n)/n \le 1$ for all $n \ge 1$. -/
theorem totientRatio_le_one {n : ℕ} (hn : 1 ≤ n) : totientRatio n ≤ 1 := by
  unfold totientRatio
  have h_le : n.totient ≤ n := Nat.totient_le n
  have h_den_pos : 0 < (n : ℝ) := by
    have : 0 < n := by linarith
    exact Nat.cast_pos.mpr this
  have h_cast_le : (n.totient : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr h_le
  exact (div_le_iff₀ h_den_pos).mpr (by linarith)

/-! ### Part II: Local Euler Factor Separation Floor -/

/-- Prime local Euler factor lower bound: for any $p \ge 2$, $1 - 1/p \ge 1/2$. -/
theorem prime_euler_factor_ge_half {p : ℝ} (hp : 2 ≤ p) :
    1 / 2 ≤ 1 - 1 / p := by
  have hp_pos : 0 < p := by linarith
  have h_inv : 1 / p ≤ 1 / 2 := by
    have : (2 : ℝ) ≤ p := hp
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) this
  linarith

/-- Prime local Euler factor upper bound: for any $p > 1$, $1 - 1/p < 1$. -/
theorem prime_euler_factor_lt_one {p : ℝ} (hp : 1 < p) :
    1 - 1 / p < 1 := by
  have hp_pos : 0 < p := by linarith
  have : 0 < 1 / p := div_pos (by norm_num) hp_pos
  linarith

/-! ### Part III: The 10th Pillar Architecture Package -/

/-- **Arithmetic Euler Totient Package**:
Encapsulates the totient positivity, minimal ratio floor, and Euler factor separation. -/
structure ArithmeticEulerTotientPackage where
  -- Strict positivity of the totient function
  totient_pos : ∀ {n : ℕ}, 1 ≤ n → 0 < (n.totient : ℝ)
  -- Exact base totient at 2
  totient_two_eq : Nat.totient 2 = 1
  -- Positivity of the totient ratio
  ratio_pos : ∀ {n : ℕ}, 1 ≤ n → 0 < totientRatio n
  -- Exact floor ratio at 2
  ratio_two_eq : totientRatio 2 = 1 / 2
  -- Upper bound by 1
  ratio_le_one : ∀ {n : ℕ}, 1 ≤ n → totientRatio n ≤ 1
  -- Prime local Euler factor floor
  euler_factor_ge_half : ∀ {p : ℝ}, 2 ≤ p → 1 / 2 ≤ 1 - 1 / p

/-- Universal realization of the Euler Totient Package in Lean 4. -/
theorem arithmetic_euler_totient_package_universal :
    ArithmeticEulerTotientPackage := {
  totient_pos := fun hn => totient_real_pos hn,
  totient_two_eq := totient_two,
  ratio_pos := fun hn => totientRatio_pos hn,
  ratio_two_eq := totientRatio_two,
  ratio_le_one := fun hn => totientRatio_le_one hn,
  euler_factor_ge_half := fun hp => prime_euler_factor_ge_half hp
}

end RhG1Lean
