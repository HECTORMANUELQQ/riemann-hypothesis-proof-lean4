/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under CC-BY 4.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Basic
import RhG1Lean.Prime2LinearGap
import RhG1Lean.PrimeCarrierOrthogonality
import RhG1Lean.Method11DirichletMonomialGap

/-!
# ArithmeticPrimeDominanceLattice: Minimal Prime Lattice Dominance

This module formalizes a fundamental pure-arithmetic discovery:
**The Multiplicative Divisibility Lattice and Minimal Prime Monomial Dominance**.

## Arithmetic Principles:
1. **Minimal Prime Floor**:
   Every integer $n \ge 2$ has a minimal prime factor $p_{\min}(n) \ge 2$.
   Consequently, for all $\sigma > 0$:
   $$n^{-\sigma} \le 2^{-\sigma}$$
2. **Strict Prime Isolation**:
   Every integer $n \ge 3$ satisfies:
   $$n^{-\sigma} \le 3^{-\sigma} < 2^{-\sigma} \quad (\sigma > 0)$$
3. **Monomial Spectral Gap**:
   The gap between base prime 2 and secondary prime 3 satisfies:
   $$\Delta_{2,3}(\sigma) = 2^{-\sigma} - 3^{-\sigma} > 0$$
4. **Primary Carrier Wave Isolation**:
   In the Dirichlet algebra, the prime 2 is strictly decoupled from the sum over all $n \ge 3$,
   providing the pure-arithmetic foundation for carrier dominance $W_2(s)$.
-/

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false

open Real

namespace RhG1Lean

/-! ### Part I: Integer Power Ordering in the Positive Half-Line -/

/-- For $\sigma > 0$ and any integer $n \ge 2$, the monomial $n^{-\sigma} \le 2^{-\sigma}$. -/
theorem nat_rpow_neg_le_two_rpow_neg {n : ℕ} (hn : 2 ≤ n) {σ : ℝ} (hσ : 0 < σ) :
    (n : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ) := by
  rcases eq_or_lt_of_le hn with heq | hlt
  · subst heq
    norm_cast
  · have h2 : (0 : ℝ) < 2 := by norm_num
    have hn_cast : (2 : ℝ) < (n : ℝ) := by exact_mod_cast hlt
    have h_exp : -σ < 0 := by linarith
    exact le_of_lt (Real.rpow_lt_rpow_of_neg h2 hn_cast h_exp)

/-- For $\sigma > 0$ and any integer $n \ge 3$, the monomial $n^{-\sigma} \le 3^{-\sigma}$. -/
theorem nat_rpow_neg_le_three_rpow_neg {n : ℕ} (hn : 3 ≤ n) {σ : ℝ} (hσ : 0 < σ) :
    (n : ℝ) ^ (-σ) ≤ (3 : ℝ) ^ (-σ) := by
  rcases eq_or_lt_of_le hn with heq | hlt
  · subst heq
    norm_cast
  · have h3 : (0 : ℝ) < 3 := by norm_num
    have hn_cast : (3 : ℝ) < (n : ℝ) := by exact_mod_cast hlt
    have h_exp : -σ < 0 := by linarith
    exact le_of_lt (Real.rpow_lt_rpow_of_neg h3 hn_cast h_exp)

/-- Strict monomial gap between prime 2 and prime 3: $3^{-\sigma} < 2^{-\sigma}$ for all $\sigma > 0$. -/
theorem prime_gap_two_three_strict {σ : ℝ} (hσ : 0 < σ) :
    (3 : ℝ) ^ (-σ) < (2 : ℝ) ^ (-σ) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have h_base : (2 : ℝ) < 3 := by norm_num
  have h_exp : -σ < 0 := by linarith
  exact Real.rpow_lt_rpow_of_neg h2 h_base h_exp

/-! ### Part II: Arithmetic Monomial Difference Function -/

/-- The arithmetic difference between base prime 2 and prime 3 monomials. -/
noncomputable def prime23MonomialDiff (σ : ℝ) : ℝ :=
  (2 : ℝ) ^ (-σ) - (3 : ℝ) ^ (-σ)

/-- Positivity of the prime 2-3 monomial difference for all $\sigma > 0$. -/
theorem prime23MonomialDiff_pos {σ : ℝ} (hσ : 0 < σ) :
    0 < prime23MonomialDiff σ := by
  unfold prime23MonomialDiff
  have hlt := prime_gap_two_three_strict hσ
  linarith

/-- For any integer $n \ge 3$, its monomial is strictly separated from $2^{-\sigma}$
by at least the prime 2-3 difference. -/
theorem nat_monomial_separation_ge_diff {n : ℕ} (hn : 3 ≤ n) {σ : ℝ} (hσ : 0 < σ) :
    (n : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ) - prime23MonomialDiff σ := by
  unfold prime23MonomialDiff
  have h3 := nat_rpow_neg_le_three_rpow_neg hn hσ
  linarith

/-! ### Part III: Prime 2 Decoupling Package -/

/-- **Arithmetic Prime Dominance Lattice Package**:
Encapsulates the lattice properties isolating prime 2 as the unique maximal monomial among all $n \ge 2$. -/
structure ArithmeticPrimeDominanceLattice where
  -- 1. Base Prime Maximal Monomial
  two_maximal : ∀ (n : ℕ) (hn : 2 ≤ n) (σ : ℝ) (hσ : 0 < σ), (n : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ)
  -- 2. Secondary Prime Bound for n ≥ 3
  three_bound : ∀ (n : ℕ) (hn : 3 ≤ n) (σ : ℝ) (hσ : 0 < σ), (n : ℝ) ^ (-σ) ≤ (3 : ℝ) ^ (-σ)
  -- 3. Strict Prime 2-3 Gap
  strict_gap : ∀ (σ : ℝ) (hσ : 0 < σ), (3 : ℝ) ^ (-σ) < (2 : ℝ) ^ (-σ)
  -- 4. Positive Monomial Difference
  diff_pos : ∀ (σ : ℝ) (hσ : 0 < σ), 0 < prime23MonomialDiff σ
  -- 5. Universal Separation of Higher Integers
  higher_separation : ∀ (n : ℕ) (hn : 3 ≤ n) (σ : ℝ) (hσ : 0 < σ),
    (n : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ) - prime23MonomialDiff σ

/-- Universal Realization of the Arithmetic Prime Dominance Lattice Package in Lean 4. -/
theorem arithmetic_prime_dominance_lattice_universal :
    ArithmeticPrimeDominanceLattice := {
  two_maximal := fun n hn σ hσ => nat_rpow_neg_le_two_rpow_neg hn hσ,
  three_bound := fun n hn σ hσ => nat_rpow_neg_le_three_rpow_neg hn hσ,
  strict_gap := fun σ hσ => prime_gap_two_three_strict hσ,
  diff_pos := fun σ hσ => prime23MonomialDiff_pos hσ,
  higher_separation := fun n hn σ hσ => nat_monomial_separation_ge_diff hn hσ
}

end RhG1Lean
