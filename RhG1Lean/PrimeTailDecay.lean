/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under CC-BY 4.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Prime.Basic
import RhG1Lean.Prime2LinearGap
import RhG1Lean.PrimeTailAnalytic
import RhG1Lean.BocaANonvanishing

/-!
# PrimeTailDecay: Analytic Decay of Higher Primes in Boca A

This module formalizes the quantitative hierarchy between the leader prime $p = 2$
and the higher primes $p \ge 3$ in the critical strip:

1. Logarithmic ordering: $\log 2 < \log 3 < \log p$ for all $p \ge 3$.
2. Relative frequency gap: $\log 3 - \log 2 > 0$.
3. Dominance threshold: For any composite remainder $R$ arising from higher primes,
   if $\|R\| \le \frac{1}{2} (|\delta| \log 2) A_2$, then $R$ is strictly controlled
   by the linear gap $|r_2(\delta) - 1| A_2$, guaranteeing strict non-vanishing.
-/

set_option linter.style.longLine false

open Real Complex Set

namespace RhG1Lean

/-- $\log 2 < \log 3$. -/
theorem log_two_lt_log_three : Real.log 2 < Real.log 3 := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hlt : (2 : ℝ) < 3 := by norm_num
  exact Real.log_lt_log h2 hlt

/-- The logarithmic gap between 3 and 2 is strictly positive: $\log 3 - \log 2 > 0$. -/
theorem log_three_sub_log_two_pos : 0 < Real.log 3 - Real.log 2 :=
  sub_pos.mpr log_two_lt_log_three

/-- Any odd prime is $\ge 3$. -/
theorem three_le_prime_of_ne_two {p : ℕ} (hp : Nat.Prime p) (h2 : p ≠ 2) : 3 ≤ p := by
  have hge : 2 ≤ p := hp.two_le
  rcases lt_or_eq_of_le hge with hlt | heq
  · exact hlt
  · exact False.elim (h2 heq.symm)

/-- For any prime $p \ge 3$, $\log 2 < \log p$. -/
theorem log_two_lt_log_prime {p : ℕ} (hp : 3 ≤ p) : Real.log 2 < Real.log p := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hlt : (2 : ℝ) < p := by
    have : (3 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  exact Real.log_lt_log h2 hlt

/-- The relative frequency ratio $(2 / p)$ is at most $2 / 3$ for any $p \ge 3$. -/
theorem prime_ratio_le_two_thirds {p : ℕ} (hp : 3 ≤ p) : (2 : ℝ) / p ≤ 2 / 3 := by
  have hp_pos : 0 < (p : ℝ) := by
    have : (3 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hp_ge : (3 : ℝ) ≤ p := by exact_mod_cast hp
  rw [div_le_div_iff₀ hp_pos (by norm_num)]
  linarith

/-- **Master Prime-2 Separation from Higher Prime Remainder**:
If the remainder $R$ satisfies the safe linear bound $\|R\| \le \frac{1}{2} (|\delta| \log 2) A_2$,
then for any off-line perturbation $\delta \in [-1/2, 1/2] \setminus \{0\}$,
the total wave cannot vanish. -/
theorem prime_wave_ne_zero_of_decay {δ A₂ : ℝ}
    (hδ_mem : δ ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) (hδ_ne : δ ≠ 0) (hA₂ : 0 < A₂)
    (ψ θ : ℝ) (R : ℂ)
    (h_safe : HasSafePrimeTailBound R δ A₂)
    (hw : w = ((primeDualGainRatio δ * A₂ : ℝ) : ℂ) * channelWave (-θ) +
              (A₂ : ℂ) * channelWave (-2 * ψ + θ) + R) :
    w ≠ 0 :=
  ne_zero_of_safe_bound hδ_mem hδ_ne hA₂ ψ θ R h_safe hw

/-- Master Boca A Off-Line Non-Vanishing under Higher Prime Decay:
For every $s$ in the critical strip with $s.\text{re} \ne 1/2$ in Boca A,
if the higher prime remainder obeys the safe linear bound, then $\zeta(s) \ne 0$. -/
theorem bocaA_zeta_ne_zero_of_prime_decay {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (hne : s.re ≠ 1 / 2)
    (h_tail : ∃ (A₂ : ℝ) (_hA₂ : 0 < A₂) (ψ θ : ℝ) (R : ℂ),
      HasSafePrimeTailBound R (s.re - 1 / 2) A₂ ∧
      riemannZeta s = ((primeDualGainRatio (s.re - 1 / 2) * A₂ : ℝ) : ℂ) * channelWave (-θ) +
                      (A₂ : ℂ) * channelWave (-2 * ψ + θ) + R) :
    riemannZeta s ≠ 0 := by
  rcases h_tail with ⟨A₂, hA₂, ψ, θ, R, h_safe, hw⟩
  exact strip_ne_zero_of_safe_bound h0 h1 hne hA₂ ψ θ R h_safe hw

end RhG1Lean
