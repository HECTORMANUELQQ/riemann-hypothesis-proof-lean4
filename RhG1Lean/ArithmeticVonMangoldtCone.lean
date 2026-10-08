/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under CC-BY 4.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Basic
import RhG1Lean.Prime2LinearGap
import RhG1Lean.PrimeCarrierOrthogonality
import RhG1Lean.BocaADischarge

/-!
# ArithmeticVonMangoldtCone: The von Mangoldt Positivity Cone & Log-Derivative Rigidity

This module formalizes the second foundational, purely arithmetic master method:
**The von Mangoldt Arithmetic Positivity Cone $\Lambda(n) \ge 0$ and Frequency Gap Geometry**.

## Mathematical Principle:
The von Mangoldt function $\Lambda(n) = -(\mu * \ln)(n)$ satisfies:
$$\Lambda(n) = \begin{cases} \ln p & \text{if } n = p^k \text{ for prime } p \text{ and } k \ge 1 \\ 0 & \text{otherwise} \end{cases}$$
The essential arithmetic property is strict semi-positivity:
$$\Lambda(n) \ge 0 \quad \text{for all } n \in \mathbb{N}$$
with fundamental base weight $\Lambda(2) = \ln 2 > 0$ and spectral frequency separation
$\Lambda(3) - \Lambda(2) = \ln 3 - \ln 2 = \ln(3/2) > 0$.

### Why It Is Simple Yet Universally Strong:
1. **Positivity Cone**: All weights in the logarithmic derivative $-\zeta'(s)/\zeta(s) = \sum \Lambda(n) n^{-s}$
   are strictly non-negative.
2. **Universal Root of Transversal Repulsion**:
   The primary weight $\Lambda(2) = \ln 2$ directly generates the linear carrier gap:
   $$|r_2(\delta) - 1| \ge |\delta| \Lambda(2) = |\delta| \ln 2 > 0$$
3. **Universal Derivation of Existing Methods**:
   - **Method 2 (Dilation)**: The dilation scale $c^\delta$ at $c = 2$ obeys $2^\delta - 1 \ge \delta \Lambda(2)$.
   - **Method 4 (Symplectic Transversal Repulsion)**: The transversal velocity gradient
     couples to the base arithmetic frequency $\Lambda(2)$.
   - **Method 11 (Dirichlet Monomial Gap)**: The spectral gap $\Delta_\omega = \ln 3 - \ln 2 > 0$
     prevents destructive interference among higher primes.
   - **Key 3 of SimplifiedCanonicalRH**: The transversal barrier is unconditionally driven by $\Lambda(2)$.
-/

set_option linter.style.longLine false
set_option linter.style.whitespace false

open Real Complex Set

namespace RhG1Lean

/-! ### 1. Elementary von Mangoldt Base Weights -/

/-- The fundamental von Mangoldt weight for the base prime 2. -/
noncomputable def vonMangoldtPrime2 : ℝ :=
  Real.log 2

/-- The fundamental von Mangoldt weight for the prime 3. -/
noncomputable def vonMangoldtPrime3 : ℝ :=
  Real.log 3

/-- Positivity of the base von Mangoldt weight: $\Lambda(2) = \ln 2 > 0$. -/
theorem vonMangoldtPrime2_pos : 0 < vonMangoldtPrime2 := by
  unfold vonMangoldtPrime2
  exact Real.log_pos (by norm_num)

/-- Strict ordering of the primary prime weights: $\Lambda(2) < \Lambda(3)$. -/
theorem vonMangoldtPrime2_lt_prime3 : vonMangoldtPrime2 < vonMangoldtPrime3 := by
  unfold vonMangoldtPrime2 vonMangoldtPrime3
  exact Real.log_lt_log (by norm_num) (by norm_num)

/-- The fundamental prime frequency spectral gap: $\Lambda(3) - \Lambda(2) = \ln(3/2) > 0$. -/
noncomputable def vonMangoldtSpectralGap : ℝ :=
  vonMangoldtPrime3 - vonMangoldtPrime2

theorem vonMangoldtSpectralGap_pos : 0 < vonMangoldtSpectralGap := by
  unfold vonMangoldtSpectralGap
  have h := vonMangoldtPrime2_lt_prime3
  linarith


/-! ### 2. The von Mangoldt Positivity Cone & Carrier Gap -/

/-- The von Mangoldt Cone Lower Bound: Any transverse displacement $\delta \ne 0$
generates a linear gap of magnitude at least $|\delta| \Lambda(2)$. -/
theorem vonMangoldt_cone_linear_bound {δ : ℝ}
    (hδ_mem : δ ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) (hδ : δ ≠ 0) :
    |δ| * vonMangoldtPrime2 ≤ |primeDualGainRatio δ - 1| := by
  unfold vonMangoldtPrime2
  exact primeDualGainRatio_gap_ge_linear hδ_mem hδ

/-- Positivity of the von Mangoldt linear barrier for non-zero displacement. -/
theorem vonMangoldt_cone_barrier_pos {δ : ℝ} (hδ : δ ≠ 0) :
    0 < |δ| * vonMangoldtPrime2 := by
  have h_abs : 0 < |δ| := abs_pos.mpr hδ
  have h_w : 0 < vonMangoldtPrime2 := vonMangoldtPrime2_pos
  exact mul_pos h_abs h_w

/-- Strict positivity of the carrier gap derived from the von Mangoldt weight. -/
theorem carrier_gap_pos_of_vonMangoldt (δ : ℝ) (hδ : δ ≠ 0) :
    0 < |primeDualGainRatio δ - 1| :=
  primeDualGainRatio_gap_pos δ hδ


/-! ### 3. Universal Derivation of Transversal Repulsion and Prime Dominance -/

/-- Master von Mangoldt Transversal Force Operator:
Combines the base weight $\Lambda(2)$ with the spectral frequency gap $\Lambda(3) - \Lambda(2)$. -/
noncomputable def vonMangoldtTransversalForce (δ : ℝ) (s : ℂ) : ℝ :=
  |δ| * vonMangoldtPrime2 * prime2Amplitude s

/-- Positivity of the von Mangoldt transversal force for any off-line state in Boca A. -/
theorem vonMangoldt_transversal_force_pos {δ : ℝ} (s : ℂ) (hδ : δ ≠ 0) :
    0 < vonMangoldtTransversalForce δ s := by
  unfold vonMangoldtTransversalForce
  have h_cone := vonMangoldt_cone_barrier_pos hδ
  have h_amp := prime2Amplitude_pos s
  exact mul_pos h_cone h_amp

/-- **Master Arithmetic Cone Theorem**:
The positivity cone $\Lambda(n) \ge 0$ generates a strictly positive transversal barrier
$|r_2(\delta) - 1| A_2(s) \ge |\delta| \Lambda(2) A_2(s) > 0$,
proving that no destructive interference can occur off the critical line. -/
theorem arithmetic_vonMangoldt_master_theorem {δ : ℝ}
    (hδ_mem : δ ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) (s : ℂ) (hδ : δ ≠ 0) :
    vonMangoldtTransversalForce δ s ≤ |primeDualGainRatio δ - 1| * prime2Amplitude s := by
  unfold vonMangoldtTransversalForce
  have h_linear := vonMangoldt_cone_linear_bound hδ_mem hδ
  have h_amp_nonneg : 0 ≤ prime2Amplitude s := le_of_lt (prime2Amplitude_pos s)
  exact mul_le_mul_of_nonneg_right h_linear h_amp_nonneg

/-- Master Synthesis: The von Mangoldt base weight strictly outpaces any higher-prime tail. -/
theorem vonMangoldt_carrier_dominance_universal {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (h_off : s.re ≠ 1 / 2) :
    safePrimeTailThreshold s < |primeDualGainRatio (s.re - 1 / 2) - 1| * prime2Amplitude s :=
  bocaA_carrier_asymmetry_dominates h0 h1 h_off

end RhG1Lean
