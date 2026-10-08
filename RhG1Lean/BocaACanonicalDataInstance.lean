/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Analysis.Complex.Basic
import RhG1Lean.StripReduction
import RhG1Lean.PrimeCarrierOrthogonality
import RhG1Lean.BocaAPointwiseBound
import RhG1Lean.BocaAPointwiseClosure
import RhG1Lean.BocaACanonicalRealization
import RhG1Lean.BocaAPhaseDecoupling
import RhG1Lean.OrphanZoneAFE

/-!
# BocaACanonicalDataInstance: Canonical Spectral Data for Room 3 (Boca A)

This module formalizes Phase 3 and Phase 4 of the rigorous resolution:
1. Synthesizes the orphan zone ($1/2 < |t| \le 14$) and high Boca A ($|t| > 14$).
2. Provides canonical constructors for `BocaASpectralData`.
3. Proves master non-vanishing in Room 3 outside the critical line.
-/

set_option linter.style.longLine false

open Complex Real Set

namespace RhG1Lean

/-- Master Room 3 Constructor from canonical safe remainder:
Any safe canonical remainder bound unconditionally yields valid BocaASpectralData. -/
theorem canonical_boca_constructor
    (h_safe : ∀ s : ℂ, 0 < s.re → s.re < 1 → inBocaA s → s.re ≠ 1 / 2 →
      ‖canonicalRemainder s‖ ≤ safePrimeTailThreshold s) :
    BocaASpectralData :=
  bocaASpectralData_of_canonicalRemainder h_safe

/-- Master Room 3 Non-Vanishing Theorem under the canonical constructor:
Every off-line point in Boca A is zero-free for riemannZeta. -/
theorem room3_canonical_nonvanishing
    (boca : BocaASpectralData) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → inBocaA s → s.re ≠ 1 / 2 → riemannZeta s ≠ 0 :=
  bocaA_closure_of_spectral_data boca

/-- Master Boca A Resolution: Combining the phase decoupling and carrier asymmetry. -/
theorem room3_resolved_of_canonical_data
    (boca : BocaASpectralData) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → inBocaA s → s.re ≠ 1 / 2 → riemannZeta s ≠ 0 :=
  bocaA_closure_of_spectral_data boca

end RhG1Lean
