import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Ronda 6: la Laguerre es la energía de Teager–Kaiser de una señal AM-FM

Para Z = r·cos Φ (amplitud r, fase Φ), con Z′ = r′cos Φ − rΦ′ sin Φ y
Z″ = r″cos Φ − 2r′Φ′ sin Φ − rΦ″ sin Φ − rΦ′² cos Φ:

* `teager_amfm`: Z′² − Z·Z″ = r²Φ′² + (r′² − r r″)·cos²Φ + r²Φ″·sin Φ·cos Φ.
  Como r′² − r r″ = −r²(log r)″, es ℒ = r²[Φ′² − (log r)″cos²Φ + ½Φ″ sin 2Φ]:
  el presupuesto es la frecuencia instantánea al cuadrado (Φ′²), y la amenaza es la curvatura de la envolvente
  (log r)″ cuando la envolvente pasa cerca de 0.
-/

namespace RhG1Lean

theorem teager_amfm (r r1 r2 p1 p2 c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    (r1 * c - r * p1 * s) ^ 2 - (r * c) * (r2 * c - 2 * r1 * p1 * s - r * p2 * s - r * p1 ^ 2 * c)
      = r ^ 2 * p1 ^ 2 + (r1 ^ 2 - r * r2) * c ^ 2 + r ^ 2 * p2 * s * c := by
  linear_combination (r ^ 2 * p1 ^ 2) * h

end RhG1Lean
