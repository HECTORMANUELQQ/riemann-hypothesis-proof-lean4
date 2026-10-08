/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import RhG1Lean.Arc
import RhG1Lean.Majorant
import RhG1Lean.Diameter
import RhG1Lean.Nonvanishing

/-!
# G4 · match del principio del argumento (Cβ61 / A5)

Mapa: G4 = instanciar dominio / hipótesis / conclusión, no inventar otro contorno.

Instancia que ya está en Lean:

* f = `riemannXi` (ξ del mapa AX-C4)
* Γ½ = C_R ∪ L_R (arco G1 ∪ diámetro G2)
* En Re s > 1: cota |ξ| ≤ M (G1, G2 |y|>1/2) y ξ ≠ 0 (G3)
* Interior del semi-disco ⊂ {Re u > 0} = O₁ (geometría del mapa 47)

Otras lógicas (documentos, diccionario — no son este teorema):

* Rosas / HTML: ξ=0 en la recta es “las flechas apagan el 1”. Este G
  no usa pétalos; el objeto es el mismo cero de ξ.
* Monografía Pick: polar p^{-iγ ln p} es la hoja de primos (N2), no el
  contorno Γ½. Pick no sustituye G4; si hace falta radio vs σ, está ahí.
* Compacto |y|≤1/2: s ≠ 1 (`sOnDiameter_ne_one`); Re s ≤ 1; G4 no
  reclama AP ahí todavía.

G5 (N=0) sigue OPEN: hace falta el argumento / Rouché con estas piezas.
-/

open Complex Real

namespace RhG1Lean

/-- Piezas G1–G3 listas para AP donde Re s > 1 (arco). -/
theorem G4_arc_ready {R φ : ℝ} (hR : 1 / 2 < R) (hφ : |φ| ≤ π / 4)
    {s : ℂ} (hs : s.re = reSR R φ) :
    ‖riemannXi s‖ ≤ majorantXi s ∧ riemannXi s ≠ 0 :=
  ⟨norm_riemannXi_le_majorant_on_arc hR hφ hs, G3_riemannXi_ne_zero_on_arc hR hφ hs⟩

/-- Piezas G1–G3 listas para AP en el diámetro |y| > 1/2. -/
theorem G4_diameter_ready {y : ℝ} (hy : 1 / 2 < |y|) :
    ‖riemannXi (sOnDiameter y)‖ ≤ majorantXi (sOnDiameter y) ∧
      riemannXi (sOnDiameter y) ≠ 0 :=
  ⟨G2_norm_riemannXi_le_majorant hy, G3_riemannXi_ne_zero_on_diameter hy⟩

/-- Polo s=1 fuera del diámetro. -/
theorem G4_diameter_avoids_pole (y : ℝ) : sOnDiameter y ≠ 1 :=
  sOnDiameter_ne_one y

end RhG1Lean
