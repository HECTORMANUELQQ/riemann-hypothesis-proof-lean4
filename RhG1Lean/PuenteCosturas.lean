/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.

# Puente con los proyectos anteriores (Rampa, Costura, Certificado)

Un cero de ξ fuera de la recta tiene que estar en el empate |E| = |E♯| de **todas** las costuras E (con ξ = E + E♯) a la
vez. Junto con `riemannHypothesis_of_rampa` (Espejos.lean): basta UNA costura sin empates fuera de la recta
(dominancia estricta) para la meta. Las bahías de la costura de Riemann–Siegel son el obstáculo para esa costura; las que
tienen la fase candada se pueden "reflejar" (Kawasaki.lean, `apagon_reflejable_iff`).
-/
import RhG1Lean.RutaCostura

open Complex

namespace RhG1Lean

/-- **Un escapado está en el empate de TODAS las costuras.** Si ξ = E + E♯ (cualquier costura) y ξ(z) = 0, entonces
|E(z)| = |E♯(z)|: el cero vive en el conjunto de empate de cada costura a la vez. -/
theorem escapado_en_todo_empate {E : ℂ → ℂ} (hxi : ∀ s, entireXi s = E s + reflejo E s) {z : ℂ}
    (hz : entireXi z = 0) : ‖E z‖ = ‖reflejo E z‖ := by
  have h : reflejo E z = -E z := by
    have := hxi z
    rw [hz] at this
    linear_combination -this
  rw [h, norm_neg]


/-- Dos costuras: un cero de ξ está en el empate de ambas a la vez. -/
theorem escapado_en_dos_empates {E F : ℂ → ℂ} (hE : ∀ s, entireXi s = E s + reflejo E s)
    (hF : ∀ s, entireXi s = F s + reflejo F s) {z : ℂ} (hz : entireXi z = 0) :
    ‖E z‖ = ‖reflejo E z‖ ∧ ‖F z‖ = ‖reflejo F z‖ :=
  ⟨escapado_en_todo_empate hE hz, escapado_en_todo_empate hF hz⟩

end RhG1Lean
