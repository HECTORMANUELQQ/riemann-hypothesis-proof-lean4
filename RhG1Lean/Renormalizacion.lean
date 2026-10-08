import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Ronda 3, línea E: la identidad de renormalización de la costura trasladada

Con q_h(x) = f(x − h)/f(x + h) (la costura trasladada de Lagarias para f = ξ):

* `duplicacion_escala`: q_{2h}(s) = q_h(s + h)·q_h(s − h). Pasar a la escala gruesa (h → 2h) es un producto exacto.
  Bajar de escala (2h → h) es la dirección difícil, como en el grupo de renormalización: saber que el producto es < 1 no
  dice nada de cada factor.
-/

namespace RhG1Lean

/-- La costura trasladada de una función `f` a escala `h`. -/
def qTras {K : Type*} [Field K] (f : K → K) (h x : K) : K := f (x - h) / f (x + h)

theorem duplicacion_escala {K : Type*} [Field K] (f : K → K) (h s : K) (hs : f s ≠ 0) :
    qTras f (2 * h) s = qTras f h (s + h) * qTras f h (s - h) := by
  unfold qTras
  have e1 : s + h - h = s := by ring
  have e2 : s + h + h = s + 2 * h := by ring
  have e3 : s - h - h = s - 2 * h := by ring
  have e4 : s - h + h = s := by ring
  rw [e1, e2, e3, e4]
  field_simp

end RhG1Lean
