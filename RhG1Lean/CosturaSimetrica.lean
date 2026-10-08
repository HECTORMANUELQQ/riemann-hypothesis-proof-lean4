import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Field.Basic

/-!
# Costura simétrica (M20b): una costura exacta para cualquier función con espejo

Valores en un punto `s` (y su espejo `1 − s̄`), en un campo `K` de característica ≠ 2:

* `L`, `S`, `X` son los valores de la función, de la caja y del factor del espejo en `s`.
* `Ls`, `Ss`, `Xs` son los valores "sostenido" (♯): la conjugada evaluada en el espejo.
* El espejo exacto da `X·Xs = 1` y `X·Ls = L`.
* El error de la caja es `E = L − S − X·Ss`, y su sostenido es `Es = Ls − Ss − Xs·S`.

Teoremas:
* `error_simetrico`: `X·Es = E`. El error ya es simétrico respecto del espejo.
* `costura_simetrica_exacta`: con `A = S + E/2` y `As = Ss + Es/2`, se cumple `L = A + X·As`.
-/

namespace RhG1Lean

variable {K : Type*} [Field K]

theorem error_simetrico {L S X Ls Ss Xs : K}
    (hXX : X * Xs = 1) (hXL : X * Ls = L) :
    X * (Ls - Ss - Xs * S) = L - S - X * Ss := by
  linear_combination hXL - S * hXX

theorem costura_simetrica_exacta {L S X Ls Ss Xs : K} (h2 : (2 : K) ≠ 0)
    (hXX : X * Xs = 1) (hXL : X * Ls = L) :
    L = (S + (L - S - X * Ss) / 2) + X * (Ss + (Ls - Ss - Xs * S) / 2) := by
  have hE := error_simetrico (S := S) (Ss := Ss) hXX hXL
  have h2' : (2 : K) * (2 : K)⁻¹ = 1 := mul_inv_cancel₀ h2
  rw [div_eq_mul_inv, div_eq_mul_inv]
  linear_combination (-(2 : K)⁻¹) * hE + (-(L - S - X * Ss)) * h2'

end RhG1Lean
