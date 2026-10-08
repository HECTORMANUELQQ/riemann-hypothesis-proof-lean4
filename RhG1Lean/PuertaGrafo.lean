import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Polyrith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# La puerta en un caso demostrado: el factor de Ihara 1 − λu + q·u² (grafos regulares)

* `ihara_circulo`: si λ² < 4q (λ real), todo cero u del factor está en el círculo crítico, ‖u‖² = 1/q (la "RH" local de los grafos).
* `ihara_puerta`: en λ² = 4q el factor es q·(u − λ/(2q))², es decir, un cero doble (la puerta).

Es la misma estructura que nuestras bahías: dos ceros espejo que solo pueden salir del círculo chocando en un cero doble.
-/

namespace RhG1Lean

theorem ihara_circulo {q l : ℝ} {u : ℂ} (hq : 0 < q) (hd : l ^ 2 < 4 * q)
    (hu : (q : ℂ) * u ^ 2 - (l : ℂ) * u + 1 = 0) : Complex.normSq u = 1 / q := by
  have hre := congrArg Complex.re hu
  have him := congrArg Complex.im hu
  simp [pow_two, Complex.mul_re, Complex.mul_im] at hre him
  -- him : q*(u.re*u.im + u.im*u.re) − l*u.im = 0 ;  hre : q*(u.re² − u.im²) − l*u.re + 1 = 0
  have hy : u.im ≠ 0 := by
    intro h0
    rw [h0] at hre
    have : 0 < q * u.re ^ 2 - l * u.re + 1 := by nlinarith [sq_nonneg (2 * q * u.re - l)]
    nlinarith
  have hx : 2 * q * u.re = l := by
    have : u.im * (2 * q * u.re - l) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hy
    · linarith
  have h3 : l * u.re = 2 * q * (u.re * u.re) := by rw [← hx]; ring
  have key : q * (u.re * u.re + u.im * u.im) = 1 := by
    linear_combination (-1 : ℝ) * hre + (-1 : ℝ) * h3
  rw [Complex.normSq_apply, eq_div_iff (ne_of_gt hq)]
  linear_combination key

theorem ihara_puerta {q l : ℝ} (hq : 0 < q) (hd : l ^ 2 = 4 * q) (u : ℂ) :
    (q : ℂ) * u ^ 2 - (l : ℂ) * u + 1 = (q : ℂ) * (u - (l : ℂ) / (2 * q)) ^ 2 := by
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hd' : (l : ℂ) ^ 2 = 4 * (q : ℂ) := by exact_mod_cast hd
  field_simp
  linear_combination (-(1 : ℂ)) * hd'

end RhG1Lean
