import Mathlib.Analysis.Complex.AbsMax

/-!
# Bahía sin apagón: imposible (principio del módulo máximo)

Costura `F = R·(1 + q)`, con `q = χR♯/R`. Una *bahía* es una región acotada donde `‖q‖ > 1`
cuyo borde cumple `‖q‖ ≤ 1`. Los apagones (ceros de `R`) son los polos de `q`.

* `bahia_sin_apagon_acotada`: si `q` es analítica en una región acotada (sin polos, es decir,
  sin apagones) y `‖q‖ ≤ 1` en el borde, entonces `‖q‖ ≤ 1` en toda la región.
* `no_hay_bahia_sin_apagon`: por eso, en una región así no hay ningún punto con `‖q‖ > 1`.
* `costura_sin_apagon_sin_ceros`: tampoco hay ceros de la costura (`q = −1`) adentro, salvo
  el caso degenerado `q ≡ −1` en toda la región.

Nota de la bitácora (M24): para el producto de Euler truncado `P_X`, `R = P_X` no tiene ceros, pero
`R♯` tiene polos en `σ = 1`. Ahí `q` sí tiene polos, y esos polos abren bahías.
-/

open Set Function Bornology

namespace RhG1Lean

theorem bahia_sin_apagon_acotada {U : Set ℂ} {q : ℂ → ℂ} (hU : IsBounded U)
    (hq : DiffContOnCl ℂ q U) (hborde : ∀ z ∈ frontier U, ‖q z‖ ≤ 1) :
    ∀ z ∈ closure U, ‖q z‖ ≤ 1 :=
  fun _ hz => Complex.norm_le_of_forall_mem_frontier_norm_le hU hq hborde hz

theorem no_hay_bahia_sin_apagon {U : Set ℂ} {q : ℂ → ℂ} (hU : IsBounded U)
    (hq : DiffContOnCl ℂ q U) (hborde : ∀ z ∈ frontier U, ‖q z‖ ≤ 1) :
    ¬ ∃ z ∈ U, 1 < ‖q z‖ := by
  rintro ⟨z, hz, hz1⟩
  have := bahia_sin_apagon_acotada hU hq hborde z (subset_closure hz)
  linarith

theorem costura_sin_apagon_sin_ceros {U : Set ℂ} {q : ℂ → ℂ} (hU : IsBounded U)
    (ho : IsOpen U) (hc : IsPreconnected U)
    (hq : DiffContOnCl ℂ q U) (hborde : ∀ z ∈ frontier U, ‖q z‖ ≤ 1)
    {c : ℂ} (hcU : c ∈ U) (hcero : q c = -1) :
    EqOn q (const ℂ (-1)) U := by
  have hmax : IsMaxOn (norm ∘ q) U c := by
    intro z hz
    have h1 : ‖q z‖ ≤ 1 := bahia_sin_apagon_acotada hU hq hborde z (subset_closure hz)
    have h2 : ‖q c‖ = 1 := by rw [hcero]; simp
    change ‖q z‖ ≤ ‖q c‖
    rw [h2]
    exact h1
  have := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hc ho
    hq.differentiableOn hcU hmax
  rw [hcero] at this
  exact this

end RhG1Lean
