/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under CC-BY 4.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# F1 · Dirichlet η (factor + even subsum, Re s > 1)

Definición algebraica `η(s) = (1 − 2^{1−s}) ζ(s)`.

* **F1.0** def
* **F1.1** `2^s ≠ 0`
* **F1.2** factor `1 − 2^{1−σ} ≠ 0` si σ ∈ (0,1) (sin ζ)
* **F1.3a** subsuma par = `2^{−s} ζ(s)` si Re s > 1
* **F1.3b** `η = ζ − 2 · (subsuma par)` y coincide con la def si Re s > 1

* **F1.3c** η = serie alternada si Re s > 1
* **F1.4** η holomorfa / AnalyticOnNhd fuera de `{1}`

No tipa F1.5–F1.6 / IAT / ζ≠0 en (0,1). Sin `sorry` de RH.
-/

open Complex Real Set

namespace RhG1Lean

/-! ### F1.0 · definición -/

/-- Dirichlet eta vía el factor algebraico (definición global). -/
noncomputable def dirichletEta (s : ℂ) : ℂ :=
  (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s

@[simp] theorem dirichletEta_def (s : ℂ) :
    dirichletEta s = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s :=
  rfl

/-! ### F1.1 · `2^s ≠ 0` -/

/-- **F1.1.** `(2 : ℂ) ^ s ≠ 0` para todo `s`. -/
theorem two_cpow_ne_zero (s : ℂ) : (2 : ℂ) ^ s ≠ 0 := by
  rw [cpow_ne_zero_iff]
  exact Or.inl two_ne_zero

/-! ### F1.2 · factor ≠ 0 en (0,1) (sin ζ) -/

/-- Auxiliar real: si σ ∈ (0,1) entonces `2^(1−σ) ∈ (1,2)`. -/
theorem one_lt_two_rpow_one_sub_of_mem_Ioo {σ : ℝ} (h : σ ∈ Ioo 0 1) :
    1 < (2 : ℝ) ^ (1 - σ) ∧ (2 : ℝ) ^ (1 - σ) < 2 := by
  obtain ⟨h0, h1⟩ := h
  have hpos : 0 < 1 - σ := by linarith
  have hlt : 1 - σ < 1 := by linarith
  refine ⟨Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) hpos, ?_⟩
  have := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hlt
  simpa [Real.rpow_one] using this

/-- Identifica el cpow complejo con el rpow real cuando el exponente es real. -/
theorem two_cpow_one_sub_eq_ofReal {σ : ℝ} :
    (2 : ℂ) ^ (1 - (σ : ℂ)) = ↑((2 : ℝ) ^ (1 - σ)) := by
  have hcast : (1 : ℂ) - (σ : ℂ) = ↑(1 - σ) := by
    simp [ofReal_sub]
  rw [hcast]
  exact (ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2) (1 - σ)).symm

/-- **F1.2.** Si σ ∈ (0,1) entonces `1 − 2^{1−σ} ≠ 0` (como complejo). Sin ζ. -/
theorem one_sub_two_cpow_one_sub_ne_zero_of_mem_Ioo
    {σ : ℝ} (h : σ ∈ Ioo 0 1) :
    (1 : ℂ) - (2 : ℂ) ^ (1 - (σ : ℂ)) ≠ 0 := by
  have hbounds := one_lt_two_rpow_one_sub_of_mem_Ioo h
  have hne : (2 : ℝ) ^ (1 - σ) ≠ 1 := ne_of_gt hbounds.1
  rw [two_cpow_one_sub_eq_ofReal, sub_ne_zero]
  exact_mod_cast hne.symm

/-! ### F1.3a · subsuma de términos pares -/

/-- Factorización `(2·(n+1))^s = 2^s · (n+1)^s`. -/
theorem mul_two_nat_cpow (n : ℕ) (s : ℂ) :
    (2 * (n + 1) : ℂ) ^ s = (2 : ℂ) ^ s * (n + 1 : ℂ) ^ s := by
  simpa using natCast_mul_natCast_cpow (2 : ℕ) (n + 1) s

/-- Inversa: `((2·(n+1))^s)⁻¹ = 2^{−s} · ((n+1)^s)⁻¹`. -/
theorem inv_mul_two_nat_cpow (n : ℕ) (s : ℂ) :
    ((2 * (n + 1) : ℂ) ^ s)⁻¹ = (2 : ℂ) ^ (-s) * ((n + 1 : ℂ) ^ s)⁻¹ := by
  rw [mul_two_nat_cpow, mul_inv, ← cpow_neg]

/-- Sumabilidad de `n ↦ ((n+1)^s)⁻¹` si `1 < Re s`. -/
theorem summable_inv_nat_add_one_cpow {s : ℂ} (hs : 1 < s.re) :
    Summable fun n : ℕ => ((n + 1 : ℂ) ^ s)⁻¹ := by
  have h := (Complex.summable_one_div_nat_cpow (p := s)).2 hs
  have h' :
      Summable fun n : ℕ => (1 : ℂ) / ((n + 1 : ℕ) : ℂ) ^ s :=
    (summable_nat_add_iff (f := fun n : ℕ => (1 : ℂ) / (n : ℂ) ^ s) 1).2 h
  simpa [one_div, Nat.cast_add, Nat.cast_one] using h'

/-- **F1.3a.** Si `1 < Re s`, la subsuma par es `2^{−s} ζ(s)`. -/
theorem tsum_inv_two_mul_nat_add_one_cpow {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, ((2 * (n + 1) : ℂ) ^ s)⁻¹) = (2 : ℂ) ^ (-s) * riemannZeta s := by
  have hsum := summable_inv_nat_add_one_cpow hs
  simp_rw [inv_mul_two_nat_cpow]
  rw [tsum_mul_left, show
      (∑' n : ℕ, ((n + 1 : ℂ) ^ s)⁻¹) = ∑' n : ℕ, (1 : ℂ) / (n + 1 : ℂ) ^ s by
        simp_rw [one_div],
      ← zeta_eq_tsum_one_div_nat_add_one_cpow hs]

/-! ### F1.3b · η como ζ menos el doble de la subsuma par -/

/-- Identidad `2 · 2^{−s} = 2^{1−s}`. -/
theorem two_mul_two_cpow_neg (s : ℂ) :
    (2 : ℂ) * (2 : ℂ) ^ (-s) = (2 : ℂ) ^ (1 - s) := by
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  calc
    (2 : ℂ) * (2 : ℂ) ^ (-s)
        = (2 : ℂ) ^ (1 : ℂ) * (2 : ℂ) ^ (-s) := by simp [cpow_one]
    _ = (2 : ℂ) ^ ((1 : ℂ) + (-s)) := (cpow_add (1 : ℂ) (-s) h2).symm
    _ = (2 : ℂ) ^ (1 - s) := by rw [sub_eq_add_neg]

/-- **F1.3b** (forma serie). Si `1 < Re s`,
`η(s) = ζ(s) − 2 · ∑' ((2(n+1))^s)⁻¹`. -/
theorem dirichletEta_eq_zeta_sub_two_mul_even_tsum {s : ℂ} (hs : 1 < s.re) :
    dirichletEta s =
      riemannZeta s - 2 * ∑' n : ℕ, ((2 * (n + 1) : ℂ) ^ s)⁻¹ := by
  rw [dirichletEta_def, tsum_inv_two_mul_nat_add_one_cpow hs, ← mul_assoc,
      two_mul_two_cpow_neg, sub_mul, one_mul]

/-- **F1.3b** (cierre). La forma serie coincide con el factor algebraico:
`ζ − 2·(subsuma par) = (1 − 2^{1−s}) ζ` si `1 < Re s`. -/
theorem zeta_sub_two_mul_even_tsum_eq_mul_zeta {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s - 2 * ∑' n : ℕ, ((2 * (n + 1) : ℂ) ^ s)⁻¹ =
      (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  rw [← dirichletEta_eq_zeta_sub_two_mul_even_tsum hs, dirichletEta_def]


/-! ### F1.3c · η = serie alternada si Re s > 1 -/

/-- **F1.3c.** Si `1 < Re s`,
`η(s) = ∑' (−1)^n (n+1)^{−s}`. -/
theorem dirichletEta_eq_tsum_alternating {s : ℂ} (hs : 1 < s.re) :
    dirichletEta s = ∑' n : ℕ, (-1 : ℂ) ^ n * ((n + 1 : ℂ) ^ s)⁻¹ := by
  set a : ℕ → ℂ := fun n => ((n + 1 : ℂ) ^ s)⁻¹
  have ha : Summable a := summable_inv_nat_add_one_cpow hs
  have he : Summable fun k : ℕ => a (2 * k) :=
    ha.comp_injective (mul_right_injective₀ (two_ne_zero' ℕ))
  have ho : Summable fun k : ℕ => a (2 * k + 1) :=
    ha.comp_injective ((add_left_injective 1).comp (mul_right_injective₀ (two_ne_zero' ℕ)))
  have hζ : riemannZeta s = ∑' n : ℕ, a n := by
    simpa [a, one_div] using zeta_eq_tsum_one_div_nat_add_one_cpow hs
  have hpares :
      (∑' n : ℕ, ((2 * (n + 1) : ℂ) ^ s)⁻¹) = ∑' k : ℕ, a (2 * k + 1) := by
    refine tsum_congr fun n => ?_
    -- ((2(n+1))^s)⁻¹ = a(2n+1) = ((2n+2)^s)⁻¹
    dsimp [a]
    congr 2
    push_cast
    ring
  have hsplit :
      ∑' n : ℕ, a n = (∑' k : ℕ, a (2 * k)) + ∑' k : ℕ, a (2 * k + 1) :=
    (tsum_even_add_odd he ho).symm
  have halt_split :
      (∑' n : ℕ, (-1 : ℂ) ^ n * a n) =
        (∑' k : ℕ, a (2 * k)) - ∑' k : ℕ, a (2 * k + 1) := by
    have heven2 : Even (2 : ℕ) := by decide
    have he' : Summable fun k : ℕ => (-1 : ℂ) ^ (2 * k) * a (2 * k) := by
      convert he using 1
      funext k
      simp [pow_mul, Even.neg_pow heven2]
    have ho' : Summable fun k : ℕ => (-1 : ℂ) ^ (2 * k + 1) * a (2 * k + 1) := by
      convert ho.neg using 1
      funext k
      simp [pow_add, pow_mul, Even.neg_pow heven2, pow_one]
    have h := (tsum_even_add_odd (f := fun n : ℕ => (-1 : ℂ) ^ n * a n) he' ho').symm
    -- ∑ alt = ∑_k (-1)^{2k}a(2k) + ∑_k (-1)^{2k+1}a(2k+1)
    --       = ∑ a(2k) + ∑ (-a(2k+1))
    --       = ∑ a(2k) - ∑ a(2k+1)
    calc
      ∑' n : ℕ, (-1 : ℂ) ^ n * a n
          = (∑' k : ℕ, (-1 : ℂ) ^ (2 * k) * a (2 * k)) +
              ∑' k : ℕ, (-1 : ℂ) ^ (2 * k + 1) * a (2 * k + 1) := h
      _ = (∑' k : ℕ, a (2 * k)) + ∑' k : ℕ, -a (2 * k + 1) := by
            congr 1
            · refine tsum_congr fun k => ?_
              simp [pow_mul, Even.neg_pow heven2]
            · refine tsum_congr fun k => ?_
              simp [pow_add, pow_mul, Even.neg_pow heven2, pow_one]
      _ = (∑' k : ℕ, a (2 * k)) - ∑' k : ℕ, a (2 * k + 1) := by
            rw [sub_eq_add_neg]
            congr 1
            exact ho.hasSum.neg.tsum_eq
  calc
    dirichletEta s
        = riemannZeta s - 2 * ∑' n : ℕ, ((2 * (n + 1) : ℂ) ^ s)⁻¹ :=
          dirichletEta_eq_zeta_sub_two_mul_even_tsum hs
    _ = (∑' n : ℕ, a n) - 2 * ∑' k : ℕ, a (2 * k + 1) := by
          rw [hζ, hpares]
    _ = ((∑' k : ℕ, a (2 * k)) + ∑' k : ℕ, a (2 * k + 1)) -
          2 * ∑' k : ℕ, a (2 * k + 1) := by
          rw [hsplit]
    _ = (∑' k : ℕ, a (2 * k)) - ∑' k : ℕ, a (2 * k + 1) := by
          ring
    _ = ∑' n : ℕ, (-1 : ℂ) ^ n * a n := halt_split.symm
    _ = ∑' n : ℕ, (-1 : ℂ) ^ n * ((n + 1 : ℂ) ^ s)⁻¹ := by
          rfl

/-! ### F1.4 · η holomorfa fuera de s=1 -/

/-- Factor `2^(1−s)` es holomorfo en todo ℂ (base 2 ≠ 0). -/
theorem differentiableAt_two_cpow_one_sub (s : ℂ) :
    DifferentiableAt ℂ (fun z : ℂ => (2 : ℂ) ^ (1 - z)) s :=
  ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id).const_cpow (.inl two_ne_zero)

/-- **F1.4.** `dirichletEta` es holomorfa en todo `s ≠ 1`. -/
theorem differentiableAt_dirichletEta {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ dirichletEta s := by
  have hfac :
      DifferentiableAt ℂ (fun z : ℂ => (1 : ℂ) - (2 : ℂ) ^ (1 - z)) s :=
    (differentiableAt_const (1 : ℂ)).sub (differentiableAt_two_cpow_one_sub s)
  have h := hfac.mul (differentiableAt_riemannZeta hs)
  convert h using 1
  funext z
  simp [dirichletEta, Pi.mul_apply]

theorem differentiableOn_dirichletEta :
    DifferentiableOn ℂ dirichletEta ({1} : Set ℂ)ᶜ :=
  fun _ hs => (differentiableAt_dirichletEta hs).differentiableWithinAt

/-- **F1.4** (forma analítica). η es analítica en el complemento de `{1}`. -/
theorem analyticOn_dirichletEta :
    AnalyticOnNhd ℂ dirichletEta ({1} : Set ℂ)ᶜ :=
  differentiableOn_dirichletEta.analyticOnNhd isOpen_compl_singleton



/-! ### F1.5ℝ-a · Sumabilidad y positividad de la serie alternada real -/

/-- Para σ > 0, la sucesión n ↦ (n + 1)^(-σ) es antítona en ℕ. -/
theorem antitone_nat_inv_rpow {σ : ℝ} (hσ : 0 < σ) :
    Antitone (fun n : ℕ => ((n + 1 : ℝ) ^ σ)⁻¹) := by
  intro a b hab
  have h1 : (0 : ℝ) < (a : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
    linarith
  have hle : (a : ℝ) + 1 ≤ (b : ℝ) + 1 := by
    have : (a : ℝ) ≤ (b : ℝ) := Nat.cast_le.mpr hab
    linarith
  have hpow : ((a : ℝ) + 1) ^ σ ≤ ((b : ℝ) + 1) ^ σ :=
    rpow_le_rpow h1.le hle hσ.le
  exact inv_anti₀ (rpow_pos_of_pos h1 σ) hpow

/-- Para σ > 0, (n + 1)^(-σ) tiende a 0 cuando n → ∞. -/
theorem tendsto_nat_inv_rpow_zero {σ : ℝ} (hσ : 0 < σ) :
    Filter.Tendsto (fun n : ℕ => ((n + 1 : ℝ) ^ σ)⁻¹) Filter.atTop (nhds 0) := by
  have h_rpow : Filter.Tendsto (fun x : ℝ => x ^ (-σ)) Filter.atTop (nhds 0) :=
    tendsto_rpow_neg_atTop hσ
  have h_nat : Filter.Tendsto (fun n : ℕ => (n : ℝ) + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono
      (fun n => le_add_of_nonneg_right zero_le_one)
      tendsto_natCast_atTop_atTop
  have h_comp := h_rpow.comp h_nat
  refine h_comp.congr (fun n => ?_)
  dsimp
  have hpos : (0 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  rw [rpow_neg hpos, inv_eq_one_div]

/-- **F1.5ℝ-a.** La serie alternada ∑ (-1)^n (n+1)^(-σ) converge en ℝ para todo σ > 0. -/
theorem exists_tendsto_alternating_series_real {σ : ℝ} (hσ : 0 < σ) :
    ∃ l : ℝ, Filter.Tendsto
      (fun n ↦ ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * ((i + 1 : ℝ) ^ σ)⁻¹)
      Filter.atTop (nhds l) := by
  have h_anti := antitone_nat_inv_rpow hσ
  have h_zero := tendsto_nat_inv_rpow_zero hσ
  exact h_anti.tendsto_alternating_series_of_tendsto_zero h_zero

/-- Para todo σ > 0, el límite de la serie alternada es estrictamente positivo. -/
theorem alternating_series_real_pos {σ : ℝ} (hσ : 0 < σ) {l : ℝ}
    (hl : Filter.Tendsto
      (fun n ↦ ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * ((i + 1 : ℝ) ^ σ)⁻¹)
      Filter.atTop (nhds l)) :
    0 < l := by
  have h_anti := antitone_nat_inv_rpow hσ
  have h_bound := h_anti.alternating_series_le_tendsto hl 1
  have h_sum2 : (∑ i ∈ Finset.range (2 * 1), (-1 : ℝ) ^ i * ((i + 1 : ℝ) ^ σ)⁻¹) =
      1 - (2 : ℝ) ^ (-σ) := by
    rw [show 2 * 1 = 2 by rfl, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    simp only [pow_zero, CharP.cast_eq_zero, zero_add, pow_one, Nat.cast_one, neg_one_mul]
    rw [Real.one_rpow, inv_one]
    have h2pos : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
    rw [rpow_neg h2pos, inv_eq_one_div]
    ring_nf
  rw [h_sum2] at h_bound
  have h2pos : 0 < 1 - (2 : ℝ) ^ (-σ) := by
    have : (2 : ℝ) ^ (-σ) < 1 := by
      rw [← Real.rpow_zero (2 : ℝ)]
      exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) (by linarith)
    linarith
  exact lt_of_lt_of_le h2pos h_bound

/-- **F1.6.** If `dirichletEta` agrees with the alternating series limit on `(0, 1)`,
then `riemannZeta` does not vanish on `(0, 1)`. -/
theorem riemannZeta_ne_zero_of_dirichletEta_eq_alternating
    {σ : ℝ} (hσ : σ ∈ Ioo (0 : ℝ) 1) {l : ℝ}
    (hl : Filter.Tendsto
      (fun n ↦ ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * ((i + 1 : ℝ) ^ σ)⁻¹)
      Filter.atTop (nhds l))
    (heta : dirichletEta (σ : ℂ) = (l : ℂ)) :
    riemannZeta (σ : ℂ) ≠ 0 := by
  have hl_pos : 0 < l := alternating_series_real_pos hσ.1 hl
  have hl_cpos : (l : ℂ) ≠ 0 := by
    intro h0
    have : (l : ℂ).re = 0 := by rw [h0, Complex.zero_re]
    simp only [Complex.ofReal_re] at this
    linarith
  have heta_ne : dirichletEta (σ : ℂ) ≠ 0 := by
    rw [heta]
    exact hl_cpos
  have _hfac_ne : 1 - (2 : ℂ) ^ (1 - (σ : ℂ)) ≠ 0 :=
    one_sub_two_cpow_one_sub_ne_zero_of_mem_Ioo hσ
  unfold dirichletEta at heta_ne
  intro hz
  rw [hz, mul_zero] at heta_ne
  exact heta_ne rfl

end RhG1Lean

