/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under CC-BY 4.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Normed.Group.Basic
import RhG1Lean.KroneckerMismatch
import RhG1Lean.DualCancellation
import RhG1Lean.StripReduction

/-!
# Boca A Dual Cancellation

Geometric and operator framework for dual channel cancellation and amplitude mismatch in Boca A.
-/

set_option linter.style.longLine false

open Complex Real Finset

namespace RhG1Lean

/-- The unitary phase wave for angle $\theta \in \mathbb{R}$. -/
noncomputable def channelWave (θ : ℝ) : ℂ :=
  Complex.exp (θ * I)

@[simp]
theorem norm_channelWave (θ : ℝ) : ‖channelWave θ‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem channelWave_zero : channelWave 0 = 1 := by
  simp [channelWave]

theorem channelWave_add (θ₁ θ₂ : ℝ) :
    channelWave (θ₁ + θ₂) = channelWave θ₁ * channelWave θ₂ := by
  unfold channelWave
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The aligned frame rotation operator by angle $\psi \in \mathbb{R}$. -/
noncomputable def alignedFrame (ψ : ℝ) (z : ℂ) : ℂ :=
  channelWave ψ * z

@[simp]
theorem alignedFrame_zero (z : ℂ) : alignedFrame 0 z = z := by
  simp [alignedFrame]

@[simp]
theorem norm_alignedFrame (ψ : ℝ) (z : ℂ) : ‖alignedFrame ψ z‖ = ‖z‖ := by
  unfold alignedFrame
  rw [norm_mul, norm_channelWave, one_mul]

@[simp]
theorem alignedFrame_eq_zero_iff (ψ : ℝ) (z : ℂ) : alignedFrame ψ z = 0 ↔ z = 0 := by
  unfold alignedFrame
  have hexp : channelWave ψ ≠ 0 := by
    intro hz
    have := norm_channelWave ψ
    rw [hz, norm_zero] at this
    norm_num at this
  constructor
  · intro h
    cases mul_eq_zero.mp h with
    | inl h1 => exact (hexp h1).elim
    | inr h2 => exact h2
  · intro h
    rw [h, mul_zero]

theorem ofReal_cos_im (x : ℝ) : (Complex.cos (x : ℂ)).im = 0 := by
  rw [← Complex.ofReal_cos]
  exact Complex.ofReal_im (Real.cos x)

theorem dual_channel_balanced_factorization (ψ θ : ℝ) :
    channelWave (-θ) + channelWave (-2 * ψ + θ) =
      2 * channelWave (-ψ) * (Complex.cos (((ψ - θ : ℝ) : ℂ))) := by
  unfold channelWave
  have hcos : Complex.cos (((ψ - θ : ℝ) : ℂ)) =
      (Complex.exp (((ψ - θ : ℝ) : ℂ) * I) + Complex.exp (-(((ψ - θ : ℝ) : ℂ)) * I)) / 2 := by
    unfold Complex.cos
    rfl
  rw [hcos]
  have hneg_psi : ((-ψ : ℝ) : ℂ) = - (ψ : ℂ) := by simp
  have htwo : (2 : ℂ) * Complex.exp (((-ψ : ℝ) : ℂ) * I) *
      ((Complex.exp (((ψ - θ : ℝ) : ℂ) * I) + Complex.exp (-(((ψ - θ : ℝ) : ℂ)) * I)) / 2) =
      Complex.exp (((-ψ : ℝ) : ℂ) * I) * Complex.exp (((ψ - θ : ℝ) : ℂ) * I) +
      Complex.exp (((-ψ : ℝ) : ℂ) * I) * Complex.exp (-(((ψ - θ : ℝ) : ℂ)) * I) := by ring
  rw [htwo]
  have h1 : Complex.exp (((-ψ : ℝ) : ℂ) * I) * Complex.exp (((ψ - θ : ℝ) : ℂ) * I) = Complex.exp (((-θ : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have h2 : Complex.exp (((-ψ : ℝ) : ℂ) * I) * Complex.exp (-(((ψ - θ : ℝ) : ℂ)) * I) =
      Complex.exp (((-2 * ψ + θ : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [h1, h2]

theorem aligned_frame_dual_channel_balanced (ψ θ : ℝ) :
    alignedFrame ψ (channelWave (-θ) + channelWave (-2 * ψ + θ)) =
      2 * Complex.cos (((ψ - θ : ℝ) : ℂ)) := by
  unfold alignedFrame
  rw [dual_channel_balanced_factorization ψ θ]
  unfold channelWave
  have hneg_psi : ((-ψ : ℝ) : ℂ) = - (ψ : ℂ) := by simp
  calc Complex.exp ((ψ : ℂ) * I) * (2 * Complex.exp (((-ψ : ℝ) : ℂ) * I) * Complex.cos (((ψ - θ : ℝ) : ℂ)))
      = 2 * (Complex.exp ((ψ : ℂ) * I) * Complex.exp (((-ψ : ℝ) : ℂ) * I)) * Complex.cos (((ψ - θ : ℝ) : ℂ)) := by ring
    _ = 2 * Complex.exp ((ψ : ℂ) * I + ((-ψ : ℝ) : ℂ) * I) * Complex.cos (((ψ - θ : ℝ) : ℂ)) := by rw [← Complex.exp_add]
    _ = 2 * Complex.exp 0 * Complex.cos (((ψ - θ : ℝ) : ℂ)) := by
          congr 2
          push_cast
          ring_nf
    _ = 2 * 1 * Complex.cos (((ψ - θ : ℝ) : ℂ)) := by rw [Complex.exp_zero]
    _ = 2 * Complex.cos (((ψ - θ : ℝ) : ℂ)) := by ring

theorem aligned_frame_dual_channel_balanced_im_zero (ψ θ : ℝ) :
    (alignedFrame ψ (channelWave (-θ) + channelWave (-2 * ψ + θ))).im = 0 := by
  rw [aligned_frame_dual_channel_balanced]
  have : (2 * Complex.cos (((ψ - θ : ℝ) : ℂ))).im = 2 * (Complex.cos (((ψ - θ : ℝ) : ℂ))).im := by simp
  rw [this, ofReal_cos_im (ψ - θ), mul_zero]

theorem sum_channels_ne_zero_of_leader_dominant {ι E : Type*} [DecidableEq ι]
    [SeminormedAddCommGroup E] (s : Finset ι) (k_star : ι) (hk : k_star ∈ s)
    (v : ι → E) (R : E)
    (hdom : ‖R‖ + ∑ k ∈ s.erase k_star, ‖v k‖ < ‖v k_star‖) :
    (∑ k ∈ s, v k) + R ≠ 0 := by
  intro hsum
  have hsplit : (∑ k ∈ s, v k) = v k_star + ∑ k ∈ s.erase k_star, v k :=
    (Finset.add_sum_erase s v hk).symm
  rw [hsplit] at hsum
  have heq : v k_star = - ((∑ k ∈ s.erase k_star, v k) + R) := by
    calc v k_star = (v k_star + (∑ k ∈ s.erase k_star, v k) + R) - ((∑ k ∈ s.erase k_star, v k) + R) := by abel
      _ = 0 - ((∑ k ∈ s.erase k_star, v k) + R) := by rw [hsum]
      _ = - ((∑ k ∈ s.erase k_star, v k) + R) := by simp
  have hnorm : ‖v k_star‖ = ‖(∑ k ∈ s.erase k_star, v k) + R‖ := by
    rw [heq, norm_neg]
  have htri : ‖(∑ k ∈ s.erase k_star, v k) + R‖ ≤ (∑ k ∈ s.erase k_star, ‖v k‖) + ‖R‖ := by
    have h1 := norm_add_le (∑ k ∈ s.erase k_star, v k) R
    have h2 := norm_sum_le (s.erase k_star) v
    linarith
  linarith

theorem asymmetric_dual_pair_norm_lower_bound (A₁ A₂ : ℝ) (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (ψ θ : ℝ) :
    |A₁ - A₂| ≤ ‖(A₁ : ℂ) * channelWave (-θ) + (A₂ : ℂ) * channelWave (-2 * ψ + θ)‖ := by
  set v₁ := (A₁ : ℂ) * channelWave (-θ)
  set v₂ := (A₂ : ℂ) * channelWave (-2 * ψ + θ)
  have hnorm₁ : ‖v₁‖ = A₁ := by
    dsimp [v₁]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA₁,
        norm_channelWave, mul_one]
  have hnorm₂ : ‖v₂‖ = A₂ := by
    dsimp [v₂]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA₂,
        norm_channelWave, mul_one]
  have htri := norm_sub_norm_le v₁ (-v₂)
  rw [norm_neg, hnorm₁, hnorm₂] at htri
  have heq : v₁ - (-v₂) = v₁ + v₂ := sub_neg_eq_add v₁ v₂
  rw [heq] at htri
  have htri' := norm_sub_norm_le (-v₂) v₁
  rw [norm_neg, hnorm₁, hnorm₂] at htri'
  have heq' : -v₂ - v₁ = -(v₁ + v₂) := by abel
  rw [heq', norm_neg] at htri'
  rw [abs_le]
  constructor <;> linarith

theorem asymmetric_dual_pair_ne_zero {A₁ A₂ : ℝ} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (hne : A₁ ≠ A₂) (ψ θ : ℝ) :
    (A₁ : ℂ) * channelWave (-θ) + (A₂ : ℂ) * channelWave (-2 * ψ + θ) ≠ 0 := by
  intro hzero
  have hle := asymmetric_dual_pair_norm_lower_bound A₁ A₂ hA₁ hA₂ ψ θ
  rw [hzero, norm_zero] at hle
  have : |A₁ - A₂| = 0 := by linarith [abs_nonneg (A₁ - A₂)]
  have : A₁ - A₂ = 0 := abs_eq_zero.mp this
  exact hne (sub_eq_zero.mp this)

theorem strictMono_zero_ne_zero {f : ℝ → ℝ} (hmono : StrictMono f) (h0 : f 0 = 0)
    {δ : ℝ} (hδ : δ ≠ 0) : f δ ≠ 0 := by
  rcases lt_or_gt_of_ne hδ with hlt | hgt
  · have : f δ < f 0 := hmono hlt
    rw [h0] at this
    exact ne_of_lt this
  · have : f 0 < f δ := hmono hgt
    rw [h0] at this
    exact ne_of_gt this

end RhG1Lean
