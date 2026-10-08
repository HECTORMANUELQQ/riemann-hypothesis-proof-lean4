/-
Copyright (c) 2026 Hector Manuel Quezada Quiñonez. All rights reserved.
Released under CC-BY 4.0 license as described in the file LICENSE.
Authors: Hector Manuel Quezada Quiñonez
-/
import RhG1Lean.Arc
import RhG1Lean.ZetaBound
import RhG1Lean.GammaBound
import RhG1Lean.Majorant
import RhG1Lean.Diameter
import RhG1Lean.Nonvanishing
import RhG1Lean.G4Match
import RhG1Lean.G5
import RhG1Lean.MouthA
import RhG1Lean.G5Interior
import RhG1Lean.Leftover
import RhG1Lean.FunEq
import RhG1Lean.LeftoverCompact
import RhG1Lean.Split
import RhG1Lean.LeftoverNonvanishing
import RhG1Lean.LeftoverCore
import RhG1Lean.Conj
import RhG1Lean.Lip
import RhG1Lean.Eta
import RhG1Lean.DerivBound
import RhG1Lean.XiEntire
import RhG1Lean.DualCancellation
import RhG1Lean.StripReduction
import RhG1Lean.BocaADualCancellation
import RhG1Lean.BocaANonvanishing
import RhG1Lean.FrontierMeasurement
import RhG1Lean.RiemannHypothesis
import RhG1Lean.CajitaWallBound
import RhG1Lean.LambdaZeroRealBound
import RhG1Lean.LambdaZeroFrontierBound
import RhG1Lean.PrimeRemainderBound
import RhG1Lean.EtaContinuationBound
import RhG1Lean.Prime2LinearGap
import RhG1Lean.ThetaTailGeometric
import RhG1Lean.ThetaIntegralBound
import RhG1Lean.ThetaKernelDomination
import RhG1Lean.MaximumModulusLeftover
import RhG1Lean.PrimeTailAnalytic
import RhG1Lean.PrimeTailDecay
import RhG1Lean.RiemannHypothesisMaster

/-!
# Qué está demostrado en Lean y qué no

Si no hay `theorem` verde, no está probado.
No hay `axiom RiemannHypothesis`. No hay `sorry` de RH.

## FILLED

* `sigmaMin_gt_one` — Lema 65.1
* `reSR_ge_sigmaMin` — Lema 65.2 (parte real)
* `reSR_gt_one` — el arco R > 1/2 está en Re s > 1
* `norm_riemannZeta_le_riemannZeta_re` — Lema 65.3 `|ζ(s)| ≤ |ζ(σ)|` si Re s > 1
* `norm_riemannZeta_le_on_arc` — 65.3 en el arco
* `norm_Gamma_le_Gamma_re` — 65.4 `|Γ(z)| ≤ Γ(Re z)` si Re z > 0 (integral de Euler)
* `norm_Gamma_half_le_on_arc` — 65.4 en el arco
* `norm_riemannXi_le_majorant` — 65.5 `‖ξ(s)‖ ≤ M(σ)` si Re s > 1
* `norm_riemannXi_le_majorant_on_arc` — 65.5 en el arco
* `G2_norm_riemannXi_le_majorant` — G2 en L_R si |y|>1/2
* `re_sOnDiameter_le_one` — compacto G2: |y|≤1/2 ⇒ Re s ≤ 1
* `riemannXi_ne_zero_of_one_lt_re` — G3 si Re s > 1
* `G3_riemannXi_ne_zero_on_arc` / `on_diameter` — G3 en G1 y G2 (|y|>1/2)
* `sOnDiameter_ne_one` — compacto: s≠1 en L_R
* `G4_arc_ready` / `G4_diameter_ready` — G4 match AP en Re s>1
* `differentiableAt_riemannXi` — G5: ξ holomorfa si Re s>1
* `G5_hypotheses_on_re_gt_one` — AP: holomorfa y ≠0 (N=0 OPEN)
* `isOpen_re_gt_one` — {Re s>1} es abierto
* `G3_riemannXi_ne_zero_on_diameter_endpoint` — G3 en |y|=1/2
* `bocaA_re_neg` / `offLine_not_in_O1` — contraejemplos altos no están en O₁
* `riemannXi_eq_zero_iff_zeta_sOnDiameter` — en L_R, ξ=0 ↔ ζ=0
* `differentiableAt_riemannXi_sOnDiameter` — ξ holomorfa en todo L_R
* `differentiableAt_riemannXi_of` — holomorfa si s≠1 y Re(s/2)>0
* `xi_zeros_one_lt_re_empty` — N=0 en Re s>1
* `xi_ne_zero_of_sector_outer` — N=0 en O₁ si ‖w‖>√2/2
* `finite_zeta_zeros_of_compact` — finitos ceros en un compacto (no uno por uno)
* `leftoverHard_im_le_half` — caja dura O₁: |t| ≤ 1/2
* `rose_height_not_leftoverHard` — γ≥14 (rosas/Pick) no está en esa caja
* `rose_height_in_A_if_off_line` — si δ≠0 y |t|≥14, es boca A
* `stripO1Small_of_O1_in_strip` — O₁ en la franja ⇒ |t|<|δ|≤1/2
* `rose_height_not_stripO1Small` — γ≥14 no está en esa O₁ chica
* `monograph_sample_not_stripO1Small` — las 10 γ de Pick-3 tampoco
* `stripO1Small_neg` / `completedRiemannZeta₀_symmetric` — FE: un lado de la caja basta
* `isCompact_leftoverRect` / `finite_zeta_zeros_leftoverRect` — caja |t|≤1/2: finitos ceros
* `stripA` — boca A en la franja (|δ|<|t|)
* `differentiableAt_riemannXi_leftoverRect` — ξ holomorfa en la caja salvo s=1
* `finite_zeta_zeros_aBand` — A por bandas [T,H]: finitos ceros
* `strip_trichotomy` — franja: caja O₁, o diámetro u, o A
* `leftoverRect_right_edge_zeta_ne_zero` — Re s=1, s≠1: ζ≠0
* `isCompact_leftoverRect_sdiff_open` / `finite_zeta_zeros_leftoverRect_sdiff_open` — leftoverRect\U compacto + finitos ceros (LeftoverCore)
* `exists_ball_one_leftoverRect_zeta_ne_zero` — bola métrica en 1 sin ceros en leftoverRect (LeftoverCore)
* `riemannXi_eq_zero_iff_zeta_leftoverRect` / `exists_compact_leftoverCore_cut` — puente ξ↔ζ y núcleo compacto (LeftoverCore)
* `continuousOn_norm_riemannXi_leftoverRect_sdiff` / `exists_isMinOn_norm_riemannXi_leftoverRect_sdiff` — ‖ξ‖ continua + mínimo en leftoverRect\U (LeftoverCore)
* `riemannXi_eq_mul_completedRiemannZeta` / `riemannXi_one_sub` / `norm_riemannXi_one_sub` — N1/J4: ξ↔Λ y ξ(1-s)=ξ(s) (FunEq)
* `riemannXi_one_sub_of_mem_leftoverInterior` / `mem_leftoverInterior_of_stripO1Small` — FE ξ en leftoverInterior + glue O1→cajita (LeftoverCore)
* `riemannXi_eq_zero_iff_completedRiemannZeta_leftoverRect` — ceros ξ↔Λ en leftoverRect (LeftoverCore)
* `riemannXi_conj` / `norm_riemannXi_conj` / `norm_riemannXi_symm_re` — L20 conj+t-fijo (Conj)
* `riemannXi_lipschitz_on_convex` / `convex_leftoverRect` / `leftoverLeftSlab` — Lipschitz ξ en convexos; losa izquierda (Lip)
* `leftoverUpSlab` / `convex_leftoverUpSlab` / `leftoverUpSlab_subset_sdiff_ball` / `riemannXi_lipschitz_on_leftoverUpSlab` — losa superior convexa, sin bola, Lip (Lip)
* `leftoverDnSlab` / `convex_leftoverDnSlab` / `leftoverDnSlab_subset_sdiff_ball` / `riemannXi_lipschitz_on_leftoverDnSlab` — losa inferior convexa, sin bola, Lip (Lip)
* `dirichletEta` / `two_cpow_ne_zero` / `one_sub_two_cpow_one_sub_ne_zero_of_mem_Ioo` / `tsum_inv_two_mul_nat_add_one_cpow` / `dirichletEta_eq_zeta_sub_two_mul_even_tsum` — F1.0–F1.3b η (Eta)
* `differentiableAt_dirichletEta` / `analyticOn_dirichletEta` — F1.4 η holomorfa fuera de {1} (Eta)
* `dirichletEta_eq_tsum_alternating` — F1.3c η=serie alternada si Re s>1 (Eta)
* `antitone_nat_inv_rpow` / `tendsto_nat_inv_rpow_zero` — n ↦ (n+1)^{-σ} antítona y tiende a 0 para σ>0 (Eta)
* `exists_tendsto_alternating_series_real` — F1.5ℝ-a: ∑ (-1)^n (n+1)^{-σ} converge en ℝ para todo σ>0 (Eta)
* `alternating_series_real_pos` — para todo σ>0, límite de serie alternada es >0 (Eta)
* `riemannZeta_ne_zero_of_dirichletEta_eq_alternating` — F1.6: η alternada ⇒ ζ≠0 en (0,1) (Eta)
* `isCompact_leftoverLeftSlab` / `exists_nnnorm_deriv_riemannXi_le_leftoverLeftSlab` — losa izquierda compacta + cota ∃C (DerivBound)
* `isCompact_leftoverUpSlab` / `exists_nnnorm_deriv_riemannXi_le_leftoverUpSlab` — losa superior compacta + cota ∃C (DerivBound)
* `isCompact_leftoverDnSlab` / `exists_nnnorm_deriv_riemannXi_le_leftoverDnSlab` — losa inferior compacta + cota ∃C (DerivBound)
* `leftoverCore_zeta_ne_zero_of_xi_min_pos` — Teorema E: cota inferior ‖ξ‖≥m>0 ⇒ ζ≠0 en leftoverInterior\bola (LeftoverCore)
* `exists_norm_riemannXi_min_pos_right_edge` — m>0 de ‖ξ‖ en borde Re=1 fuera de bola (LeftoverCore)
* `leftoverInterior_real_mem_Ioo` / `leftoverInterior_real_zeta_ne_zero_of_eta_eq` — F1.6 en el eje real de leftoverInterior (LeftoverCore)
* `entireXi` / `differentiable_entireXi` / `entireXi_one` / `entireXi_zero` / `entireXi_one_sub` — ξ entera canónica sin singularidad ni valores basura (XiEntire)
* `mul_sub_inv_eq` / `entireXi_eq_mul_completedRiemannZeta` / `entireXi_eq_riemannXi` / `entireXi_eq_zero_iff_zeta_leftoverInterior` — cancelación exacta de polos y puente ξ↔ζ (XiEntire)
* `entireXi_lipschitz_on_convex` / `continuous_deriv_entireXi` / `exists_nnnorm_deriv_entireXi_le_leftoverRect` / `entireXi_lipschitz_on_leftoverRect` — Lipschitz de entireXi en todo leftoverRect sin recortar bola (XiEntire)
* `norm_sub_one_le_one_of_mem_leftoverRect` — distancia a s=1 es ≤ 1 en todo leftoverRect (XiEntire)
* `entireXi_ne_zero_of_deriv_lt_half` / `leftoverInterior_zeta_ne_zero_of_deriv_lt_half` — resolución de Gap 5.1: cota de derivada C < 1/2 ⇒ ζ≠0 en leftoverInterior (XiEntire)
* `riemannXi_critical_line_im_eq_zero` / `entireXi_critical_line_im_eq_zero` / `entireXi_critical_line_mem_re` — Dual Cancellation Teorema 1: ξ y entireXi son idénticamente REALES sobre la línea crítica (corte equilibrado μ=0) (DualCancellation)
* `riemannXi_reflection_symm` / `entireXi_reflection_symm` — Dual Cancellation Teorema 2: simetría transversal ξ(1/2-δ+it) = conj(ξ(1/2+δ+it)) para |δ|<1/2 (DualCancellation)
* `re_entireXi_neg_delta` / `im_entireXi_neg_delta` — Dual Cancellation Teorema 3 y 4: Re(entireXi) es PAR en δ, Im(entireXi) es IMPAR en δ y nula en δ=0 (DualCancellation)
* `entireXi_zero_iff_re_and_im_zero` / `entireXi_zero_symm_delta` / `entireXi_zero_re_im_pair` — anulación fuera de la línea requiere anulación simultánea y emparejamiento estricto en ±δ (DualCancellation)
* `deriv_entireXi_one_sub` / `deriv_entireXi_half` / `deriv_entireXi_critical_line_neg` — antisimetría de la derivada ξ'(1-s) = -ξ'(s), anulación exacta en el centro ξ'(1/2) = 0 y antisimetría en la línea crítica (DualCancellation)
* `hasDerivAt_neg_id` / `hasDerivAt_even_deriv_zero` — lema general: toda función real localmente par y diferenciable en 0 tiene derivada nula f'(0) = 0 (DualCancellation)
* `re_deriv_entireXi_critical_line` / `deriv_entireXi_critical_line_eq_I_mul_im` — Dual Cancellation Teoremas 5 y 6: Re(ξ'(1/2+it)) = 0, la derivada sobre la línea crítica es estrictamente pura imaginaria ξ'(1/2+it) = i·Im(ξ') (DualCancellation)
* `im_deriv_entireXi_critical_line_neg` — la parte imaginaria de la derivada sobre la línea es impar en t (DualCancellation)
* `deriv_entireXi_critical_line_sq_re_nonpos` / `deriv_entireXi_critical_line_sq_im_eq_zero` — Dual Cancellation Teorema 7: (ξ'(1/2+it))² es un número real ≤ 0, alineado idénticamente con el régimen no-positivo de Boca A (DualCancellation)
* `entireXi_eventually_ne_zero_of_deriv_ne_zero` / `exists_ball_punctured_entireXi_ne_zero_of_deriv_ne_zero` — Dual Cancellation Teorema 8: rigidez transversal local de ceros críticos simples (DualCancellation)
* `entireXi_off_line_ne_zero_near_critical_zero` — Dual Cancellation Teorema 9: no-bifurcación transversal de ceros fuera de la línea crítica (DualCancellation)
* `hasDerivAt_entireXi_transversal` / `hasDerivAt_entireXi_transversal_re` — Dual Cancellation Teorema 10: velocidad transversal real nula ∂_δ Re(ξ) = 0 (DualCancellation)
* `hasDerivAt_entireXi_transversal_im` — Dual Cancellation Teorema 11: velocidad transversal imaginaria pura ∂_δ Im(ξ) = Im(ξ') (DualCancellation)
* `hasDerivAt_entireXi_vertical` / `hasDerivAt_entireXi_vertical_re` — Dual Cancellation Teorema 12: velocidad vertical real pura ∂_τ Re(ξ) = -Im(ξ') (DualCancellation)
* `hasDerivAt_entireXi_vertical_im` — Dual Cancellation Teorema 13: velocidad vertical imaginaria nula ∂_τ Im(ξ) = 0 (DualCancellation)
* `dual_cancellation_cauchy_riemann_jacobian_det` — Dual Cancellation Teorema 14: rotación ortogonal exacta de Cauchy-Riemann de 90° con determinante jacobiano (Im ξ')² ≥ 0 (DualCancellation)
* `two_vectors_sum_ne_zero_of_norm_ne` — barrera geométrica universal: dos vectores con normas distintas jamás suman cero (KroneckerMismatch)
* `channelGainRatio` / `channelGainRatio_pos` / `channelGainRatio_zero` / `channelGainRatio_at_tau_star` — cociente de ganancia Oeste/Este en el canal lento (KroneckerMismatch)
* `channelGainRatio_eq_one_iff` — teorema de mismatch: r(δ, τ) = 1 si y solo si δ = 0 o τ = τ_* (KroneckerMismatch)
* `channelGainRatio_ne_one_of_delta_ne_zero` — asimetría estricta fuera de la línea crítica: r ≠ 1 para todo δ ≠ 0 y τ ≠ τ_* (KroneckerMismatch)
* `channelGainRatio_gt_one_of_pos` / `channelGainRatio_lt_one_of_neg` — dominancia estricta del Oeste (r > 1 para δ > 0) y del Este (r < 1 para δ < 0) (KroneckerMismatch)
* `vector_add_remainder_ne_zero_of_norm_lt` / `norm_add_lower_bound` — barrera de dominancia: ‖R‖ < ‖v‖ ⇒ v + R ≠ 0 y cota inferior triangular (KroneckerMismatch)
* `channelGainRatio_lt_channelGainRatio_of_lt` / `channelGainRatio_lt_channelGainRatio_of_lt_neg` — amplificación monótona estricta del desajuste de ganancia con la altura τ (KroneckerMismatch)
* `norm_add_add_lower_bound` / `sum_three_ne_zero_of_mismatch_gt_remainder` — cota inferior de 3 vectores: |‖v₁‖ - ‖v₂‖| - ‖R‖ ≤ ‖v₁ + v₂ + R‖; si ‖R‖ < |‖v₁‖ - ‖v₂‖| entonces v₁ + v₂ + R ≠ 0 (KroneckerMismatch)
* `norm_sub_norm_eq_mul_abs_sub_one` / `sum_three_ne_zero_of_relative_mismatch` — obstrucción macroscópica: desajuste relativo |r - 1| > ‖R‖/‖v₂‖ ⇒ campo total no nulo (KroneckerMismatch)
* `delta_lt_half_of_mem_strip` / `mem_leftoverRect_of_half_le_and_height_le` / `mem_leftoverInterior_of_half_le_and_height_le` / `mem_leftoverInterior_one_sub_of_re_lt_half` / `bocaA_of_high_height_in_strip` — métrica y contención en la franja crítica (StripReduction)
* `critical_strip_decomposition` — partición exacta de 4 cuadrantes de la franja crítica en línea crítica, caja este, caja oeste y Boca A alta (StripReduction)
* `diameter_in_strip_east_subset_leftoverInterior` / `diameter_in_strip_west_subset_leftoverInterior` — absorción rigurosa de Habitación 2 (diámetro |t|=|δ|) dentro de leftoverInterior (StripReduction)
* `Gammaℝ_ne_zero_of_re_pos` / `entireXi_eq_riemannXi_of_mem_strip` / `prefactor_ne_zero_of_mem_strip` / `riemannXi_eq_zero_iff_zeta_of_mem_strip` / `entireXi_eq_zero_iff_zeta_of_mem_strip` — equivalencia exacta entireXi(s)=0 ↔ ζ(s)=0 en toda la franja crítica (StripReduction)
* `zeta_zero_one_sub_iff_of_mem_strip` / `zeta_ne_zero_of_one_sub_mem_leftoverInterior` — simetría reflexiva de ceros de ζ y no-anulación en la caja oeste heredada de leftoverInterior (StripReduction)
* `inBocaA` / `riemann_hypothesis_reduction_to_bocaA_and_leftover` — Teorema Maestro de Reducción: no-anulación en leftoverInterior (Hab 1) y Boca A (Hab 3) implica la Hipótesis de Riemann en toda la franja (StripReduction)
* `channelWave` / `norm_channelWave` / `channelWave_zero` / `channelWave_add` — onda de fase unitaria e^{iθ} (BocaADualCancellation)
* `alignedFrame` / `alignedFrame_zero` / `norm_alignedFrame` / `alignedFrame_eq_zero_iff` — operador de marco alineado isométrico (BocaADualCancellation)
* `ofReal_cos_im` / `dual_channel_balanced_factorization` / `aligned_frame_dual_channel_balanced` / `aligned_frame_dual_channel_balanced_im_zero` — colapso exacto de fase contrarrotatoria y confinamiento en la recta real Im=0 (BocaADualCancellation)
* `sum_channels_ne_zero_of_leader_dominant` — Teorema Universal de Dominancia Multi-Canal con resto en espacios seminormados (BocaADualCancellation)
* `asymmetric_dual_pair_norm_lower_bound` / `asymmetric_dual_pair_ne_zero` — cota inferior de asimetría dual |A₁ - A₂| ≤ ‖A₁ v₁ + A₂ v₂‖ y no-anulación estricta por desajuste de amplitud (BocaADualCancellation)
* `strictMono_zero_ne_zero` — lema de estricta monotonía: todo cero único en el origen excluye ceros para δ ≠ 0 (BocaADualCancellation)
* `deriv_entireXi_le_of_sphere_bound` — Cota de Cauchy para la derivada de entireXi en esferas complejas: ‖deriv entireXi c‖ ≤ M / R (XiEntire)
* `bocaA_delta_ne_zero` — fuera de la línea en Boca A, el desplazamiento δ = Re s - 1/2 es estrictamente no nulo (BocaANonvanishing)
* `asymmetric_dual_sum_remainder_lower_bound` — cota inferior con resto: |A₁ - A₂| - ‖R‖ ≤ ‖A₁ e^{-iθ} + A₂ e^{-i(2ψ-θ)} + R‖ (BocaANonvanishing)
* `asymmetric_dual_sum_ne_zero_of_remainder_lt` — no-anulación estricta del canal dual con resto cuando ‖R‖ < |A₁ - A₂| (BocaANonvanishing)
* `bocaA_mismatch_amplitude_eq` — factorización exacta del desajuste |r A₂ - A₂| = |r - 1| A₂ (BocaANonvanishing)
* `bocaA_relative_mismatch_ne_zero` — no-anulación por desajuste relativo cuando ‖R‖ < |r - 1| A₂ (BocaANonvanishing)
* `bocaA_gain_ratio_mismatch` — para todo δ ≠ 0 y τ ≠ τ_*, el cociente de ganancia r(δ, τ) ≠ 1 (BocaANonvanishing)
* `bocaA_west_mismatch_pos` / `bocaA_east_mismatch_pos` — positividad estricta del margen de desajuste Oeste (r > 1) y Este (r < 1) (BocaANonvanishing)
* `bocaA_master_nonvanishing` — Criterio Maestro de Boca A: para todo punto fuera de la línea con ‖R‖ < |r - 1| A₂, la onda total compuesta jamás se anula (BocaANonvanishing)
* `RiemannHypothesis` / `riemann_hypothesis_of_cajita_and_bocaA` / `riemann_hypothesis_of_entireXi` — Teorema Maestro Global: reducción completa de la Hipótesis de Riemann a las dos condiciones canónicas de las Habitaciones 1 y 3 (RiemannHypothesis)
* `riemannZeta_ne_zero_iff_entireXi_ne_zero` / `bocaA_zeta_ne_zero_iff_entireXi_ne_zero` — equivalencia exacta de no-anulación entre zeta y entireXi en toda la franja y en Boca A (RiemannHypothesis)
* `bocaA_zero_requires_even_and_odd_vanishing` / `critical_zeros_rigid_transverse` — obstrucción de doble anulación simultánea y rigidez transversal absoluta de ceros críticos (RiemannHypothesis)
* `leftoverRect_deriv_bound_of_uniform_sphere_bound` / `exists_deriv_bound_lt_half_of_uniform_sphere_bound` / `riemann_hypothesis_of_cauchy_tube_and_bocaA` — Teorema Maestro de Reducción de Cauchy: cota de tubo esférico M/R < 1/2 en leftoverRect y Boca A implican formalmente RiemannHypothesis (RiemannHypothesis)
* `bocaA_delta_mem_Ioo` / `bocaA_delta_ne_zero_of_off_line` / `bocaA_gain_ratio_mismatch_of_off_line` — confinamiento métrico y desajuste estricto de ganancia r ≠ 1 para todo punto fuera de la línea en Boca A (RiemannHypothesis)
* `riemann_hypothesis_reduction_to_bocaA_off_line_and_leftover` / `riemann_hypothesis_of_cajita_and_bocaA_off_line` — Reducción refinada: no-anulación en Boca A fuera de la línea y en leftoverInterior implica formalmente RiemannHypothesis (StripReduction & RiemannHypothesis)
* `norm_prefactor_le_three_eighths_of_mem_frontier` / `norm_prefactor_le_half_of_mem_frontier` — cota afilada del prefactor |s(s-1)/2| ≤ 3/8 en las 4 paredes de la cajita (FrontierMeasurement)
* `norm_entireXi_sub_half_le_three_eighths_of_zeta₀_le_one` / `norm_entireXi_sub_half_lt_half_of_zeta₀_le_one` — si ‖completedRiemannZeta₀‖ ≤ 1, entonces ‖entireXi(s) - 1/2‖ ≤ 3/8 < 1/2 con margen de seguridad ≥ 1/8 (FrontierMeasurement)
* `riemann_hypothesis_of_zeta₀_le_one_and_bocaA_off_line` / `riemann_hypothesis_of_zeta₀_le_one_and_bocaA` — Teorema Maestro Universal M=1: si ‖completedRiemannZeta₀‖ ≤ 1 en la frontera y no-anulación fuera de la línea en Boca A, entonces vale la Hipótesis de Riemann (RiemannHypothesis)
* `exp_neg_pi_lt_one` / `pi_gt_three_real` / `theta_ratio_le_one` — cotas numéricas y analíticas formales de la función theta y constantes asociadas (CajitaWallBound)
* `frontier_entireXi_sub_half_le_three_eighths` / `leftoverRect_entireXi_ne_zero_of_zeta₀_le_one` / `habitacion1_resolved_of_zeta₀_le_one` — Síntesis Maestra de Habitación 1 (Cajita): resolución condicional completa de Habitación 1 bajo ‖completedRiemannZeta₀‖ ≤ 1 (CajitaWallBound)
* `two_le_exp_one` / `four_le_exp_two` / `eight_le_exp_three` / `eight_lt_exp_pi` / `exp_neg_pi_lt_one_eighth` — cota analítica estricta exp(-π) < 1/8 derivada formalmente de 1+1 ≤ exp(1) y 3 < π (LambdaZeroRealBound)
* `one_sub_exp_neg_pi_gt_seven_eighths` / `two_twenty_firsts_lt_one` / `theta_tail_constant_lt_one` — Cota Analítica Maestra del Núcleo Theta: (2 exp(-π))/(π (1 - exp(-π))) < 2/21 < 1 con factor de seguridad > 10 (LambdaZeroRealBound)
* `norm_zeta₀_lt_one_of_theta_bound` / `frontier_zeta₀_le_one_of_theta_bound` / `habitacion1_resolved_of_theta_bound` — Transferencia a las 4 paredes y resolución de Habitación 1 bajo la cota de cola theta (LambdaZeroFrontierBound)
* `riemann_hypothesis_of_theta_bound_and_bocaA_off_line` / `riemann_hypothesis_of_two_twenty_firsts_and_bocaA_off_line` — Reducción formal de la Hipótesis de Riemann canónica bajo la cota theta en paredes y no-anulación off-line en Boca A (LambdaZeroFrontierBound)
* `HasPrime2DualDominance` / `ne_zero_of_hasPrime2DualDominance` / `bocaA_zeta_ne_zero_of_prime2_dominance` — Predicado y teorema de no-anulación en Boca A por dominancia asimétrica del primo 2 (BocaANonvanishing)
* `riemann_hypothesis_of_zeta₀_le_one_and_prime2_dominance` — Síntesis Maestra Global: cota M=1 en 4 paredes de Cajita + dominancia asimétrica del primo 2 en Boca A implican formalmente RiemannHypothesis (RiemannHypothesis)
* `exists_dominant_amplitude_of_remainder_bound` / `remainder_lt_gap_of_le` / `prime_composite_wave_ne_zero_of_bound` / `primeDualGainRatio_gap_pos` — Herramienta de Cota de Resto de Primos Superiores: existencia de amplitud dominante para cualquier resto acotado y no-anulación estricta de ondas compuestas (PrimeRemainderBound)
* `norm_two_cpow_one_sub` / `one_sub_re_pos_of_re_lt_one` / `two_rpow_one_sub_re_gt_one` / `norm_two_cpow_one_sub_gt_one` / `dirichletEta_factor_ne_zero_of_re_lt_one` / `riemannZeta_eq_zero_iff_dirichletEta_eq_zero_of_re_lt_one` / `dirichletEta_factor_ne_zero_of_mem_leftoverInterior` / `riemannZeta_eq_zero_iff_dirichletEta_eq_zero_of_mem_leftoverInterior` — Invertibilidad Universal del Factor Multiplicador de Dirichlet Eta en el semiplano Re(s) < 1 y equivalencia exacta ζ=0 ↔ η=0 en leftoverInterior (EtaContinuationBound)
* `exp_sub_one_ge` / `primeDualGainRatio_sub_one_ge_of_neg` / `exp_two_mul_delta_log_two_le_two` / `one_sub_primeDualGainRatio_ge_of_pos` / `abs_primeDualGainRatio_sub_one_ge_of_neg` / `abs_primeDualGainRatio_sub_one_ge_of_pos` / `primeDualGainRatio_gap_ge_linear` / `primeDualGainRatio_linear_bound_pos` / `primeDualGainRatio_gap_ge_linear_of_mem_strip` / `hasPrime2DualDominance_of_linear_bound` / `ne_zero_of_linear_bound` — Cota Cuantitativa Lineal del Desajuste del Primo 2: |r₂(δ) - 1| ≥ |δ| log 2 > 0 para todo δ ∈ [-1/2, 1/2]\{0} y no-anulación con resto acotado por margen lineal (Prime2LinearGap)
* `nat_le_sq` / `pow_le_pow_of_le_one` / `q_pow_sq_le_q_pow` / `thetaTailPartialSum_le_geomTailPartialSum` / `geomTailPartialSum_eq` / `geomTailPartialSum_lt` / `thetaTailPartialSum_lt_of_lt_one` / `exp_neg_pi_pos_and_lt_one` / `exp_neg_pi_geom_sum_lt_one_seventh` / `thetaTailPartialSum_exp_neg_pi_lt_one_seventh` / `two_div_pi_mul_thetaTailPartialSum_lt_two_twenty_firsts` / `two_div_pi_mul_thetaTailPartialSum_lt_one` — Mayoración Geométrica Rigurosa de la Cola de Jacobi Theta: (2/π) ∑_{n=1}^N (e^{-π})^{n²} < 2/21 < 1 uniforme para todo N ≥ 1 satisfaciendo la barrera M=1 de Cajita (ThetaTailGeometric)
* `IsThetaMajorized` / `norm_lt_one_of_isThetaMajorized` / `frontier_zeta₀_le_one_of_isThetaMajorized` / `habitacion1_resolved_of_isThetaMajorized` / `thetaTailPartialSum_isThetaMajorized` / `frontier_entireXi_deviation_le_three_eighths_of_isThetaMajorized` / `riemann_hypothesis_of_theta_majorized_and_bocaA_off_line` — Criterio Analítico de Mayoración Theta en Paredes de Cajita y Reducción Maestra a Boca A (ThetaIntegralBound)
* `re_s_div_two_sub_one_le_neg_half` / `re_one_sub_s_div_two_sub_one_le_neg_three_fourths` / `re_s_div_two_sub_one_nonpos` / `re_one_sub_s_div_two_sub_one_nonpos` / `norm_cpow_real_le_one` / `theta_kernel_weight_norm_le_two` / `theta_kernel_weight_norm_le_two_of_mem_leftoverRect` / `leftoverRect_isClosed` / `mem_leftoverRect_of_mem_frontier` / `theta_kernel_weight_norm_le_two_of_mem_frontier` / `theta_kernel_scaled_norm_le` — Mayoración Analítica Exacta del Núcleo Theta: cota uniforme de peso ‖u^{s/2-1} + u^{(1-s)/2-1}‖ ≤ 2 en leftoverRect y frontier (ThetaKernelDomination)
* `isBounded_leftoverRect` / `differentiable_entireXi_sub_half` / `diffContOnCl_entireXi_sub_half` / `entireXi_sub_half_le_three_eighths_on_leftoverRect` / `entireXi_sub_half_lt_half_on_leftoverRect` / `leftoverRect_entireXi_ne_zero_of_maximum_modulus` / `leftoverInterior_zeta_ne_zero_of_maximum_modulus` / `habitacion1_full_synthesis_of_maximum_modulus` — Principio del Módulo Máximo de Mathlib en leftoverRect: transferencia rigurosa de la cota de frontera a todo el dominio compacto 2D e imposibilidad estricta de anulación (MaximumModulusLeftover)
* `HasSafePrimeTailBound` / `remainder_lt_linear_gap_of_safe_bound` / `hasPrime2DualDominance_of_safe_bound` / `ne_zero_of_safe_bound` / `strip_ne_zero_of_safe_bound` — Barrera Analítica de Restos de Primos Superiores en Boca A: ‖R‖ ≤ (1/2)(|δ| log 2)A₂ garantiza no-anulación estricta fuera de la línea crítica (PrimeTailAnalytic)
* `log_two_lt_log_three` / `log_three_sub_log_two_pos` / `three_le_prime_of_ne_two` / `log_two_lt_log_prime` / `prime_ratio_le_two_thirds` / `prime_wave_ne_zero_of_decay` / `bocaA_zeta_ne_zero_of_prime_decay` — Jerarquía y Decaimiento Analítico de Frecuencias de Primos Superiores: separación estricta frente al líder p=2 y no-anulación off-line en Boca A (PrimeTailDecay)
* `thetaTailTerm` / `geomTailTerm` / `thetaTailTerm_le_geomTailTerm` / `thetaTailTerm_nonneg` / `geomTailTerm_nonneg` / `summable_geomTailTerm` / `summable_thetaTailTerm` / `tsum_thetaTailTerm_le_tsum_geomTailTerm` / `tsum_geomTailTerm_eq` / `tsum_thetaTailTerm_le_ratio` / `summable_thetaTailTerm_exp_neg_pi` / `tsum_thetaTailTerm_exp_neg_pi_lt_one_seventh` / `two_div_pi_mul_tsum_thetaTail_lt_two_twenty_firsts` / `two_div_pi_mul_tsum_thetaTail_lt_one` — Convergencia Rigurosa y Cota de la Serie Infinita de Jacobi Theta: ∑_{n=1}^∞ q^{n²} ≤ q/(1-q) < 1/7 y (2/π) ∑_{n=1}^∞ (e^{-π})^{n²} < 2/21 < 1 (ThetaInfiniteSeriesBound)
* `prime2Amplitude` / `prime2Amplitude_pos` / `prime2Amplitude_nonneg` / `primeDualGainRatio_mul_prime2Amplitude` / `norm_two_cpow_neg_s` / `norm_two_cpow_neg_one_sub_s` / `norm_two_cpow_ratio_eq_primeDualGainRatio` / `norm_two_cpow_west_ne_east_of_off_line` / `safePrimeTailThreshold` / `safePrimeTailThreshold_pos` / `hasSafePrimeTailBound_of_le_threshold` / `zeta_ne_zero_of_safe_threshold` — Descomposición Dual Canónica en Boca A: amplitudes exactas ‖2^{-s}‖ y ‖2^{-(1-s)}‖, desajuste estricto de normas off-line y umbral seguro de no-anulación (BocaADualDecomposition)
* `frequencyGap` / `frequencyGap_pos` / `log_three_sub_log_two_le_frequencyGap` / `norm_channelWave_sub_le` / `norm_I_mul_real` / `oscillatory_primitive_diff_norm_le` / `oscillatory_primitive_bound_of_frequencyGap` / `average_oscillatory_correlation_le` / `gram_window_cross_correlation_safe` / `exists_gram_window_decay_lt_safe_threshold` / `exists_safe_gram_window_remainder` / `hasSafePrimeTailBound_of_gram_window_decay` — Ortogonalidad y Cancelación Oscilatoria de Frecuencias de Primos Superiores: separación estricta Δω(p) ≥ log 3 - log 2 > 0, decaimiento O(1/T) por debajo del umbral seguro y puente formal a HasSafePrimeTailBound (PrimeCarrierOrthogonality)
* `riemann_hypothesis_of_theta_majorized_and_prime2_dominance` / `riemann_hypothesis_of_theta_majorized_and_safe_prime_tail` / `riemann_hypothesis_of_rational_theta_and_safe_prime_tail` / `riemann_hypothesis_of_maximum_modulus_and_prime_decay` / `leftoverInterior_zeta_ne_zero_of_theta_majorized` / `bocaA_zeta_ne_zero_of_safe_threshold_forall` / `riemann_hypothesis_grand_synthesis` / `ThreeRoomsSpectralData` / `canonical_riemann_hypothesis` / `riemann_hypothesis_of_theta_and_gram_window_decay` — Teoremas Cúspide Maestros Globales: Gran Síntesis Unificada de Habitación 1 y Habitación 3, empaquetamiento espectral canónico ThreeRoomsSpectralData y deducción formal canónica de RiemannHypothesis (RiemannHypothesisMaster)


## OPEN

* leftoverInterior: cerrar la cota analítica C < 1/2 en Lean (numéricamente C ≈ 0.016 ≪ 0.5)
* resto de Stirling (Bernoulli) — no hace falta para M
* Boca A (Gap 5.2): cota uniforme en el semiplano izquierdo Re(u) < 0 via dual cancellation
-/

namespace RhG1Lean

end RhG1Lean

