import Yau.Proofs.F04GalerkinOperators

open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ContDiff

noncomputable section

namespace Yau.F04Proof

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] {m : ℕ}

/-- Actual continuous finite Galerkin solutions of the original form equation.
 The Volterra theorem is the already proved native finite-dimensional theorem. -/
theorem variationalGalerkin_exists
    {T C : ℝ} (hT : 0 < T) (hC : 0 ≤ C)
    (j : V →L[ℝ] H) (e : Fin m → V)
    (B : ℝ → V →L[ℝ] V →L[ℝ] ℝ)
    (hB : ∀ t, ‖B t‖ ≤ C) (hcB : ∀ u v, Continuous (fun t => B t u v))
    {F : ℝ → H} (hF : MemLp F 2 (volume.restrict (Ioo 0 T))) :
    ∃ c : ℝ → EuclideanSpace ℝ (Fin m),
      ContinuousOn c (Icc 0 T) ∧ c 0 = 0 ∧
      (∀ t ∈ Icc 0 T, c t = ∫ s in (0 : ℝ)..t,
        variationalForcing j e (F s) - variationalMatrix e (B s) (c s)) ∧
      ∀ᵐ t ∂volume.restrict (Ioo 0 T), HasDerivAt c
        (variationalForcing j e (F t) - variationalMatrix e (B t) (c t)) t := by
  let M := ‖variationalTestEvaluation e‖ * C * ‖variationalReconstruction e‖
  have hM : 0 ≤ M := mul_nonneg (mul_nonneg (ContinuousLinearMap.opNorm_nonneg (variationalTestEvaluation e)) hC) (norm_nonneg _)
  apply Yau.LeafProofs.L16Aux.finiteVolterra_exists m hT hM
    (fun t => variationalMatrix e (B t)) (fun t => variationalForcing j e (F t))
    (variationalMatrix_continuous e B hcB).aestronglyMeasurable
  · exact ae_of_all _ fun t => (variationalMatrix_norm_le e (B t)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hB t) (ContinuousLinearMap.opNorm_nonneg (variationalTestEvaluation e))) (norm_nonneg _))
  · exact (variationalForcing j e).integrable_comp (hF.integrable (by norm_num))

theorem variationalGalerkin_rhs_integrable {T C : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C)
    (j : V →L[ℝ] H) (e : Fin m → V)
    (B : ℝ → V →L[ℝ] V →L[ℝ] ℝ) (hB : ∀ t, ‖B t‖ ≤ C)
    (hcB : ∀ u v, Continuous (fun t => B t u v))
    {F : ℝ → H} (hF : MemLp F 2 (volume.restrict (Ioo 0 T)))
    {c : ℝ → EuclideanSpace ℝ (Fin m)} (hc : ContinuousOn c (Icc 0 T)) :
    Integrable (fun t => variationalForcing j e (F t) - variationalMatrix e (B t) (c t))
      (volume.restrict (Ioo 0 T)) := by
  let cc : C(Icc (0 : ℝ) T, EuclideanSpace ℝ (Fin m)) := ⟨_, hc.domRestrict⟩
  let M := ‖variationalTestEvaluation e‖ * C * ‖variationalReconstruction e‖
  have hM : 0 ≤ M := mul_nonneg (mul_nonneg (ContinuousLinearMap.opNorm_nonneg (variationalTestEvaluation e)) hC) (norm_nonneg _)
  have hA : Continuous (fun t => variationalMatrix e (B t)) := variationalMatrix_continuous e B hcB
  have hAM : ∀ t, ‖variationalMatrix e (B t)‖ ≤ M := fun t =>
    (variationalMatrix_norm_le e (B t)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hB t) (ContinuousLinearMap.opNorm_nonneg (variationalTestEvaluation e))) (norm_nonneg _))
  have hcm : AEStronglyMeasurable c (volume.restrict (Ioo 0 T)) :=
    (hc.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  have hm : AEStronglyMeasurable (fun t => variationalMatrix e (B t) (c t))
      (volume.restrict (Ioo 0 T)) :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂ hA.aestronglyMeasurable hcm
  have hAc : Integrable (fun t => variationalMatrix e (B t) (c t)) (volume.restrict (Ioo 0 T)) := by
    refine (integrable_const (M * ‖cc‖)).mono' hm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact ((variationalMatrix e (B t)).le_opNorm (c t)).trans
      (mul_le_mul (hAM t) (cc.norm_coe_le_norm ⟨t, ht.1.le, ht.2.le⟩) (norm_nonneg _) hM)
  exact ((variationalForcing j e).integrable_comp (hF.integrable (by norm_num))).sub hAc

/-- The uniform coercive inequality uses the true H-orthonormal coordinates,
 and hence has constants independent of the finite Galerkin space. -/
theorem variationalGalerkin_pointwise_energy {α shift : ℝ}
    (j : V →L[ℝ] H) (e : Fin m → V)
    (he : Orthonormal ℝ (fun i => j (e i)))
    (B : V →L[ℝ] V →L[ℝ] ℝ) (F : H) (c : EuclideanSpace ℝ (Fin m))
    (hGard : α * ‖variationalReconstruction e c‖ ^ 2 ≤
      B (variationalReconstruction e c) (variationalReconstruction e c) +
        shift * ‖j (variationalReconstruction e c)‖ ^ 2) :
    2 * inner ℝ (variationalForcing j e F - variationalMatrix e B c) c +
      (2 * α) * ‖variationalReconstruction e c‖ ^ 2 ≤
        (2 * shift + 1) * ‖c‖ ^ 2 + ‖F‖ ^ 2 := by
  rw [inner_sub_left, variationalForcing_inner, variationalMatrix_inner]
  have hi := real_inner_le_norm F (j (variationalReconstruction e c))
  have hs := sq_nonneg (‖F‖ - ‖j (variationalReconstruction e c)‖)
  have hn := variationalReconstruction_norm_sq j e he c
  rw [hn] at hGard
  nlinarith

end Yau.F04Proof
