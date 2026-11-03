import Yau.Proofs.C03CompactMinimizers
import Yau.Proofs.C03MetricEnvelope

/-! Constant-speed minimizing segments approach their endpoints from the
interior of the corresponding distance ball, including at the cut locus. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ContDiff Manifold ENNReal

namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs L12Aux L23Aux L23LocalDistanceContract
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem fieldPathELength_constant_speed (h : HermitianField M)
    (γ : ℝ → M.Carrier) (a b D : ℝ) (hab : a ≤ b) (hD : 0 ≤ D)
    (hspeed : ∀ u ∈ Icc a b, actualSpeedSq h γ u = D ^ 2) :
    fieldPathELength h γ a b = ENNReal.ofReal ((b - a) * D) := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup h y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace h y
  change Manifold.pathELength 𝓘(ℝ, ComplexVector n) γ a b = _
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  have heq : (fun u => ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) γ u 1‖ₑ) =ᵐ[
      volume.restrict (Icc a b)] (fun _ => ENNReal.ofReal D) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    rw [← ofReal_norm]
    apply congrArg ENNReal.ofReal
    have H : ‖realCurveVelocity γ u‖ ^ 2 = D ^ 2 :=
      (real_inner_self_eq_norm_sq _).symm.trans (hspeed u hu)
    exact (sq_eq_sq₀ (norm_nonneg _) hD).mp H
  rw [lintegral_congr_ae heq]
  simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc,
    ← ENNReal.ofReal_mul hD, mul_comm D]

theorem field_segment_distance_le (h : HermitianField M) (hh : MetricSmooth h)
    (γ : ℝ → M.Carrier) (a b D : ℝ) (hab : a ≤ b) (hD : 0 ≤ D) :
    letI := manifold_realSmooth M
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 γ (Icc a b) →
    (∀ u ∈ Icc a b, actualSpeedSq h γ u = D ^ 2) →
    inducedDistance h (γ a) (γ b) ≤ (b - a) * D := by
  letI := manifold_realSmooth M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup h y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace h y
  intro hγ hspeed
  have H : ENNReal.ofReal (inducedDistance h (γ a) (γ b)) ≤ fieldPathELength h γ a b := by
    rw [inducedDistance_eq_riemannianEDist h hh]
    exact Manifold.riemannianEDist_le_pathELength hγ rfl rfl hab
  rw [fieldPathELength_constant_speed h γ a b D hab hD hspeed] at H
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sub_nonneg.mpr hab) hD)).mp H

theorem field_closedBall_subset_closure_ball
    (h : HermitianField M) (hh : MetricSmooth h)
    (hcompact : ∀ p R, IsCompact {x | inducedDistance h p x ≤ R})
    (o : M.Carrier) (ρ : ℝ) (hρ : 0 < ρ) :
    letI := metricSpaceOfField h hh
    Metric.closedBall o ρ ⊆ closure (Metric.ball o ρ) := by
  letI := manifold_realSmooth M
  letI := metricSpaceOfField h hh
  intro y hy
  have hdy : inducedDistance h o y ≤ ρ := by
    change inducedDistance h y o ≤ ρ at hy
    rwa [inducedDistance_symm h hh y o] at hy
  obtain ⟨δ, hδ, γ, hγ0, hγ1, hγ, hspeed⟩ :=
    minimizing_geodesic_of_compact_sublevels h hh hcompact o y
  have hcont : ContinuousAt γ 1 :=
    (hγ.1.continuousOn.continuousAt (isOpen_Ioo.mem_nhds
      (show (1 : ℝ) ∈ Ioo (-δ) (1 + δ) by constructor <;> linarith)))
  have hcl : (1 : ℝ) ∈ closure (Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (show (0 : ℝ) ≠ 1 by norm_num)]
    exact ⟨zero_le_one, le_rfl⟩
  rw [← hγ1]
  apply hcont.continuousWithinAt.mem_closure hcl
  intro u hu
  have hC : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 γ (Icc 0 u) :=
    (hγ.1.of_le (by norm_num)).mono (by
      intro t ht
      constructor <;> linarith [ht.1, ht.2, hu.2])
  have H := field_segment_distance_le h hh γ 0 u (inducedDistance h o y) hu.1.le
    (inducedDistance_nonneg h hh o y) hC (by
      intro t ht
      exact hspeed t ⟨ht.1, ht.2.trans hu.2.le⟩)
  rw [hγ0, sub_zero] at H
  change dist (γ u) o < ρ
  rw [dist_comm]
  change inducedDistance h o (γ u) < ρ
  exact H.trans_lt ((mul_le_mul_of_nonneg_left hdy hu.1.le).trans_lt
    (by nlinarith [mul_pos hρ (sub_pos.mpr hu.2)]))

end Yau.Proofs.C03Aux
