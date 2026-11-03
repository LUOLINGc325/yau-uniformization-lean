import Yau.LeafProofs.L17UniformCharts

/-!
Quantitative distance comparisons for the original bounded holomorphic charts.
The metric distance is the previously proved length distance of the field.
-/

noncomputable section

open Set Metric Filter MeasureTheory Bundle
open scoped Topology ContDiff Manifold ENNReal

namespace Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem BoundedChartFamily.distance_le
    {g : HermitianField M} (A : BoundedChartFamily g) (hg : MetricSmooth g)
    (p : M.Carrier) {z w : ComplexVector n}
    (hz : z ∈ ball 0 A.radius) (hw : w ∈ ball 0 A.radius) :
    inducedDistance g (A.chart p z) (A.chart p w) ≤
      Real.sqrt (2 * A.bound 0) * dist z w := by
  let := L12Aux.manifold_realSmooth M
  let : ∀ x : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) x) :=
    fun x => L12Aux.underlyingRealTangentNormedAddCommGroup g x
  let : ∀ x : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) x) :=
    fun x => L12Aux.underlyingRealTangentInnerProductSpace g x
  let η := ContinuousAffineMap.lineMap (R := ℝ) z w
  let γ := (A.chart p) ∘ η
  let C := Real.sqrt (2 * A.bound 0)
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hη : ∀ t ∈ Icc (0 : ℝ) 1, η t ∈ ball 0 A.radius := by
    intro t ht
    apply (convex_ball (0 : ComplexVector n) A.radius).segment_subset hz hw
    rw [segment_eq_image_lineMap]
    exact ⟨t, ht, rfl⟩
  have hsource (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : η t ∈ (A.chart p).source :=
    A.closedBall_source p (ball_subset_closedBall (hη t ht))
  have hηsmooth : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 η (Icc 0 1) := by
    rw [contMDiffOn_iff_contDiffOn]
    exact (ContinuousAffineMap.contDiff η).contDiffOn
  have hγsmooth : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 γ (Icc 0 1) :=
    ((chart_real_contMDiffOn (A.chart p) (A.differentiable p)).of_le (by simp)).comp
      hηsmooth hsource
  have hd : Manifold.riemannianEDist 𝓘(ℝ, ComplexVector n) (A.chart p z) (A.chart p w) ≤
      Manifold.pathELength 𝓘(ℝ, ComplexVector n) γ 0 1 := by
    apply Manifold.riemannianEDist_le_pathELength hγsmooth _ _ zero_le_one
    · simp [γ, η, ContinuousAffineMap.coe_lineMap_eq]
    · simp [γ, η, ContinuousAffineMap.coe_lineMap_eq]
  have hlen : Manifold.pathELength 𝓘(ℝ, ComplexVector n) γ 0 1 ≤
      ENNReal.ofReal C * edist z w := by
    rw [Manifold.pathELength_eq_lintegral_mfderivWithin_Icc,
      ← lintegral_fderiv_lineMap_eq_edist,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_mono' measurableSet_Icc
    intro t ht
    have heAt := ((chart_real_contMDiffOn (A.chart p) (A.differentiable p))
      (η t) (hsource t ht)).contMDiffAt
        ((A.chart p).open_source.mem_nhds (hsource t ht))
    have hchain : mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) γ (Icc 0 1) t =
        (mfderiv 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) (A.chart p) (η t)).comp
          (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) η (Icc 0 1) t) := by
      apply mfderiv_comp_mfderivWithin
      · exact heAt.mdifferentiableAt (by simp)
      · exact hηsmooth.mdifferentiableOn one_ne_zero t ht
      · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
        exact uniqueDiffOn_Icc zero_lt_one t ht
    rw [hchain, ContinuousLinearMap.comp_apply, mfderivWithin_eq_fderivWithin]
    change ‖realChartFrame (A.chart p) (η t)
      (fderivWithin ℝ η (Icc 0 1) t 1)‖ₑ ≤
        ENNReal.ofReal C * ‖fderivWithin ℝ η (Icc 0 1) t 1‖ₑ
    have hn := (A.realFrame_norm_comparison p (hη t ht)
      (fderivWithin ℝ η (Icc 0 1) t 1)).2
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hC]
    exact ENNReal.ofReal_le_ofReal hn
  have hdist : ENNReal.ofReal (inducedDistance g (A.chart p z) (A.chart p w)) ≤
      ENNReal.ofReal (C * dist z w) := by
    rw [L23Aux.inducedDistance_eq_riemannianEDist g hg]
    convert hd.trans hlen using 1
    rw [edist_dist, ENNReal.ofReal_mul hC]
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC dist_nonneg)).mp hdist

end Yau.LeafProofs.L17Aux
