import Yau.LeafProofs.L17ChartEscape

/-! Actual transition differentials and their uniform first-order bounds. -/

noncomputable section

open Set Metric Filter
open scoped Topology ContDiff Manifold

namespace Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem transition_fderiv_apply
    (e d : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hdi : MDifferentiableOn (ComplexModel n) (ComplexModel n) d.symm d.target)
    {z : ComplexVector n} (hz : z ∈ transitionDomain e d) (v : ComplexVector n) :
    fderiv ℝ (fun w => d.symm (e w)) z v =
      realInverseCoordinateDifferential d (e z) (realChartFrame e z v) := by
  let := L12Aux.manifold_realSmooth M
  have heAt := ((chart_real_contMDiffOn e he) z hz.1).contMDiffAt
    (e.open_source.mem_nhds hz.1)
  have hdAt := ((inverse_chart_real_contMDiffOn d hdi) (e z) hz.2).contMDiffAt
    (d.open_target.mem_nhds hz.2)
  have hchain := mfderiv_comp_apply z (hdAt.mdifferentiableAt (by simp))
    (heAt.mdifferentiableAt (by simp))
    ((tangentSpaceCastModel 𝓘(ℝ, ComplexVector n) z).symm v)
  rw [mfderiv_eq_fderiv] at hchain
  convert! hchain using 1

theorem transition_frame
    (e d : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hd : MDifferentiableOn (ComplexModel n) (ComplexModel n) d d.source)
    (hdi : MDifferentiableOn (ComplexModel n) (ComplexModel n) d.symm d.target)
    {z : ComplexVector n} (hz : z ∈ transitionDomain e d) (v : ComplexVector n) :
    realChartFrame d (d.symm (e z))
      (fderiv ℝ (fun w => d.symm (e w)) z v) = realChartFrame e z v := by
  let := L12Aux.manifold_realSmooth M
  let T : ComplexVector n → ComplexVector n := fun w => d.symm (e w)
  have hU := (transitionDomain_isOpen e d).mem_nhds hz
  have hT : DifferentiableAt ℝ T z :=
    ((transition_real_contDiffOn e d he hdi).contDiffAt hU).differentiableAt (by simp)
  have hTm : MDifferentiableAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) T z :=
    mdifferentiableAt_iff_differentiableAt.mpr hT
  have hdAt := ((chart_real_contMDiffOn d hd) (T z) (d.map_target hz.2)).contMDiffAt
    (d.open_source.mem_nhds (d.map_target hz.2))
  have heq : (fun w => d (T w)) =ᶠ[𝓝 z] e := by
    filter_upwards [hU] with w hw
    exact d.right_inv hw.2
  have hlocal : mfderiv 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n)
      (d ∘ T) z =
        mfderiv 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) e z := by
    convert! heq.mfderiv_eq (I := 𝓘(ℝ, ComplexVector n))
      (I' := 𝓘(ℝ, ComplexVector n)) using 1
  have hchain := mfderiv_comp_apply z (hdAt.mdifferentiableAt (by simp)) hTm
    ((tangentSpaceCastModel 𝓘(ℝ, ComplexVector n) z).symm v)
  rw [mfderiv_eq_fderiv, hlocal] at hchain
  convert! hchain.symm using 1

theorem transition_fderiv_surjective
    (e d : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    (hd : MDifferentiableOn (ComplexModel n) (ComplexModel n) d d.source)
    (hdi : MDifferentiableOn (ComplexModel n) (ComplexModel n) d.symm d.target)
    {z : ComplexVector n} (hz : z ∈ transitionDomain e d) :
    Function.Surjective (fderiv ℝ (fun w => d.symm (e w)) z) := by
  let := L12Aux.manifold_realSmooth M
  have heR : e.MDifferentiable 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) :=
    ⟨(chart_real_contMDiffOn e he).mdifferentiableOn (by simp),
      (inverse_chart_real_contMDiffOn e hei).mdifferentiableOn (by simp)⟩
  have hdR : d.MDifferentiable 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) :=
    ⟨(chart_real_contMDiffOn d hd).mdifferentiableOn (by simp),
      (inverse_chart_real_contMDiffOn d hdi).mdifferentiableOn (by simp)⟩
  have hsurj := (heR.trans hdR.symm).mfderiv_surjective hz
  rw [mfderiv_eq_fderiv] at hsurj
  convert! hsurj using 1

theorem sqrt_frame_ratio {C : ℝ} (hC : 0 < C) :
    (Real.sqrt (2 * C⁻¹))⁻¹ * Real.sqrt (2 * C) = C := by
  rw [← Real.sqrt_inv, ← Real.sqrt_mul (by positivity : 0 ≤ (2 * C⁻¹)⁻¹)]
  have heq : (2 * C⁻¹)⁻¹ * (2 * C) = C ^ 2 := by field_simp
  rw [heq, Real.sqrt_sq hC.le]

theorem BoundedChartFamily.transition_fderiv_norm_le
    {g : HermitianField M} (A : BoundedChartFamily g) (p q : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ ball 0 A.radius)
    (hq : A.chart p z ∈ A.chart q '' ball 0 A.radius) (v : ComplexVector n) :
    ‖fderiv ℝ (fun w => (A.chart q).symm (A.chart p w)) z v‖ ≤
      A.bound 0 * ‖v‖ := by
  let := L12Aux.underlyingRealTangentNormedAddCommGroup g (A.chart p z)
  have hs : z ∈ (A.chart p).source := A.closedBall_source p (ball_subset_closedBall hz)
  have ht : A.chart p z ∈ (A.chart q).target := by
    obtain ⟨w, hw, hweq⟩ := hq
    rw [← hweq]
    exact (A.chart q).map_source (A.closedBall_source q (ball_subset_closedBall hw))
  rw [transition_fderiv_apply (A.chart p) (A.chart q)
    (A.differentiable p) (A.inverse_differentiable q) ⟨hs, ht⟩]
  calc
    _ ≤ (Real.sqrt (2 * (A.bound 0)⁻¹))⁻¹ * ‖realChartFrame (A.chart p) z v‖ :=
      A.inverseCoordinateDifferential_norm_le q (A.chart p z) hq _
    _ ≤ (Real.sqrt (2 * (A.bound 0)⁻¹))⁻¹ *
        (Real.sqrt (2 * A.bound 0) * ‖v‖) :=
      mul_le_mul_of_nonneg_left (A.realFrame_norm_comparison p hz v).2 (by positivity)
    _ = _ := by rw [← mul_assoc, sqrt_frame_ratio (A.bound_pos 0)]

theorem BoundedChartFamily.transition_fderiv_opNorm_le
    {g : HermitianField M} (A : BoundedChartFamily g) (p q : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ ball 0 A.radius)
    (hq : A.chart p z ∈ A.chart q '' ball 0 A.radius) :
    ‖fderiv ℝ (fun w => (A.chart q).symm (A.chart p w)) z‖ ≤ A.bound 0 :=
  ContinuousLinearMap.opNorm_le_bound _ (A.bound_pos 0).le
    (A.transition_fderiv_norm_le p q hz hq)

end Yau.LeafProofs.L17Aux
