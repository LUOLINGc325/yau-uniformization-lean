import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime
import Mathlib.Analysis.ODE.ExistUnique

/-! Actual chart solutions and uniform local Picard curves near an initial point. -/
noncomputable section
open scoped Manifold Topology
open Set Filter Function
namespace Yau.Proofs.C05CompactInvariantFlowAux
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

set_option backward.isDefEq.respectTransparency false in
 theorem chart_ode_isMIntegralCurveOn
    (v : (x : M) → TangentSpace I x) (x₀ : M) (f : ℝ → E) (s : Set ℝ)
    (hf : ∀ t ∈ s, HasDerivAt f
      (tangentCoordChange I ((extChartAt I x₀).symm (f t)) x₀
        ((extChartAt I x₀).symm (f t)) (v ((extChartAt I x₀).symm (f t)))) t)
    (htarget : ∀ t ∈ s, f t ∈ interior (extChartAt I x₀).target) :
    IsMIntegralCurveOn ((extChartAt I x₀).symm ∘ f) v s := by
  intro t ht
  let xₜ : M := (extChartAt I x₀).symm (f t)
  have h := hf t ht
  have hf3 := htarget t ht
  have hf3' := mem_of_mem_of_subset hf3 interior_subset
  have hft1 := mem_preimage.mp <|
    mem_of_mem_of_subset hf3' (extChartAt I x₀).target_subset_preimage_source
  have hft2 := mem_extChartAt_source (I := I) xₜ
  apply HasMFDerivAt.hasMFDerivWithinAt
  refine ⟨(continuousAt_extChartAt_symm'' hf3').comp h.continuousAt,
    HasDerivWithinAt.hasFDerivWithinAt ?_⟩
  simp only [mfld_simps, hasDerivWithinAt_univ]
  change HasDerivAt ((extChartAt I xₜ ∘ (extChartAt I x₀).symm) ∘ f) (v xₜ) t
  rw [← tangentCoordChange_self (I := I) (x := xₜ) (z := xₜ) (v := v xₜ) hft2,
    ← tangentCoordChange_comp (x := x₀) ⟨⟨hft2, hft1⟩, hft2⟩]
  apply HasFDerivAt.comp_hasDerivAt _ _ h
  apply HasFDerivWithinAt.hasFDerivAt (s := range I) _ <|
    mem_nhds_iff.mpr ⟨interior (extChartAt I x₀).target,
      subset_trans interior_subset (extChartAt_target_subset_range ..),
      isOpen_interior, hf3⟩
  rw [← (extChartAt I x₀).right_inv hf3']
  exact hasFDerivWithinAt_tangentCoordChange ⟨hft1, hft2⟩

set_option backward.isDefEq.respectTransparency false in
 theorem exists_uniform_nearby_integral_curves
    [CompleteSpace E] [BoundarylessManifold I M]
    (v : (x : M) → TangentSpace I x) (x₀ : M)
    (hv : ContMDiffAt I (I.prod 𝓘(ℝ,E)) 1
      (fun x => (⟨x,v x⟩ : TangentBundle I M)) x₀) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ U ∈ 𝓝 x₀, ∀ x ∈ U,
      ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ioo (-ε) ε) := by
  let e := extChartAt I x₀
  let c := e x₀
  let f : E → E := fun y => tangentCoordChange I (e.symm y) x₀ (e.symm y) (v (e.symm y))
  have hcf : ContDiffAt ℝ 1 f c := by
    rw [contMDiffAt_iff] at hv
    exact (hv.2.contDiffAt (range_mem_nhds_isInteriorPoint
      (BoundarylessManifold.isInteriorPoint (I := I) (x := x₀)))).snd
  obtain ⟨ε,hε,a,r,L,C,hr,hpl⟩ := IsPicardLindelof.of_contDiffAt_one hcf
  obtain ⟨α,hα,hcont⟩ := (hpl 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  simp only [zero_sub,zero_add] at hα hcont
  have hdom : Metric.closedBall c (r:ℝ) ×ˢ Icc (-ε) ε ∈ 𝓝 (c,(0:ℝ)) :=
    prod_mem_nhds (Metric.closedBall_mem_nhds c hr) (Icc_mem_nhds (by linarith) hε)
  have hcenter : α (c,0) = c := (hα c (Metric.mem_closedBall_self hr.le)).1
  have htgt : ∀ᶠ p in 𝓝 (c,(0:ℝ)), α p ∈ interior e.target := by
    apply (hcont.continuousAt hdom).eventually_mem
    rw [hcenter]
    exact isOpen_interior.mem_nhds ((I.isInteriorPoint_iff).mp
      (BoundarylessManifold.isInteriorPoint (I := I) (x := x₀)))
  rw [nhds_prod_eq] at htgt
  have hnear : ∀ᶠ p in 𝓝 c ×ˢ 𝓝 (0:ℝ),
      p.1 ∈ Metric.closedBall c (r:ℝ) ∧ p.2 ∈ Ioo (-ε) ε :=
    Filter.prod_mem_prod_iff.mpr ⟨Metric.closedBall_mem_nhds c hr,
      Ioo_mem_nhds (by linarith) hε⟩
  obtain ⟨U,hU,T,hT,hgood⟩ := Filter.mem_prod_iff.mp (hnear.and htgt)
  obtain ⟨δ,hδ,hδT⟩ := Metric.mem_nhds_iff.mp hT
  refine ⟨δ,hδ,e.source ∩ e ⁻¹' U,inter_mem (extChartAt_source_mem_nhds x₀)
    ((continuousAt_extChartAt x₀).preimage_mem_nhds hU),?_⟩
  intro x hx
  have hxball : e x ∈ Metric.closedBall c (r:ℝ) :=
    (hgood (show (e x,0) ∈ U ×ˢ T from ⟨hx.2,mem_of_mem_nhds hT⟩)).1.1
  refine ⟨e.symm ∘ (fun t => α (e x,t)),?_,?_⟩
  · change e.symm (α (e x,0)) = x
    rw [(hα (e x) hxball).1,e.left_inv hx.1]
  · have hpair (t : ℝ) (ht : t ∈ Ioo (-δ) δ) :=
      hgood (show (e x,t) ∈ U ×ˢ T from ⟨hx.2,hδT (by
        simpa only [Real.ball_eq_Ioo,zero_sub,zero_add] using ht)⟩)
    apply chart_ode_isMIntegralCurveOn v x₀ (fun t => α (e x,t))
    · intro t ht
      exact ((hα (e x) hxball).2 t (Ioo_subset_Icc_self (hpair t ht).1.2)).hasDerivAt
        (Icc_mem_nhds (hpair t ht).1.2.1 (hpair t ht).1.2.2)
    · exact fun t ht => (hpair t ht).2

end Yau.Proofs.C05CompactInvariantFlowAux
