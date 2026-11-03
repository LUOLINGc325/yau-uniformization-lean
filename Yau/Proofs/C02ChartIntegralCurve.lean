import Yau.Proofs.C02ODELocalFlow

/-! A coordinate solution is an integral curve of the same actual vector
field when the chart coefficient identity holds. No replacement connection
or flow is introduced. -/

noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff
namespace Yau.Blueprint.C02Proof

variable {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace N] [ChartedSpace H N]
  {I : ModelWithCorners ℝ E H} [IsManifold I ∞ N] [I.Boundaryless]

theorem chart_ODE_isMIntegralCurveOn (p : N) (F : E → E)
    (V : ∀ q : N, TangentSpace I q) (η : ℝ → E) {s : Set ℝ}
    (hV : ∀ q ∈ (extChartAt I p).source,
      tangentCoordChange I q p q (V q) = F (extChartAt I p q))
    (hη : ∀ t ∈ s, η t ∈ (extChartAt I p).target ∧ HasDerivAt η (F (η t)) t) :
    IsMIntegralCurveOn ((extChartAt I p).symm ∘ η) V s := by
  intro t ht
  let xt := (extChartAt I p).symm (η t)
  have htarg : η t ∈ (extChartAt I p).target := (hη t ht).1
  have hft1 : xt ∈ (extChartAt I p).source := (extChartAt I p).map_target htarg
  have hft2 : xt ∈ (extChartAt I xt).source := mem_extChartAt_source _
  let v : E := V xt
  have hcoord : tangentCoordChange I xt p xt v = F (η t) := by
    simpa only [v, xt, (extChartAt I p).right_inv htarg] using hV xt hft1
  have h : HasDerivAt η (tangentCoordChange I xt p xt v) t := by
    rw [hcoord]
    exact (hη t ht).2
  apply HasMFDerivAt.hasMFDerivWithinAt
  refine ⟨(continuousAt_extChartAt_symm'' htarg).comp h.continuousAt,
    HasDerivWithinAt.hasFDerivWithinAt ?_⟩
  simp only [mfld_simps]
  change HasDerivWithinAt ((extChartAt I xt ∘ (extChartAt I p).symm) ∘ η) (V xt) univ t
  apply HasDerivAt.hasDerivWithinAt
  have hD : HasFDerivAt (extChartAt I xt ∘ (extChartAt I p).symm)
      (tangentCoordChange I p xt xt) (η t) := by
    apply HasFDerivWithinAt.hasFDerivAt (s := range I) _
      (by rw [ModelWithCorners.range_eq_univ]; exact Filter.univ_mem)
    rw [← (extChartAt I p).right_inv htarg]
    exact hasFDerivWithinAt_tangentCoordChange ⟨hft1, hft2⟩
  have hcomp : tangentCoordChange I p xt xt (tangentCoordChange I xt p xt v) = v :=
    (tangentCoordChange_comp (I := I) (w := xt) (x := p) (y := xt) (z := xt) (v := v)
      ⟨⟨hft2, hft1⟩, hft2⟩).trans (tangentCoordChange_self hft2)
  simpa only [hcomp] using hD.comp_hasDerivAt t h

end Yau.Blueprint.C02Proof
