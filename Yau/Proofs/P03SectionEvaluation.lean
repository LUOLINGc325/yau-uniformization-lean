import Yau.Proofs.P03SectionArrayGlue

open scoped Manifold Topology

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ} {M : ComplexManifold n} {ι : Type*}
variable (a : ι → M.Carrier) (r : ι → ℝ)
  (hcover : ∀ x : M.Carrier, ∃ i,
    x ∈ (extChartAt (ComplexModel n) (a i)).source ∧
    chartPt (a i) x ∈ Metric.ball (chartPt (a i) (a i)) (r i))

def sectionArrayEvaluationCLM (x : M.Carrier) :
    closedSectionArrays a r →L[ℂ] TangentVector M x :=
  let i := Classical.choose (hcover x)
  let hi := Metric.ball_subset_closedBall (Classical.choose_spec (hcover x)).2
  (mfderiv (ComplexModel n) (ComplexModel n) (extChartAt (ComplexModel n) (a i)).symm
    (chartPt (a i) x)).comp
      ((ContinuousMap.evalCLM (R := ℂ) ⟨chartPt (a i) x, hi⟩).comp
        ((ContinuousLinearMap.proj i).comp (closedSectionArrays a r).subtypeL))

@[simp]
theorem sectionArrayEvaluationCLM_apply (x : M.Carrier) (b : closedSectionArrays a r) :
    sectionArrayEvaluationCLM a r hcover x b = sectionArrayField a r hcover b x := rfl

theorem sectionArray_ballEvaluation_continuous (i : ι) :
    Continuous (fun p : closedSectionArrays a r × Metric.ball (chartPt (a i) (a i)) (r i) =>
      compactBallExtension (a i) (r i) (p.1.1 i) p.2.1) := by
  let K := chartClosedBall (a i) (r i)
  have hb : Continuous (fun p : closedSectionArrays a r × Metric.ball (chartPt (a i) (a i)) (r i) =>
      p.1.1 i) := (continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)
  have hz : Continuous (fun p : closedSectionArrays a r × Metric.ball (chartPt (a i) (a i)) (r i) =>
      (⟨p.2.1, Metric.ball_subset_closedBall p.2.2⟩ : K)) := by fun_prop
  have hc := continuous_eval.comp (hb.prodMk hz)
  exact hc.congr (fun p => by
    simp only [Function.comp_apply, compactBallExtension,
      dif_pos (Metric.ball_subset_closedBall p.2.2)])

theorem sectionArrayTuple_baire [Countable ι] (m : ℕ) :
    BaireSpace (Fin m → closedSectionArrays a r) := by
  letI := sectionArrays_completelyMetrizable a r
  letI := (closedSectionArrays_isClosed a r).isCompletelyMetrizableSpace
  infer_instance

end Yau.NodeProofs.P03Aux
