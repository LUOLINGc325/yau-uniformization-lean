import Yau.Proofs.P06FormDomain

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace ENNReal

namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint Yau.LeafProofs.L03
variable {n : ℕ} {M : ComplexManifold n}

theorem hodgeCorePair_sub (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {A W B Z : RealForm M 2}
    (hA : OperatorCandidates.HodgeCorePair g.form μ A W)
    (hB : OperatorCandidates.HodgeCorePair g.form μ B Z) :
    OperatorCandidates.HodgeCorePair g.form μ (A - B) (W - Z) := by
  simpa only [neg_one_smul ℝ B, neg_one_smul ℝ Z, ← sub_eq_add_neg] using
    hodgeCorePair_add g μ hμ hA (hodgeCorePair_smul g μ hμ (-1) hB)

/-- The original Hodge energy identity controls both actual first-order
outputs by the value and second-order graph coordinates. -/
theorem hodgeCore_energy_bound (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A W : RealForm M 2)
    (hc : OperatorCandidates.HodgeCorePair g.form μ A W) :
    ‖realizeActualForm g μ (exteriorRealForm A)
      (exteriorRealForm_l2 g μ hμ A hc.1 hc.2.1)‖ ≤
        ‖realizeActualForm g μ A hc.2.2.2.1‖ + ‖realizeActualForm g μ W hc.2.2.2.2.1‖ ∧
    ‖realizeActualForm g μ (codifferentialRealForm g.form A)
      (codifferentialRealForm_l2 g μ hμ A hc.1 hc.2.1)‖ ≤
        ‖realizeActualForm g μ A hc.2.2.2.1‖ + ‖realizeActualForm g μ W hc.2.2.2.2.1‖ := by
  have hW : W = hodgeRealForm g.form 2 A :=
    ((hodgeCorePair_iff_computed g μ hμ A W).mp hc).2.2
  have he := integral_hodgeRealForm_succ_energy g μ hμ A A hc.1 hc.1 hc.2.1 hc.2.1
  rw [← hW] at he
  let a := realizeActualForm g μ A hc.2.2.2.1
  let w := realizeActualForm g μ W hc.2.2.2.2.1
  let d := realizeActualForm g μ (exteriorRealForm A) (exteriorRealForm_l2 g μ hμ A hc.1 hc.2.1)
  let δ := realizeActualForm g μ (codifferentialRealForm g.form A)
    (codifferentialRealForm_l2 g μ hμ A hc.1 hc.2.1)
  have heq : ‖d‖ ^ 2 + ‖δ‖ ^ 2 = inner ℝ w a := by
    rw [show inner ℝ w a = ∫ y, formInner g.form W A y ∂μ from
      realizeL2Form_inner g μ _ _]
    rw [he]
    simp only [d, δ, realizeActualForm_norm_sq, formNormSq, add_comm]
  have hcs := real_inner_le_norm w a
  have hd0 := norm_nonneg d
  have hδ0 := norm_nonneg δ
  have ha0 := norm_nonneg a
  have hw0 := norm_nonneg w
  constructor <;> change _ ≤ ‖a‖ + ‖w‖ <;>
    nlinarith [sq_nonneg ‖d‖, sq_nonneg ‖δ‖, sq_nonneg (‖a‖ - ‖w‖)]

/-- Second-order compact-core graph convergence forces both first-order
derivative sequences to be Cauchy in their genuine L² Hilbert completions. -/
theorem hodgeCore_derivatives_cauchy (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (As Ws : ℕ → RealForm M 2)
    (hc : ∀ j, OperatorCandidates.HodgeCorePair g.form μ (As j) (Ws j))
    (hA : CauchySeq (fun j => realizeActualForm g μ (As j) (hc j).2.2.2.1))
    (hW : CauchySeq (fun j => realizeActualForm g μ (Ws j) (hc j).2.2.2.2.1)) :
    CauchySeq (fun j => realizeActualForm g μ (exteriorRealForm (As j))
      (exteriorRealForm_l2 g μ hμ _ (hc j).1 (hc j).2.1)) ∧
    CauchySeq (fun j => realizeActualForm g μ (codifferentialRealForm g.form (As j))
      (codifferentialRealForm_l2 g μ hμ _ (hc j).1 (hc j).2.1)) := by
  have hδsub (i j : ℕ) : codifferentialRealForm g.form (As i - As j) =
      codifferentialRealForm g.form (As i) - codifferentialRealForm g.form (As j) := by
    exact hodgeLowerRealForm_sub g μ hμ (As i) (As j) (hc i).1 (hc j).1
  have hdsub (i j : ℕ) := exteriorRealForm_sub (As i) (As j) (hc i).1 (hc j).1
  constructor
  · apply cauchySeq_of_two_dist_bound _ _ _ hA hW 1 1 zero_le_one zero_le_one
    intro i j
    have hb := (hodgeCore_energy_bound g μ hμ _ _ (hodgeCorePair_sub g μ hμ (hc i) (hc j))).1
    simp only [dist_eq_norm, one_mul]
    rw [← realizeActualForm_sub, ← realizeActualForm_sub, ← realizeActualForm_sub]
    simpa only [hdsub] using hb
  · apply cauchySeq_of_two_dist_bound _ _ _ hA hW 1 1 zero_le_one zero_le_one
    intro i j
    have hb := (hodgeCore_energy_bound g μ hμ _ _ (hodgeCorePair_sub g μ hμ (hc i) (hc j))).2
    simp only [dist_eq_norm, one_mul]
    rw [← realizeActualForm_sub, ← realizeActualForm_sub, ← realizeActualForm_sub]
    simpa only [hδsub] using hb

/-- The original second-order minimal Hodge graph supplies genuine raw
first-order graph-domain data. No derivative representative is assumed. -/
theorem hodgeMinimalGraph_friedrichs (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {A W : RealForm M 2}
    (h : OperatorCandidates.HodgeMinimalGraph g.form μ A W) :
    FriedrichsHodgeRelation g.form μ A W := by
  obtain ⟨hAL, hWL, As, Ws, hc, ht⟩ := h
  have htA : Tendsto (fun j => formL2DistanceSq g.form μ (As j) A) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => bot_le)
      (fun _ => le_add_of_nonneg_right (by positivity))
  have htW : Tendsto (fun j => formL2DistanceSq g.form μ (Ws j) W) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => bot_le)
      (fun _ => le_add_of_nonneg_left (by positivity))
  have hu := ((tendsto_realizeL2Form_iff g μ
    (fun j => L2FormSpace.ofSection (As j) (hc j).2.2.2.1)
    (L2FormSpace.ofSection A hAL)).mpr htA).cauchySeq
  have hv := ((tendsto_realizeL2Form_iff g μ
    (fun j => L2FormSpace.ofSection (Ws j) (hc j).2.2.2.2.1)
    (L2FormSpace.ofSection W hWL)).mpr htW).cauchySeq
  obtain ⟨hdc, hδc⟩ := hodgeCore_derivatives_cauchy g μ hμ As Ws hc hu hv
  obtain ⟨d, hdt⟩ := cauchySeq_tendsto_of_complete hdc
  obtain ⟨δ, hδt⟩ := cauchySeq_tendsto_of_complete hδc
  obtain ⟨dA, hdAL, hdeq⟩ := l2FormHilbert_exists_section g μ d
  obtain ⟨δA, hδAL, hδeq⟩ := l2FormHilbert_exists_section g μ δ
  have htd : Tendsto (fun j => formL2DistanceSq g.form μ (exteriorRealForm (As j)) dA)
      atTop (𝓝 0) := by
    apply (tendsto_realizeL2Form_iff g μ
      (fun j => L2FormSpace.ofSection (exteriorRealForm (As j))
        (exteriorRealForm_l2 g μ hμ _ (hc j).1 (hc j).2.1)) (L2FormSpace.ofSection dA hdAL)).mp
    rw [hdeq]
    exact hdt
  have htδ : Tendsto (fun j => formL2DistanceSq g.form μ (codifferentialRealForm g.form (As j)) δA)
      atTop (𝓝 0) := by
    apply (tendsto_realizeL2Form_iff g μ
      (fun j => L2FormSpace.ofSection (codifferentialRealForm g.form (As j))
        (codifferentialRealForm_l2 g μ hμ _ (hc j).1 (hc j).2.1)) (L2FormSpace.ofSection δA hδAL)).mp
    rw [hδeq]
    exact hδt
  have hgraph : HodgeFormGraphClosure g.form μ A dA δA := by
    refine ⟨hAL, hdAL, hδAL, As, (fun j => exteriorRealForm (As j)),
      (fun j => codifferentialRealForm g.form (As j)), ?_, ?_⟩
    · intro j
      exact ⟨(hc j).1, (hc j).2.1, exteriorRealForm_smooth _ (hc j).1,
        exteriorRealForm_represents _ (hc j).1, codifferentialRealForm_smooth g μ hμ _ (hc j).1,
        codifferentialRealForm_represents g μ hμ _ (hc j).1,
        (hc j).2.2.2.1, exteriorRealForm_l2 g μ hμ _ (hc j).1 (hc j).2.1,
        codifferentialRealForm_l2 g μ hμ _ (hc j).1 (hc j).2.1⟩
    · simpa only [zero_add] using (htA.add htd).add htδ
  refine ⟨hWL, dA, δA, hgraph, ?_⟩
  intro V dV δV hV
  refine ⟨formInner_integrable g μ _ _ hdAL hV.2.1,
    formInner_integrable g μ _ _ hδAL hV.2.2.1,
    formInner_integrable g μ _ _ hWL hV.1, ?_⟩
  have hdlim := formL2DistanceSq_tendsto_integral_pairing g μ _ dA dV
    (fun j => exteriorRealForm_l2 g μ hμ _ (hc j).1 (hc j).2.1) hdAL hV.2.1 htd
  have hδlim := formL2DistanceSq_tendsto_integral_pairing g μ _ δA δV
    (fun j => codifferentialRealForm_l2 g μ hμ _ (hc j).1 (hc j).2.1) hδAL hV.2.2.1 htδ
  have hwlim := formL2DistanceSq_tendsto_integral_pairing g μ Ws W V
    (fun j => (hc j).2.2.2.2.1) hWL hV.1 htW
  have he (j : ℕ) :
      (∫ y, formInner g.form (exteriorRealForm (As j)) dV y ∂μ) +
        (∫ y, formInner g.form (codifferentialRealForm g.form (As j)) δV y ∂μ) =
          ∫ y, formInner g.form (Ws j) V y ∂μ := by
    have hw : Ws j = hodgeRealForm g.form 2 (As j) :=
      ((hodgeCorePair_iff_computed g μ hμ (As j) (Ws j)).mp (hc j)).2.2
    rw [hw, formInner_symm g.form (exteriorRealForm (As j)) dV,
      formInner_symm g.form (codifferentialRealForm g.form (As j)) δV,
      formInner_symm g.form (hodgeRealForm g.form 2 (As j)) V]
    exact formGraph_energy_pairing g μ hμ hV (As j) (hc j).1 (hc j).2.1
  exact tendsto_nhds_unique (hdlim.add hδlim)
    (hwlim.congr' (Eventually.of_forall fun j => (he j).symm))

theorem hodgeMinimalGraph_formGraph (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {A W : RealForm M 2}
    (h : OperatorCandidates.HodgeMinimalGraph g.form μ A W) :
    ∃ dA : RealForm M 3, ∃ δA : RealForm M 1, HodgeFormGraphClosure g.form μ A dA δA := by
  obtain ⟨_, dA, δA, hgraph, _⟩ := hodgeMinimalGraph_friedrichs g μ hμ h
  exact ⟨dA, δA, hgraph⟩

end Yau.NodeProofs.P06Aux
