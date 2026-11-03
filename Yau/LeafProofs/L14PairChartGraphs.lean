import Yau.LeafProofs.L14PairModelOutputs
import Yau.LeafProofs.L14PairCauchy
import Yau.LeafProofs.L14TwoAdjointGraph

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder ENNReal
open MeasureTheory Bundle Filter Module
namespace Yau.LeafProofs.L14Aux
open BundleDbar
variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)] [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem oneForm_eq_of_chart_coefficients (u v : NQForm E 1) (a : M.Carrier)
    (hzero : ∀ x,x ∉ bundleChartSource (r := r) E a → u x = v x)
    (hcoeff : ∀ z ∈ localDomain (r := r) E a,∀ i α,
      coefficients (r := r) E u a z (fun _ => i) α = coefficients (r := r) E v a z (fun _ => i) α) : u = v := by
  funext x
  by_cases hx : x ∈ bundleChartSource (r := r) E a
  · have hz : chartPt a x ∈ localDomain (r := r) E a := by
      refine ⟨(extChartAt (ComplexModel n) a).map_source hx.1,?_⟩
      change chartInv a (chartPt a x) ∈ (localTriv (r := r) E a).baseSet
      rw [chartInv_chartPt_of_mem a x (by simpa only [extChartAt_source] using hx.1)]
      exact hx.2
    apply oneTensorCoordinates_injective E a x hx
    ext p
    rw [oneTensorCoordinates_at_chartPt E u a x hx p.1 p.2,oneTensorCoordinates_at_chartPt E v a x hx p.1 p.2]
    exact hcoeff _ hz p.1 p.2
  · exact hzero x hx

theorem oneFormPushforward_add (a : M.Carrier) (F G : ComplexVector n → Fin n → ComplexVector r) :
    oneFormPushforward (r := r) E a (fun z j => F z j+G z j) =
      oneFormPushforward (r := r) E a F+oneFormPushforward (r := r) E a G := by
  classical
  apply oneForm_eq_of_chart_coefficients (r := r) E _ _ a
  · intro x hx
    apply Subtype.ext
    rw [nqForm_add_apply]
    simp only [oneFormPushforward,dite_eq_right hx,Submodule.coe_zero,zero_add]
  · intro z hz i α
    rw [coefficients_add,oneFormPushforward_coefficients E a _ z hz,
      oneFormPushforward_coefficients E a F z hz,oneFormPushforward_coefficients E a G z hz]
    rfl

variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
  (hE : Holomorphic (r := r) E)

include hE in
theorem weightedTopChartSection_dbar_graph
    (a : M.Carrier) (A : ComplexVector n → ComplexVector r) (hA : ContDiff ℝ ∞ A)
    (hcA : HasCompactSupport A) (hsA : tsupport A ⊆ localDomain (r := r) E a) :
    (realizeWeightedTopSection E g μ hμ h hh φ hφ (weightedTopChartSection E g μ hμ h hh φ hφ hE a A hA hcA hsA),
      realizeWeightedOneSection E g μ hμ h hh φ hφ
        (weightedOneChartSection E g μ hμ h hh φ hφ hE a (modelTopDbar A) (modelTopDbar_smooth A hA)
          (hcA.of_isClosed_subset (isClosed_tsupport _) (tsupport_modelTopDbar_subset A))
          ((tsupport_modelTopDbar_subset A).trans hsA))) ∈
      (weightedMaximalDbar E g μ hμ h hh φ hφ).graph := by
  rw [weightedMaximalDbar_graph]
  apply (weightedMaximalDbarHilbertGraph_realize_iff E g μ hμ h hh φ hφ _ _).mpr
  exact (topFormPushforward_maximalDbarGraph E g μ hμ h hh φ hφ hE a A hA hcA hsA).2.2

include hE in
theorem weightedTwoDbarAdjointChartSection_co_closed
    (a : M.Carrier) (F : ComplexVector n → Fin n → Fin n → ComplexVector r)
    (hskew : ∀ z i j,F z j i = -F z i j) (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F)
    (hsF : tsupport F ⊆ localDomain (r := r) E a) :
    (realizeWeightedOneSection E g μ hμ h hh φ hφ (weightedTwoDbarAdjointChartSection E g μ hμ h hh φ hφ hE a F hF hcF hsF),
      (0 : WeightedTopHilbert E g μ hμ h hh φ hφ)) ∈ (weightedMaximalDbar E g μ hμ h hh φ hφ).adjoint.graph :=
  weightedTwoAdjointGraph_co_closed E g μ hμ h hh φ hφ hE _ _
    (weightedTwoAdjointGraph_chart E g μ hμ h hh φ hφ hE a F hskew hF hcF hsF)

include hE in
theorem dbar_twoAdjointGraph_orthogonal
    (u : WeightedTopHilbert E g μ hμ h hh φ hφ) (A : WeightedOneHilbert E g μ hμ h hh φ hφ)
    (W : WeightedTwoHilbert E g μ hμ h hh φ hφ) (B : WeightedOneHilbert E g μ hμ h hh φ hφ)
    (hT : (u,A) ∈ (weightedMaximalDbar E g μ hμ h hh φ hφ).graph)
    (hG : (W,B) ∈ weightedTwoAdjointGraph E g μ hμ h hh φ hφ) : inner ℂ A B = 0 := by
  let T := weightedMaximalDbar E g μ hμ h hh φ hφ
  have hB := weightedTwoAdjointGraph_co_closed E g μ hμ h hh φ hφ hE W B hG
  obtain ⟨v,hv,hTv⟩ := T.adjoint.mem_graph_iff.mp hB
  obtain ⟨x,hx,hTx⟩ := T.mem_graph_iff.mp hT
  have hp := LinearPMap.adjoint_isFormalAdjoint (weightedMaximalDbar_domain_dense E g μ hμ h hh φ hφ hE) v x
  rw [hTv,hv,hTx,hx,inner_zero_left] at hp
  rw [← inner_conj_symm A B,← hp,map_zero]

include hE in
theorem dbar_twoAdjointGraph_cauchy_components
    (u : ℕ → WeightedTopHilbert E g μ hμ h hh φ hφ)
    (A B : ℕ → WeightedOneHilbert E g μ hμ h hh φ hφ)
    (W : ℕ → WeightedTwoHilbert E g μ hμ h hh φ hφ)
    (hT : ∀ j,(u j,A j) ∈ (weightedMaximalDbar E g μ hμ h hh φ hφ).graph)
    (hG : ∀ j,(W j,B j) ∈ weightedTwoAdjointGraph E g μ hμ h hh φ hφ)
    (hSum : CauchySeq (fun j => A j+B j)) : CauchySeq A ∧ CauchySeq B := by
  apply cauchySeq_pair_of_norm_sub_sq A B _ hSum
  intro j k
  have hTD := Submodule.sub_mem (weightedMaximalDbar E g μ hμ h hh φ hφ).graph (hT j) (hT k)
  change (u j-u k,A j-A k) ∈ (weightedMaximalDbar E g μ hμ h hh φ hφ).graph at hTD
  have hGD := Submodule.sub_mem (weightedTwoAdjointGraph E g μ hμ h hh φ hφ) (hG j) (hG k)
  change (W j-W k,B j-B k) ∈ weightedTwoAdjointGraph E g μ hμ h hh φ hφ at hGD
  have horth := dbar_twoAdjointGraph_orthogonal E g μ hμ h hh φ hφ hE _ _ _ _ hTD hGD
  have he : ‖(A j-A k)+(B j-B k)‖^2 = ‖A j-A k‖^2+‖B j-B k‖^2 := by
    simpa only [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  convert he using 1 <;> congr 1 <;> abel

include hE in
theorem exists_twoAdjointGraph_limit_of_joint_cauchy
    (u : ℕ → WeightedTopHilbert E g μ hμ h hh φ hφ)
    (A B : ℕ → WeightedOneHilbert E g μ hμ h hh φ hφ)
    (W : ℕ → WeightedTwoHilbert E g μ hμ h hh φ hφ)
    (hT : ∀ j,(u j,A j) ∈ (weightedMaximalDbar E g μ hμ h hh φ hφ).graph)
    (hG : ∀ j,(W j,B j) ∈ weightedTwoAdjointGraph E g μ hμ h hh φ hφ)
    (hSum : CauchySeq (fun j => A j+B j))
    (w : WeightedTwoHilbert E g μ hμ h hh φ hφ) (hW : Tendsto W atTop (𝓝 w)) :
    ∃ b : WeightedOneHilbert E g μ hμ h hh φ hφ,Tendsto B atTop (𝓝 b) ∧ (w,b) ∈ weightedTwoAdjointGraph E g μ hμ h hh φ hφ := by
  obtain ⟨b,hb⟩ := cauchySeq_tendsto_of_complete (dbar_twoAdjointGraph_cauchy_components E g μ hμ h hh φ hφ hE u A B W hT hG hSum).2
  exact ⟨b,hb,weightedTwoAdjointGraph_closed_limit E g μ hμ h hh φ hφ W B w b hG hW hb⟩

variable (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K)
  (hKO : K ⊆ localDomain (r := r) E a)
  (F : ComplexVector n → PairSystemInputIndex n r → ℂ)
  (hF : ∀ c,ContDiff ℝ ∞ (fun z => F z c)) (hsF : ∀ c,tsupport (fun z => F z c) ⊆ K)

include hE in
def pairChartTopSection : WeightedTopSection E g μ hμ h hh φ hφ :=
  let hp := pairModels_properties F hF hK.isClosed hsF
  weightedTopChartSection E g μ hμ h hh φ hφ hE a (pairModelTop F) hp.1
    (hK.of_isClosed_subset (isClosed_tsupport _) hp.2.2.1) (hp.2.2.1.trans hKO)

include hE in
def pairChartDbarSection : WeightedOneSection E g μ hμ h hh φ hφ :=
  let hp := pairModels_properties F hF hK.isClosed hsF
  weightedOneChartSection E g μ hμ h hh φ hφ hE a (modelTopDbar (pairModelTop F))
    (modelTopDbar_smooth _ hp.1)
    (hK.of_isClosed_subset (isClosed_tsupport _) ((tsupport_modelTopDbar_subset _).trans hp.2.2.1))
    (((tsupport_modelTopDbar_subset _).trans hp.2.2.1).trans hKO)

include hE in
def pairChartTwoSection : WeightedTwoSection E g μ hμ h hh φ hφ :=
  let hp := pairModels_properties F hF hK.isClosed hsF
  let hAlt := alternatingTwoModel_properties (pairModelTwo F) hp.2.1
    (hK.of_isClosed_subset (isClosed_tsupport _) hp.2.2.2)
  weightedTwoChartSection E g μ hμ h hh φ hφ hE a (alternatingTwoModel (pairModelTwo F))
    (alternatingTwoModel_skew _) hAlt.1 hAlt.2.1 (hAlt.2.2.trans (hp.2.2.2.trans hKO))

include hE in
def pairChartAdjointSection : WeightedOneSection E g μ hμ h hh φ hφ :=
  let hp := pairModels_properties F hF hK.isClosed hsF
  let hAlt := alternatingTwoModel_properties (pairModelTwo F) hp.2.1
    (hK.of_isClosed_subset (isClosed_tsupport _) hp.2.2.2)
  weightedTwoDbarAdjointChartSection E g μ hμ h hh φ hφ hE a (alternatingTwoModel (pairModelTwo F))
    hAlt.1 hAlt.2.1 (hAlt.2.2.trans (hp.2.2.2.trans hKO))

include hE in
def pairChartSumSection : WeightedOneSection E g μ hμ h hh φ hφ :=
  let hp := pairOneOutputModel_properties E g h hh φ hφ a F hF K hK hKO hsF
  weightedOneChartSection E g μ hμ h hh φ hφ hE a (pairOneOutputModel (r := r) E g.form h φ a F) hp.1
    (hK.of_isClosed_subset (isClosed_tsupport _) hp.2) (hp.2.trans hKO)

include hE in
theorem pairChartTop_dbar_graph :
    (realizeWeightedTopSection E g μ hμ h hh φ hφ (pairChartTopSection E g μ hμ h hh φ hφ hE a K hK hKO F hF hsF),
      realizeWeightedOneSection E g μ hμ h hh φ hφ (pairChartDbarSection E g μ hμ h hh φ hφ hE a K hK hKO F hF hsF)) ∈
      (weightedMaximalDbar E g μ hμ h hh φ hφ).graph :=
  weightedTopChartSection_dbar_graph E g μ hμ h hh φ hφ hE a (pairModelTop F)
    (pairModels_properties F hF hK.isClosed hsF).1
    (hK.of_isClosed_subset (isClosed_tsupport _) (pairModels_properties F hF hK.isClosed hsF).2.2.1)
    ((pairModels_properties F hF hK.isClosed hsF).2.2.1.trans hKO)

include hE in
theorem pairChartTwo_adjoint_graph :
    (realizeWeightedTwoSection E g μ hμ h hh φ hφ (pairChartTwoSection E g μ hμ h hh φ hφ hE a K hK hKO F hF hsF),
      realizeWeightedOneSection E g μ hμ h hh φ hφ (pairChartAdjointSection E g μ hμ h hh φ hφ hE a K hK hKO F hF hsF)) ∈
      weightedTwoAdjointGraph E g μ hμ h hh φ hφ := by
  let hp := pairModels_properties F hF hK.isClosed hsF
  let hAlt := alternatingTwoModel_properties (pairModelTwo F) hp.2.1
    (hK.of_isClosed_subset (isClosed_tsupport _) hp.2.2.2)
  exact weightedTwoAdjointGraph_chart E g μ hμ h hh φ hφ hE a (alternatingTwoModel (pairModelTwo F))
    (alternatingTwoModel_skew _) hAlt.1 hAlt.2.1 (hAlt.2.2.trans (hp.2.2.2.trans hKO))

include hE in
theorem pairChartSum_decomposition :
    realizeWeightedOneSection E g μ hμ h hh φ hφ (pairChartSumSection E g μ hμ h hh φ hφ hE a K hK hKO F hF hsF) =
      realizeWeightedOneSection E g μ hμ h hh φ hφ (pairChartDbarSection E g μ hμ h hh φ hφ hE a K hK hKO F hF hsF)+
        realizeWeightedOneSection E g μ hμ h hh φ hφ (pairChartAdjointSection E g μ hμ h hh φ hφ hE a K hK hKO F hF hsF) := by
  have hsec : pairChartSumSection E g μ hμ h hh φ hφ hE a K hK hKO F hF hsF =
      pairChartDbarSection E g μ hμ h hh φ hφ hE a K hK hKO F hF hsF+
        pairChartAdjointSection E g μ hμ h hh φ hφ hE a K hK hKO F hF hsF := by
    apply Subtype.ext
    exact oneFormPushforward_add E a (modelTopDbar (pairModelTop F))
      (chartTwoDbarAdjoint E g.form h φ a (alternatingTwoModel (pairModelTwo F)))
  rw [hsec]
  exact UniformSpace.Completion.coe_add _ _

include hE in
theorem pairChartAdjoint_limit_of_graph_errors
    (Fm : ℕ → ComplexVector n → PairSystemInputIndex n r → ℂ)
    (hFm : ∀ m c,ContDiff ℝ ∞ (fun z => Fm m z c))
    (hsFm : ∀ m c,tsupport (fun z => Fm m z c) ⊆ K)
    (v : ComplexVector n → (Fin n × Fin r) → ℂ) (hsv : ∀ row,tsupport (fun z => v z row) ⊆ K)
    (he : ∀ m row,MemLp (fun z => complexFirstOrderSystemApply realVec
      (alternatingPairFirstOrderDerivative (r := r) E g.form h φ a) (alternatingPairFirstOrderValue (r := r) E g.form h φ a)
      (Fm m) z row-v z row) 2 (lebesgueC n))
    (ht : ∀ row,Tendsto (fun m => ∫ z,‖complexFirstOrderSystemApply realVec
      (alternatingPairFirstOrderDerivative (r := r) E g.form h φ a) (alternatingPairFirstOrderValue (r := r) E g.form h φ a)
      (Fm m) z row-v z row‖^2 ∂lebesgueC n) atTop (𝓝 0))
    (w : WeightedTwoHilbert E g μ hμ h hh φ hφ)
    (hW : Tendsto (fun m => realizeWeightedTwoSection E g μ hμ h hh φ hφ
      (pairChartTwoSection E g μ hμ h hh φ hφ hE a K hK hKO (Fm m) (hFm m) (hsFm m))) atTop (𝓝 w)) :
    ∃ b : WeightedOneHilbert E g μ hμ h hh φ hφ,
      Tendsto (fun m => realizeWeightedOneSection E g μ hμ h hh φ hφ
        (pairChartAdjointSection E g μ hμ h hh φ hφ hE a K hK hKO (Fm m) (hFm m) (hsFm m))) atTop (𝓝 b) ∧
      (w,b) ∈ weightedTwoAdjointGraph E g μ hμ h hh φ hφ := by
  let U := fun m => realizeWeightedTopSection E g μ hμ h hh φ hφ
    (pairChartTopSection E g μ hμ h hh φ hφ hE a K hK hKO (Fm m) (hFm m) (hsFm m))
  let A := fun m => realizeWeightedOneSection E g μ hμ h hh φ hφ
    (pairChartDbarSection E g μ hμ h hh φ hφ hE a K hK hKO (Fm m) (hFm m) (hsFm m))
  let B := fun m => realizeWeightedOneSection E g μ hμ h hh φ hφ
    (pairChartAdjointSection E g μ hμ h hh φ hφ hE a K hK hKO (Fm m) (hFm m) (hsFm m))
  let W := fun m => realizeWeightedTwoSection E g μ hμ h hh φ hφ
    (pairChartTwoSection E g μ hμ h hh φ hφ hE a K hK hKO (Fm m) (hFm m) (hsFm m))
  have hsum : CauchySeq (fun m => A m+B m) := by
    have hp := pairOneOutputModel_cauchySeq_of_graph_errors E g μ hμ h hh φ hφ hE a K hK hKO Fm hFm hsFm v hsv he ht
    change CauchySeq (fun m => realizeWeightedOneSection E g μ hμ h hh φ hφ
      (pairChartSumSection E g μ hμ h hh φ hφ hE a K hK hKO (Fm m) (hFm m) (hsFm m))) at hp
    have hfun : (fun m => realizeWeightedOneSection E g μ hμ h hh φ hφ
      (pairChartSumSection E g μ hμ h hh φ hφ hE a K hK hKO (Fm m) (hFm m) (hsFm m))) = fun m => A m+B m := by
      funext m
      exact pairChartSum_decomposition E g μ hμ h hh φ hφ hE a K hK hKO (Fm m) (hFm m) (hsFm m)
    rwa [hfun] at hp
  exact exists_twoAdjointGraph_limit_of_joint_cauchy E g μ hμ h hh φ hφ hE U A B W
    (fun m => pairChartTop_dbar_graph E g μ hμ h hh φ hφ hE a K hK hKO (Fm m) (hFm m) (hsFm m))
    (fun m => pairChartTwo_adjoint_graph E g μ hμ h hh φ hφ hE a K hK hKO (Fm m) (hFm m) (hsFm m)) hsum w hW

end Yau.LeafProofs.L14Aux
