import Yau.LeafProofs.L14TwoLocalize
import Yau.LeafProofs.L14TwoAdjointChart

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

theorem weightedTwoPairing_add_right (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (u v w : NQForm E 2) (x : M.Carrier) :
    weightedTwoPairing E g h φ u (v+w) x =
      weightedTwoPairing E g h φ u v x + weightedTwoPairing E g h φ u w x := by
  simp only [weightedTwoPairing, twoFormPairing_add_right, add_mul]

theorem weightedTwoPairing_finset_sum_right (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (u : NQForm E 2) {ι : Type*} (s : Finset ι)
    (v : ι → NQForm E 2) (x : M.Carrier) :
    weightedTwoPairing E g h φ u (∑ i ∈ s, v i) x =
      ∑ i ∈ s, weightedTwoPairing E g h φ u (v i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact weightedTwoPairing_eq_zero_of_right_zero E g h φ u 0 x rfl
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, weightedTwoPairing_add_right, ih]

theorem weightedTwoPairing_sum_right (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (u : NQForm E 2) {ι : Type*} [Fintype ι]
    (v : ι → NQForm E 2) (x : M.Carrier) :
    weightedTwoPairing E g h φ u (∑ i, v i) x =
      ∑ i, weightedTwoPairing E g h φ u (v i) x :=
  weightedTwoPairing_finset_sum_right E g h φ u Finset.univ v x

variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
  (hE : Holomorphic (r := r) E)

include hμ hh hφ hE in
theorem locallyL2_weightedTwoPairing_compact_integrable
    (f W : NQForm E 2) (hf : LocallyL2 (r := r) E f) (hW : SmoothForm (r := r) E W)
    (hcW : IsCompact (closure {x | W x ≠ (0 : NQForm E 2) x})) :
    Integrable (weightedTwoPairing E g.form h φ f W) μ := by
  classical
  obtain ⟨s,F,hF,hskew,hdecomp⟩ := exists_finite_compact_two_chart_decomposition E g W hW hcW
  have he : weightedTwoPairing E g.form h φ f W = fun x =>
      ∑ i : s, weightedTwoPairing E g.form h φ f (twoFormPushforward E (i : M.Carrier) (F i)) x := by
    funext x
    rw [hdecomp, weightedTwoPairing_sum_right]
  rw [he]
  exact integrable_finsetSum _ fun i _ => weightedTwoPairing_twoFormPushforward_integrable
    E g μ hμ h hh φ hφ hE f hf (i : M.Carrier) (F i) (hF i).1 (hF i).2.1 (hF i).2.2 (hskew i)

include hE in
theorem weightedTwoDbarAdjointChartSection_smooth_compact
    (a : M.Carrier) (F : ComplexVector n → Fin n → Fin n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F) (hsF : tsupport F ⊆ localDomain (r := r) E a) :
    let R := weightedTwoDbarAdjointChartSection E g μ hμ h hh φ hφ hE a F hF hcF hsF
    SmoothForm (r := r) E R.1 ∧ IsCompact (closure {x | R.1 x ≠ (0 : NQForm E 1) x}) := by
  let R := chartTwoDbarAdjoint E g.form h φ a F
  have hR : ContDiff ℝ ∞ R := chartTwoDbarAdjoint_contDiff E g h hh φ hφ a F hF hsF
  have hsR : tsupport R ⊆ localDomain (r := r) E a := (tsupport_chartTwoDbarAdjoint_subset E g.form h φ a F).trans hsF
  have hcR : HasCompactSupport R := hcF.of_isClosed_subset (isClosed_tsupport _) (tsupport_chartTwoDbarAdjoint_subset E g.form h φ a F)
  refine ⟨oneFormPushforward_smooth E hE a R hR hcR hsR, ?_⟩
  have hK : IsCompact (chartInv a '' tsupport R) := hcR.image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := ComplexModel n) a).mono (hsR.trans Set.inter_subset_left))
  exact hK.of_isClosed_subset isClosed_closure (oneFormPushforward_support E a R hcR hsR)

include hE in
theorem smooth_compact_twoForm_has_adjoint
    (W : NQForm E 2) (hW : SmoothForm (r := r) E W)
    (hcW : IsCompact (closure {x | W x ≠ (0 : NQForm E 2) x})) :
    ∃ R : WeightedOneSection E g μ hμ h hh φ hφ,
      SmoothForm (r := r) E R.1 ∧ IsCompact (closure {x | R.1 x ≠ (0 : NQForm E 1) x}) ∧
      ∀ (U : WeightedOneSection E g μ hμ h hh φ hφ) (f : NQForm E 2),
        WeakDbar (r := r) E U.1 f →
        (∫ x, weightedTwoPairing E g.form h φ f W x ∂μ) = weightedOneInner E g.form μ h φ U.1 R.1 := by
  classical
  obtain ⟨s,F,hF,hskew,hdecomp⟩ := exists_finite_compact_two_chart_decomposition E g W hW hcW
  let R := fun i : s => weightedTwoDbarAdjointChartSection E g μ hμ h hh φ hφ hE (i : M.Carrier)
    (F i) (hF i).1 (hF i).2.1 (hF i).2.2
  refine ⟨∑ i, R i, ?_, ?_, ?_⟩
  · rw [weightedOneSection_sum_val]
    exact smoothForm_sum E (fun i => (R i).1) fun i =>
      (weightedTwoDbarAdjointChartSection_smooth_compact E g μ hμ h hh φ hφ hE (i : M.Carrier)
        (F i) (hF i).1 (hF i).2.1 (hF i).2.2).1
  · rw [weightedOneSection_sum_val]
    exact compact_formSupport_sum E (fun i => (R i).1) fun i =>
      (weightedTwoDbarAdjointChartSection_smooth_compact E g μ hμ h hh φ hφ hE (i : M.Carrier)
        (F i) (hF i).1 (hF i).2.1 (hF i).2.2).2
  · intro U f huf
    have he : weightedTwoPairing E g.form h φ f W = fun x =>
        ∑ i : s, weightedTwoPairing E g.form h φ f (twoFormPushforward E (i : M.Carrier) (F i)) x := by
      funext x
      rw [hdecomp, weightedTwoPairing_sum_right]
    rw [he, integral_finsetSum Finset.univ (fun (i : s) _ =>
      weightedTwoPairing_twoFormPushforward_integrable E g μ hμ h hh φ hφ hE f huf.2.1
        (i : M.Carrier) (F i) (hF i).1 (hF i).2.1 (hF i).2.2 (hskew i))]
    have hinner : weightedOneInner E g.form μ h φ U.1 (∑ i, R i).1 =
        ∑ i, weightedOneInner E g.form μ h φ U.1 (R i).1 := by
      change inner ℂ U (∑ i, R i) = ∑ i, inner ℂ U (R i)
      exact inner_sum (𝕜 := ℂ) Finset.univ R U
    rw [hinner]
    apply Finset.sum_congr rfl
    intro i _
    exact weakDbar_weighted_chartTwo_adjoint_pairing E g μ hμ h hh φ hφ hE U f huf (i : M.Carrier)
      (F i) (hF i).1 (hF i).2.1 (hF i).2.2 (hskew i)

theorem weakDbar_zero_of_weaklyClosed {q : ℕ} (f : NQForm E q)
    (hf : WeaklyClosed (r := r) E f) : WeakDbar (r := r) E f (0 : NQForm E (q+1)) := by
  refine ⟨hf.1, smoothForm_locallyL2 E 0 (smoothForm_zero (r := r) E (q+1)), ?_⟩
  intro a I α ψ hψ hc hs
  simp only [coefficients_zero, zero_mul, integral_zero, hf.2 a I α ψ hψ hc hs, neg_zero]

theorem weightedTwoPairing_eq_zero_left (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (W : NQForm E 2) (x : M.Carrier) :
    weightedTwoPairing E g h φ 0 W x = 0 := by
  have hz : twoFormPairing E g h (0 : NQForm E 2) W x = 0 := by
    simpa only [zero_smul, star_zero, zero_mul] using
      (twoFormPairing_smul_left E g h (0 : ℂ) (0 : NQForm E 2) W x)
  simp only [weightedTwoPairing, hz, zero_mul]

include hE in
theorem twoAdjoint_green_co_closed
    (W : NQForm E 2) (R : WeightedOneSection E g μ hμ h hh φ hφ)
    (hgreen : ∀ (U : WeightedOneSection E g μ hμ h hh φ hφ) (f : NQForm E 2),
      WeakDbar (r := r) E U.1 f →
      (∫ x, weightedTwoPairing E g.form h φ f W x ∂μ) = weightedOneInner E g.form μ h φ U.1 R.1) :
    (realizeWeightedOneSection E g μ hμ h hh φ hφ R, (0 : WeightedTopHilbert E g μ hμ h hh φ hφ)) ∈
      (weightedMaximalDbar E g μ hμ h hh φ hφ).adjoint.graph := by
  let T := weightedMaximalDbar E g μ hμ h hh φ hφ
  let v := realizeWeightedOneSection E g μ hμ h hh φ hφ R
  have hpair (x : T.domain) : inner ℂ (0 : WeightedTopHilbert E g μ hμ h hh φ hφ)
      (x : WeightedTopHilbert E g μ hμ h hh φ hφ) = inner ℂ v (T x) := by
    let D := weightedOneHilbertRepresentative E g μ hμ h hh φ hφ (T x)
    have hclosed : WeaklyClosed (r := r) E D.1 :=
      weightedMaximalDbar_apply_weaklyClosed E g μ hμ h hh φ hφ x
    have hp := hgreen D 0 (weakDbar_zero_of_weaklyClosed E D.1 hclosed)
    simp only [weightedTwoPairing_eq_zero_left, integral_zero] at hp
    have hi : inner ℂ (T x) v = 0 := by
      have he := realizeWeightedOneSection_inner E g μ hμ h hh φ hφ D R
      rw [weightedOneHilbertRepresentative_realize] at he
      exact he.trans hp.symm
    rw [inner_zero_left]
    symm
    rw [← inner_conj_symm v (T x), hi, map_zero]
  have hv : v ∈ T.adjoint.domain :=
    LinearPMap.mem_adjoint_domain_of_exists v ⟨0, hpair⟩
  have hout : T.adjoint ⟨v,hv⟩ = 0 :=
    LinearPMap.adjoint_apply_eq (weightedMaximalDbar_domain_dense E g μ hμ h hh φ hφ hE) _ hpair
  exact T.adjoint.mem_graph_iff.mpr ⟨⟨v,hv⟩,rfl,hout⟩

include hE in
theorem smooth_compact_twoForm_has_co_closed_adjoint
    (W : NQForm E 2) (hW : SmoothForm (r := r) E W)
    (hcW : IsCompact (closure {x | W x ≠ (0 : NQForm E 2) x})) :
    ∃ R : WeightedOneSection E g μ hμ h hh φ hφ,
      SmoothForm (r := r) E R.1 ∧ IsCompact (closure {x | R.1 x ≠ (0 : NQForm E 1) x}) ∧
      (realizeWeightedOneSection E g μ hμ h hh φ hφ R, (0 : WeightedTopHilbert E g μ hμ h hh φ hφ)) ∈
        (weightedMaximalDbar E g μ hμ h hh φ hφ).adjoint.graph ∧
      ∀ (U : WeightedOneSection E g μ hμ h hh φ hφ) (f : NQForm E 2),
        WeakDbar (r := r) E U.1 f →
        (∫ x, weightedTwoPairing E g.form h φ f W x ∂μ) = weightedOneInner E g.form μ h φ U.1 R.1 := by
  obtain ⟨R,hRs,hRc,hgreen⟩ := smooth_compact_twoForm_has_adjoint E g μ hμ h hh φ hφ hE W hW hcW
  exact ⟨R,hRs,hRc,twoAdjoint_green_co_closed E g μ hμ h hh φ hφ hE W R hgreen,hgreen⟩

include hE in
theorem dbar_twoAdjoint_orthogonal
    (R : WeightedOneSection E g μ hμ h hh φ hφ)
    (hR : (realizeWeightedOneSection E g μ hμ h hh φ hφ R, (0 : WeightedTopHilbert E g μ hμ h hh φ hφ)) ∈
      (weightedMaximalDbar E g μ hμ h hh φ hφ).adjoint.graph)
    (u : (weightedMaximalDbar E g μ hμ h hh φ hφ).domain) :
    inner ℂ (weightedMaximalDbar E g μ hμ h hh φ hφ u)
      (realizeWeightedOneSection E g μ hμ h hh φ hφ R) = 0 := by
  let T := weightedMaximalDbar E g μ hμ h hh φ hφ
  obtain ⟨v,hv,hTv⟩ := T.adjoint.mem_graph_iff.mp hR
  have hp := LinearPMap.adjoint_isFormalAdjoint
    (weightedMaximalDbar_domain_dense E g μ hμ h hh φ hφ hE) v u
  rw [hTv,hv,inner_zero_left] at hp
  rw [← inner_conj_symm (T u) (realizeWeightedOneSection E g μ hμ h hh φ hφ R), ← hp, map_zero]

include hE in
theorem dbar_twoAdjoint_norm_add_sq
    (R : WeightedOneSection E g μ hμ h hh φ hφ)
    (hR : (realizeWeightedOneSection E g μ hμ h hh φ hφ R, (0 : WeightedTopHilbert E g μ hμ h hh φ hφ)) ∈
      (weightedMaximalDbar E g μ hμ h hh φ hφ).adjoint.graph)
    (u : (weightedMaximalDbar E g μ hμ h hh φ hφ).domain) :
    ‖weightedMaximalDbar E g μ hμ h hh φ hφ u + realizeWeightedOneSection E g μ hμ h hh φ hφ R‖ ^ 2 =
      ‖weightedMaximalDbar E g μ hμ h hh φ hφ u‖ ^ 2 + ‖realizeWeightedOneSection E g μ hμ h hh φ hφ R‖ ^ 2 :=
  by
    simpa only [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _
      (dbar_twoAdjoint_orthogonal E g μ hμ h hh φ hφ hE R hR u)

end Yau.LeafProofs.L14Aux
