import Yau.LeafProofs.L14CompactTwoAdjoint

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
variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
  (hE : Holomorphic (r := r) E)

theorem weightedOnePairing_oneFormPushforward_density
    (u : NQForm E 1) (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r)
    (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) :
    Real.sqrt (realMetricFn g.form a z).det •
      weightedOnePairing E g.form h φ u (oneFormPushforward E a F) (chartInv a z) =
      (2 : ℝ)^n • (∑ i, ∑ α, star (coefficients (r := r) E u a z (fun _ => i) α) *
        chartOneDual E g.form h φ a F z i α) := by
  classical
  rw [weightedOnePairing, oneFormPairing_inChart E g.form h u _ a z hz,
    realMetricFn_sqrt_det g.form a z hz.1]
  simp_rw [oneFormPushforward_coefficients E a F z hz]
  dsimp only [chartOneDual]
  simp only [Complex.real_smul, Complex.ofReal_mul]
  have hd : ((hMat g.form a z).det.re : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (L18Aux.hMat_det_re_pos g.form a hz.1))
  simp only [div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro β _
  field_simp [hd]

include hh hφ in
theorem chartOneDual_conjugate_test_integrable
    (u : NQForm E 1) (hu : LocallyL2 (r := r) E u) (a : M.Carrier)
    (F : ComplexVector n → Fin n → ComplexVector r) (hF : ContDiff ℝ ∞ F)
    (hcF : HasCompactSupport F) (hsF : tsupport F ⊆ localDomain (r := r) E a)
    (i : Fin n) (α : Fin r) :
    Integrable (fun z => star (coefficients (r := r) E u a z (fun _ => i) α) *
      chartOneDual E g.form h φ a F z i α) (lebesgueC n) := by
  have hs := tsupport_chartOneDual_subset E g.form h φ a F i α
  exact locallyL2_conjugate_test_integrable E u hu a (fun _ => i) α _
    (chartOneDual_contDiff E g h hh φ hφ a F hF hsF i α).continuous
    (hcF.of_isClosed_subset (isClosed_tsupport _) hs) (hs.trans hsF)

include hμ hh hφ hE in
theorem locallyL2_weightedOnePairing_oneFormPushforward_integrable
    (u : NQForm E 1) (hu : LocallyL2 (r := r) E u) (a : M.Carrier)
    (F : ComplexVector n → Fin n → ComplexVector r) (hF : ContDiff ℝ ∞ F)
    (hcF : HasCompactSupport F) (hsF : tsupport F ⊆ localDomain (r := r) E a) :
    Integrable (weightedOnePairing E g.form h φ u (oneFormPushforward E a F)) μ := by
  classical
  let v := oneFormPushforward (r := r) E a F
  let Q := fun z => ∑ i, ∑ α, star (coefficients (r := r) E u a z (fun _ => i) α) *
    chartOneDual E g.form h φ a F z i α
  have hQ : Integrable Q (lebesgueC n) := integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun α _ =>
    chartOneDual_conjugate_test_integrable E g h hh φ hφ u hu a F hF hcF hsF i α
  have hv : LocallyL2 (r := r) E v := smoothForm_locallyL2 E v
    (oneFormPushforward_smooth E hE a F hF hcF hsF)
  have hw : AEMeasurable (fun x => (Real.exp (-φ x) : ℂ)) μ :=
    Complex.continuous_ofReal.measurable.comp_aemeasurable
      (Real.continuous_exp.comp (L18Aux.continuous_of_smoothFn hφ).neg).measurable.aemeasurable
  have hm : AEMeasurable (weightedOnePairing E g.form h φ u v) μ :=
    (oneFormPairing_aemeasurable E g μ hμ h hh u v hu hv).mul hw
  apply integrable_of_bundleChart_density (r := r) E g μ hμ a _ Q hm hQ
  · intro x hx
    apply weightedOnePairing_eq_zero_of_right_zero
    change (if hy : x ∈ bundleChartSource (r := r) E a then _ else _) = _
    exact dite_eq_right hx
  · exact weightedOnePairing_oneFormPushforward_density E g h φ u a F

include hμ hh hφ hE in
theorem locallyL2_weightedOneInner_oneFormPushforward
    (u : NQForm E 1) (hu : LocallyL2 (r := r) E u) (a : M.Carrier)
    (F : ComplexVector n → Fin n → ComplexVector r) (hF : ContDiff ℝ ∞ F)
    (hcF : HasCompactSupport F) (hsF : tsupport F ⊆ localDomain (r := r) E a) :
    weightedOneInner E g.form μ h φ u (oneFormPushforward E a F) =
      (2 : ℝ)^n • ∫ z, (∑ i, ∑ α, star (coefficients (r := r) E u a z (fun _ => i) α) *
        chartOneDual E g.form h φ a F z i α) ∂lebesgueC n := by
  classical
  let v := oneFormPushforward (r := r) E a F
  let P := weightedOnePairing E g.form h φ u v
  let Q := fun z => ∑ i, ∑ α, star (coefficients (r := r) E u a z (fun _ => i) α) *
    chartOneDual E g.form h φ a F z i α
  have hP := locallyL2_weightedOnePairing_oneFormPushforward_integrable E g μ hμ h hh φ hφ hE u hu a F hF hcF hsF
  have hPzero (x : M.Carrier) (hx : x ∉ bundleChartSource (r := r) E a) : P x = 0 := by
    apply weightedOnePairing_eq_zero_of_right_zero
    change (if hy : x ∈ bundleChartSource (r := r) E a then _ else _) = _
    exact dite_eq_right hx
  have hFzero (z : ComplexVector n) (hz : z ∉ localDomain (r := r) E a) : F z = 0 := by
    by_contra hn
    exact hz (hsF (subset_tsupport F hn))
  have hQzero (z : ComplexVector n) (hz : z ∉ localDomain (r := r) E a) : Q z = 0 := by
    simp [Q,chartOneDual,hFzero z hz]
  apply integral_of_compact_chart_density g μ hμ a P Q hP
    (fun x hx => hPzero x (fun hy => hx hy.1)) (fun z hz => hQzero z (fun hy => hz hy.1))
  intro z hz
  by_cases hzo : z ∈ localDomain (r := r) E a
  · exact weightedOnePairing_oneFormPushforward_density E g h φ u a F z hzo
  · rw [hPzero (chartInv a z) (fun hy => hzo ⟨hz,hy.2⟩),hQzero z hzo]
    simp

include hμ hh hφ hE in
theorem rough_weakDbar_weighted_chartTwo_adjoint_pairing
    (u : NQForm E 1) (f : NQForm E 2)
    (huf : WeakDbar (r := r) E u f)
    (a : M.Carrier) (F : ComplexVector n → Fin n → Fin n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F) (hsF : tsupport F ⊆ localDomain (r := r) E a)
    (hskew : ∀ z i j, F z j i = -F z i j) :
    (∫ x, weightedTwoPairing E g.form h φ f (twoFormPushforward (r := r) E a F) x ∂μ) =
      weightedOneInner E g.form μ h φ u
        (oneFormPushforward (r := r) E a (chartTwoDbarAdjoint E g.form h φ a F)) := by
  classical
  let R := chartTwoDbarAdjoint E g.form h φ a F
  have hR : ContDiff ℝ ∞ R := chartTwoDbarAdjoint_contDiff E g h hh φ hφ a F hF hsF
  have hsR : tsupport R ⊆ tsupport F := tsupport_chartTwoDbarAdjoint_subset E g.form h φ a F
  have hcR : HasCompactSupport R := hcF.of_isClosed_subset (isClosed_tsupport _) hsR
  have hi (j : Fin n) (α : Fin r) : Integrable
      (fun z => star (coefficients (r := r) E u a z (fun _ => j) α) * chartOneDual (r := r) E g.form h φ a R z j α)
      (lebesgueC n) := by
    have hs := tsupport_chartOneDual_subset E g.form h φ a R j α
    exact locallyL2_star_test_integrable E u huf.1 a (fun _ => j) α _
      (chartOneDual_contDiff E g h hh φ hφ a R hR (hsR.trans hsF) j α).continuous
      (hcR.of_isClosed_subset (isClosed_tsupport _) hs) (hs.trans (hsR.trans hsF))
  have hIntegral : (∫ z, ∑ j, ∑ α,
      star (coefficients (r := r) E u a z (fun _ => j) α) * chartOneDual (r := r) E g.form h φ a R z j α ∂lebesgueC n) =
      ∑ j, ∑ α, ∫ z, star (coefficients (r := r) E u a z (fun _ => j) α) *
        chartOneDual (r := r) E g.form h φ a R z j α ∂lebesgueC n := by
    rw [integral_finsetSum Finset.univ (fun j _ => integrable_finsetSum Finset.univ (fun α _ => hi j α))]
    exact Finset.sum_congr rfl fun j _ => integral_finsetSum Finset.univ (fun α _ => hi j α)
  rw [weightedTwoPairing_twoFormPushforward_integral E g μ hμ h hh φ hφ hE f huf.2.1 a F hF hcF hsF hskew,
    weakDbar_chartTwo_adjoint_pairing E g h hh φ hφ u f huf a F hF hcF hsF hskew,
    locallyL2_weightedOneInner_oneFormPushforward E g μ hμ h hh φ hφ hE u huf.1 a R hR hcR (hsR.trans hsF),
    hIntegral]

theorem weightedOnePairing_finset_sum_right (u : NQForm E 1) {ι : Type*} (s : Finset ι)
    (v : ι → NQForm E 1) (x : M.Carrier) :
    weightedOnePairing E g.form h φ u (∑ i ∈ s, v i) x =
      ∑ i ∈ s, weightedOnePairing E g.form h φ u (v i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact weightedOnePairing_eq_zero_of_right_zero E g.form h φ u 0 x rfl
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi,Finset.sum_insert hi]
      simp only [weightedOnePairing,oneFormPairing_add_right,add_mul] at ih ⊢
      rw [ih]

theorem weightedOnePairing_sum_right (u : NQForm E 1) {ι : Type*} [Fintype ι]
    (v : ι → NQForm E 1) (x : M.Carrier) :
    weightedOnePairing E g.form h φ u (∑ i, v i) x =
      ∑ i, weightedOnePairing E g.form h φ u (v i) x :=
  weightedOnePairing_finset_sum_right E g h φ u Finset.univ v x

include hμ hh hφ hE in
theorem locallyL2_weightedOnePairing_compact_integrable
    (u V : NQForm E 1) (hu : LocallyL2 (r := r) E u) (hV : SmoothForm (r := r) E V)
    (hcV : IsCompact (closure {x | V x ≠ (0 : NQForm E 1) x})) :
    Integrable (weightedOnePairing E g.form h φ u V) μ := by
  classical
  obtain ⟨s,F,hF,hdecomp⟩ := exists_finite_compact_chart_decomposition E g V hV hcV
  have he : weightedOnePairing E g.form h φ u V = fun x =>
      ∑ i : s, weightedOnePairing E g.form h φ u (oneFormPushforward E (i : M.Carrier) (F i)) x := by
    funext x
    rw [hdecomp,weightedOnePairing_sum_right]
  rw [he]
  exact integrable_finsetSum _ fun i _ => locallyL2_weightedOnePairing_oneFormPushforward_integrable
    E g μ hμ h hh φ hφ hE u hu (i : M.Carrier) (F i) (hF i).1 (hF i).2.1 (hF i).2.2

include hE in
theorem rough_smooth_compact_twoForm_has_adjoint
    (W : NQForm E 2) (hW : SmoothForm (r := r) E W)
    (hcW : IsCompact (closure {x | W x ≠ (0 : NQForm E 2) x})) :
    ∃ R : WeightedOneSection E g μ hμ h hh φ hφ,
      SmoothForm (r := r) E R.1 ∧ IsCompact (closure {x | R.1 x ≠ (0 : NQForm E 1) x}) ∧
      ∀ (u : NQForm E 1) (f : NQForm E 2), WeakDbar (r := r) E u f →
        (∫ x, weightedTwoPairing E g.form h φ f W x ∂μ) = weightedOneInner E g.form μ h φ u R.1 := by
  classical
  obtain ⟨s,F,hF,hskew,hdecomp⟩ := exists_finite_compact_two_chart_decomposition E g W hW hcW
  let R := fun i : s => weightedTwoDbarAdjointChartSection E g μ hμ h hh φ hφ hE (i : M.Carrier)
    (F i) (hF i).1 (hF i).2.1 (hF i).2.2
  have hRs (i : s) : SmoothForm (r := r) E (R i).1 :=
    (weightedTwoDbarAdjointChartSection_smooth_compact E g μ hμ h hh φ hφ hE (i : M.Carrier)
      (F i) (hF i).1 (hF i).2.1 (hF i).2.2).1
  have hRc (i : s) : IsCompact (closure {x | (R i).1 x ≠ (0 : NQForm E 1) x}) :=
    (weightedTwoDbarAdjointChartSection_smooth_compact E g μ hμ h hh φ hφ hE (i : M.Carrier)
      (F i) (hF i).1 (hF i).2.1 (hF i).2.2).2
  refine ⟨∑ i,R i,?_,?_,?_⟩
  · rw [weightedOneSection_sum_val]
    exact smoothForm_sum E (fun i => (R i).1) hRs
  · rw [weightedOneSection_sum_val]
    exact compact_formSupport_sum E (fun i => (R i).1) hRc
  · intro u f huf
    have he : weightedTwoPairing E g.form h φ f W = fun x =>
        ∑ i : s, weightedTwoPairing E g.form h φ f (twoFormPushforward E (i : M.Carrier) (F i)) x := by
      funext x
      rw [hdecomp,weightedTwoPairing_sum_right]
    rw [he,integral_finsetSum Finset.univ (fun (i : s) _ =>
      weightedTwoPairing_twoFormPushforward_integrable E g μ hμ h hh φ hφ hE f huf.2.1
        (i : M.Carrier) (F i) (hF i).1 (hF i).2.1 (hF i).2.2 (hskew i))]
    have hinner : weightedOneInner E g.form μ h φ u (∑ i,R i).1 =
        ∑ i,weightedOneInner E g.form μ h φ u (R i).1 := by
      rw [weightedOneSection_sum_val]
      unfold weightedOneInner
      have he' : weightedOnePairing E g.form h φ u (∑ i,(R i).1) =
          fun x => ∑ i,weightedOnePairing E g.form h φ u (R i).1 x := by
        funext x
        exact weightedOnePairing_sum_right E g h φ u (fun i => (R i).1) x
      rw [he']
      exact integral_finsetSum _ fun i _ => locallyL2_weightedOnePairing_compact_integrable
        E g μ hμ h hh φ hφ hE u (R i).1 huf.1 (hRs i) (hRc i)
    rw [hinner]
    apply Finset.sum_congr rfl
    intro i _
    exact rough_weakDbar_weighted_chartTwo_adjoint_pairing E g μ hμ h hh φ hφ hE u f huf (i : M.Carrier)
      (F i) (hF i).1 (hF i).2.1 (hF i).2.2 (hskew i)

include hE in
theorem rough_smooth_compact_twoForm_has_co_closed_adjoint
    (W : NQForm E 2) (hW : SmoothForm (r := r) E W)
    (hcW : IsCompact (closure {x | W x ≠ (0 : NQForm E 2) x})) :
    ∃ R : WeightedOneSection E g μ hμ h hh φ hφ,
      SmoothForm (r := r) E R.1 ∧ IsCompact (closure {x | R.1 x ≠ (0 : NQForm E 1) x}) ∧
      (realizeWeightedOneSection E g μ hμ h hh φ hφ R,(0 : WeightedTopHilbert E g μ hμ h hh φ hφ)) ∈
        (weightedMaximalDbar E g μ hμ h hh φ hφ).adjoint.graph ∧
      (∀ (u : NQForm E 1) (f : NQForm E 2),WeakDbar (r := r) E u f →
        (∫ x,weightedTwoPairing E g.form h φ f W x ∂μ) = weightedOneInner E g.form μ h φ u R.1) ∧
      (∀ f : NQForm E 1,WeaklyClosed (r := r) E f → weightedOneInner E g.form μ h φ f R.1 = 0) := by
  obtain ⟨R,hRs,hRc,hgreen⟩ := rough_smooth_compact_twoForm_has_adjoint E g μ hμ h hh φ hφ hE W hW hcW
  refine ⟨R,hRs,hRc,twoAdjoint_green_co_closed E g μ hμ h hh φ hφ hE W R
    (fun U f huf => hgreen U.1 f huf),hgreen,?_⟩
  intro f hf
  have he := hgreen f 0 (weakDbar_zero_of_weaklyClosed E f hf)
  simpa only [weightedTwoPairing_eq_zero_left,integral_zero] using he.symm

end Yau.LeafProofs.L14Aux
