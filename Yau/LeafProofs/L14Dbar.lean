import Yau.LeafProofs.L14Two
import Yau.LeafProofs.L14Calculus

noncomputable section
open scoped Manifold Topology ContDiff ComplexOrder ENNReal Matrix
open MeasureTheory Bundle Filter

namespace Yau.LeafProofs.L14Aux
open BundleDbar

def modelOnePullback {n r : ℕ}
    (P : ComplexVector n → ComplexVector r →L[ℂ] ComplexVector r)
    (T : ComplexVector n → ComplexVector n)
    (F : ComplexVector n → Fin n → ComplexVector r)
    (z : ComplexVector n) (j : Fin n) : ComplexVector r :=
  P z (∑ i, star (fderiv ℂ T z (stdVec j) i) • F (T z) i)

theorem modelOnePullback_component {n r : ℕ}
    (P : ComplexVector n → ComplexVector r →L[ℂ] ComplexVector r)
    (T : ComplexVector n → ComplexVector n)
    (F : ComplexVector n → Fin n → ComplexVector r)
    (z : ComplexVector n) (j : Fin n) (α : Fin r) :
    modelOnePullback P T F z j α =
      ∑ i, star (fderiv ℂ T z (stdVec j) i) * P z (F (T z) i) α := by
  unfold modelOnePullback
  let Lα : ComplexVector r →ₗ[ℂ] ℂ := (EuclideanSpace.projₗ α).comp (P z).toLinearMap
  change Lα (∑ i, star (fderiv ℂ T z (stdVec j) i) • F (T z) i) =
    ∑ i, star (fderiv ℂ T z (stdVec j) i) * Lα (F (T z) i)
  simp only [map_sum, map_smul, smul_eq_mul]

theorem wirtBar_modelOnePullback {n r : ℕ}
    (P : ComplexVector n → ComplexVector r →L[ℂ] ComplexVector r)
    (T : ComplexVector n → ComplexVector n)
    (F : ComplexVector n → Fin n → ComplexVector r) (z : ComplexVector n)
    (hP : ContDiffAt ℂ ∞ P z) (hT : ContDiffAt ℂ ∞ T z)
    (hF : ContDiffAt ℝ ∞ F (T z)) (j k : Fin n) (α : Fin r) :
    wirtBar (fun y => modelOnePullback P T F y k α) z (stdVec j) =
      ∑ l, (wirtBar (fun y => star (fderiv ℂ T y (stdVec k) l)) z (stdVec j) * P z (F (T z) l) α +
        star (fderiv ℂ T z (stdVec k) l) * ∑ i,
          star (fderiv ℂ T z (stdVec j) i) * P z (modelTopDbar (fun y => F y l) (T z) i) α) := by
  have hD : ContDiffAt ℂ ∞ (fderiv ℂ T) z := hT.fderiv_right (m := ∞) (by simp)
  have hJ (l : Fin n) : DifferentiableAt ℝ
      (fun y => star (fderiv ℂ T y (stdVec k) l)) z := by
    have hd : ContDiffAt ℝ ∞ (fun y => fderiv ℂ T y (stdVec k) l) z :=
      ((contDiffAt_piLp 2).mp (hD.clm_apply contDiffAt_const) l).restrict_scalars ℝ
    exact (Complex.conjCLE.contDiff.contDiffAt.comp z hd).differentiableAt (by simp)
  have hPR : ContDiffAt ℝ ∞ (fun y => (P y).restrictScalars ℝ) z :=
    (ContinuousLinearMap.restrictScalarsL ℂ (ComplexVector r) (ComplexVector r) ℝ ℝ).contDiff.contDiffAt.comp z
      (hP.restrict_scalars ℝ)
  have hQ (l : Fin n) : DifferentiableAt ℝ (fun y => P y (F (T y) l) α) z :=
    ((contDiffAt_piLp 2).mp
      (hPR.clm_apply ((contDiffAt_pi.mp hF l).comp z (hT.restrict_scalars ℝ))) α).differentiableAt (by simp)
  simp_rw [modelOnePullback_component]
  rw [wirtBar_sum_fun Finset.univ
    (fun l y => star (fderiv ℂ T y (stdVec k) l) * P y (F (T y) l) α)
      z (stdVec j) (fun l _ => (hJ l).mul (hQ l))]
  apply Finset.sum_congr rfl
  intro l _
  rw [wirtBar_mul_rule _ _ z (stdVec j) (hJ l) (hQ l),
    wirtBar_holomorphic_matrix_apply_comp P T (fun y => F y l) z (stdVec j) α hP hT
      (contDiffAt_pi.mp hF l)]
  rfl

theorem modelOnePullback_curl {n r : ℕ}
    (P : ComplexVector n → ComplexVector r →L[ℂ] ComplexVector r)
    (T : ComplexVector n → ComplexVector n)
    (F : ComplexVector n → Fin n → ComplexVector r) (z : ComplexVector n)
    (hP : ContDiffAt ℂ ∞ P z) (hT : ContDiffAt ℂ ∞ T z)
    (hF : ContDiffAt ℝ ∞ F (T z)) (j k : Fin n) (α : Fin r) :
    localCurlMatrix (modelOnePullback P T F) z α j k =
      P z (∑ i, ∑ l, (star (fderiv ℂ T z (stdVec j) i) *
        star (fderiv ℂ T z (stdVec k) l)) • modelOneDbar F (T z) i l) α := by
  let J := fun p i => star (fderiv ℂ T z (stdVec p) i)
  let D := fun i l => modelTopDbar (fun y => F y l) (T z) i
  let Q := fun i l => P z (D i l) α
  have hJac (l : Fin n) :
      wirtBar (fun y => star (fderiv ℂ T y (stdVec k) l)) z (stdVec j) =
        wirtBar (fun y => star (fderiv ℂ T y (stdVec j) l)) z (stdVec k) :=
    conjugate_jacobian_wirtBar_symm T z (hT.of_le (by simp)) l k j
  have hDF (i l : Fin n) : modelOneDbar F (T z) i l = D i l - D l i := by
    ext β
    rfl
  have hsum : localCurlMatrix (modelOnePullback P T F) z α j k =
      (∑ l, ∑ i, J k l * J j i * Q i l) - ∑ i, ∑ l, J j i * J k l * Q l i := by
    change wirtBar (fun y => modelOnePullback P T F y k α) z (stdVec j) -
      wirtBar (fun y => modelOnePullback P T F y j α) z (stdVec k) = _
    rw [wirtBar_modelOnePullback P T F z hP hT hF j k α,
      wirtBar_modelOnePullback P T F z hP hT hF k j α]
    simp_rw [hJac, Finset.sum_add_distrib, Finset.mul_sum]
    simp only [J, D, Q, mul_assoc]
    ring
  calc
    _ = (∑ l, ∑ i, J k l * J j i * Q i l) - ∑ i, ∑ l, J j i * J k l * Q l i := hsum
    _ = ∑ i, ∑ l, (J j i * J k l) * (Q i l - Q l i) := by
      conv_lhs => arg 1; rw [Finset.sum_comm]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = _ := by
      let Lα : ComplexVector r →ₗ[ℂ] ℂ := (EuclideanSpace.projₗ α).comp (P z).toLinearMap
      change _ = Lα (∑ i, ∑ l, (J j i * J k l) • modelOneDbar F (T z) i l)
      simp only [map_sum, map_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro l _
      rw [hDF, map_sub]
      rfl

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

def SmoothDbarRepresents {q : ℕ} (u : NQForm E q) (f : NQForm E (q + 1)) : Prop :=
  ∀ a z, z ∈ localDomain (r := r) E a → ∀ I α,
    coefficients (r := r) E f a z I α = dbarCoefficients (r := r) E u a z I α

theorem dbarCoefficients_one_eq_curl (u : NQForm E 1) (a : M.Carrier)
    (z : ComplexVector n) (i j : Fin n) (α : Fin r) :
    dbarCoefficients (r := r) E u a z ![i,j] α =
      localCurlMatrix (fun w p => coefficients (r := r) E u a w (fun _ => p)) z α i j := by
  have hdel0 : (fun t : Fin 1 => (![i,j] : Fin 2 → Fin n) ((0 : Fin 2).succAbove t)) = (fun _ => j) := by
    ext t
    have ht : t = 0 := Subsingleton.elim _ _
    subst t
    rfl
  have hdel1 : (fun t : Fin 1 => (![i,j] : Fin 2 → Fin n) ((1 : Fin 2).succAbove t)) = (fun _ => i) := by
    ext t
    have ht : t = 0 := Subsingleton.elim _ _
    subst t
    rfl
  change (∑ k : Fin 2, (-1 : ℂ) ^ k.val *
    wirtBar (fun w => coefficients (r := r) E u a w
      (fun l => (![i,j] : Fin 2 → Fin n) (k.succAbove l)) α)
      z (stdVec ((![i,j] : Fin 2 → Fin n) k))) = _
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero,
    pow_one, one_mul, hdel0, hdel1, Matrix.cons_val_zero, Matrix.cons_val_one]
  change _ = wirtBar _ _ _ - wirtBar _ _ _
  ring

set_option backward.isDefEq.respectTransparency false in
theorem oneFormPushforward_representsDbar (hE : Holomorphic (r := r) E)
    (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ localDomain (r := r) E a) :
    SmoothDbarRepresents (r := r) E (oneFormPushforward (r := r) E a F)
      (twoFormPushforward (r := r) E a (modelOneDbar F)) := by
  classical
  intro b z hz I α
  let i := I 0
  let j := I 1
  have hI : I = ![i,j] := by ext t; fin_cases t <;> rfl
  rw [hI, dbarCoefficients_one_eq_curl]
  let y := chartInv b z
  let u := oneFormPushforward (r := r) E a F
  let f := twoFormPushforward (r := r) E a (modelOneDbar F)
  have hi : ContinuousAt (chartInv b) z := continuousAt_extChartAt_symm'' (I := ComplexModel n) hz.1
  by_cases hya : y ∈ bundleChartSource (r := r) E a
  · let T := fun t => chartPt a (chartInv b t)
    let P := topBundleTransition (r := r) E a b
    have hP : ContDiffAt ℂ ∞ P z := topBundleTransition_contDiffAt E hE a b z hz hya
    have hT : ContDiffAt ℂ ∞ T z := L18Aux.chartTransition_contDiffAt b a hz.1 hya.1
    have heq (p : Fin n) : (fun t => coefficients (r := r) E u b t (fun _ => p) α) =ᶠ[𝓝 z]
        (fun t => modelOnePullback P T F t p α) := by
      filter_upwards [(localDomain_isOpen E b).mem_nhds hz,
        hi.tendsto.eventually ((bundleChartSource_isOpen (r := r) E a).mem_nhds hya)] with t htb hta
      exact congrArg (fun v : ComplexVector r => v α)
        (oneFormPushforward_coefficients_inChart E a b F t htb hta p)
    have hcurl : localCurlMatrix (fun w p => coefficients (r := r) E u b w (fun _ => p)) z α i j =
        localCurlMatrix (modelOnePullback P T F) z α i j := by
      unfold localCurlMatrix wirtBar
      rw [(heq j).fderiv_eq, (heq i).fderiv_eq]
    have hfchart := congrArg (fun v : ComplexVector r => v α)
      (twoFormPushforward_coefficients_inChart E a b (modelOneDbar F) (modelOneDbar_skew F) z hz hya i j)
    exact hfchart.trans ((modelOnePullback_curl P T F z hP hT hF.contDiffAt i j α).symm.trans hcurl.symm)
  · have hfzero : (f y : antiComplexSubmodule E y 2) = (0 : antiComplexSubmodule E y 2) := by
      change (if hx : y ∈ bundleChartSource (r := r) E a then
        twoTensorFromCoefficients (r := r) E a y hx (modelOneDbar F (chartPt a y)) else 0) = 0
      exact dif_neg hya
    have hfc : coefficients (r := r) E f b z ![i,j] α = 0 := by
      have he : coefficients (r := r) E f b z ![i,j] α =
          coefficients (r := r) E (0 : NQForm E 2) b z ![i,j] α := by
        unfold coefficients
        rw [hfzero]
        rfl
      exact he.trans (coefficients_zero E b z ![i,j] α)
    let K := closure {x | u x ≠ (0 : NQForm E 1) x}
    have hsource : K ⊆ bundleChartSource (r := r) E a := oneFormPushforward_support E a F hc hs |>.trans (by
      rintro x ⟨w, hw, rfl⟩
      exact ⟨(extChartAt (ComplexModel n) a).map_target (hs hw).1, (hs hw).2⟩)
    have hout : y ∉ K := fun h => hya (hsource h)
    have hzero : ∀ᶠ x in 𝓝 y, u x = (0 : NQForm E 1) x := by
      filter_upwards [isClosed_closure.compl_mem_nhds hout] with x hx
      by_contra hn
      exact hx (subset_closure hn)
    have heq (p : Fin n) : (fun t => coefficients (r := r) E u b t (fun _ => p) α) =ᶠ[𝓝 z]
        (fun _ => 0) := by
      filter_upwards [hi.tendsto.eventually hzero] with t ht
      have he : coefficients (r := r) E u b t (fun _ => p) α =
          coefficients (r := r) E (0 : NQForm E 1) b t (fun _ => p) α := by
        unfold coefficients
        rw [ht]
      exact he.trans (coefficients_zero E b t (fun _ => p) α)
    have hcurl : localCurlMatrix (fun w p => coefficients (r := r) E u b w (fun _ => p)) z α i j = 0 := by
      unfold localCurlMatrix wirtBar
      rw [(heq j).fderiv_eq, (heq i).fderiv_eq]
      simp
    exact hfc.trans hcurl.symm

theorem weakDbar_of_smooth_isDbarOf_degree {q : ℕ}
    (u : NQForm E q) (f : NQForm E (q + 1))
    (hu : SmoothForm (r := r) E u) (hf : SmoothForm (r := r) E f)
    (hD : SmoothDbarRepresents (r := r) E u f) : WeakDbar (r := r) E u f := by
  refine ⟨smoothForm_locallyL2 E u hu, smoothForm_locallyL2 E f hf, ?_⟩
  intro a I α ψ hψ hc hs
  let U := fun k : Fin (q + 1) => fun z =>
    coefficients (r := r) E u a z (fun l => I (k.succAbove l)) α
  have hInt (k : Fin (q + 1)) :
      Integrable (fun z => wirtBar (U k) z (stdVec (I k)) * ψ z) (lebesgueC n) := by
    have hd := wirtBar_contDiffOn (localDomain_isOpen E a) _
      (hu a (fun l => I (k.succAbove l)) α) (stdVec (I k))
    simpa only [mul_comm] using integrable_compactTest_mul_complex (localDomain_isOpen E a)
      hψ.continuous hc hs hd.continuousOn
  calc
    _ = ∫ z, (∑ k : Fin (q + 1), (-1 : ℂ) ^ k.val *
        wirtBar (U k) z (stdVec (I k))) * ψ z ∂lebesgueC n := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro z
      by_cases hz : z ∈ localDomain (r := r) E a
      · exact congrArg (fun c : ℂ => c * ψ z) (hD a z hz I α)
      · have hzψ : ψ z = 0 := by
          by_contra hn
          exact hz (hs (subset_tsupport ψ hn))
        simp only [hzψ, mul_zero]
    _ = ∑ k : Fin (q + 1), (-1 : ℂ) ^ k.val *
        ∫ z, wirtBar (U k) z (stdVec (I k)) * ψ z ∂lebesgueC n := by
      simp only [Finset.sum_mul, mul_assoc]
      rw [integral_finset_sum _ (fun k _ => (hInt k).const_mul _)]
      exact Finset.sum_congr rfl (fun k _ => integral_const_mul _ _)
    _ = _ := by
      have hparts (k : Fin (q + 1)) := integral_compactTest_wirtBar_on (localDomain_isOpen E a)
        hψ hc hs (hu a (fun l => I (k.succAbove l)) α) (stdVec (I k))
      dsimp only [U]
      simp only [hparts, mul_neg, Finset.sum_neg_distrib]

theorem oneFormPushforward_maximalDbarGraph
    (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (φ : M.Carrier → ℝ) (hφ : SmoothFn φ) (hE : Holomorphic (r := r) E)
    (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ localDomain (r := r) E a) :
    MaximalDbarGraph (r := r) E g.form h μ φ
      (oneFormPushforward (r := r) E a F)
      (twoFormPushforward (r := r) E a (modelOneDbar F)) := by
  refine ⟨oneFormPushforward_weightedL2 E g μ hμ h hh φ hφ hE a F hF hc hs,
    twoFormPushforward_weightedL2 E g μ hμ h hh φ hφ hE a (modelOneDbar F)
      (modelOneDbar_skew F) (modelOneDbar_contDiff F hF)
      (hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_modelOneDbar_subset F))
      ((tsupport_modelOneDbar_subset F).trans hs), ?_⟩
  exact weakDbar_of_smooth_isDbarOf_degree E _ _
    (oneFormPushforward_smooth E hE a F hF hc hs)
    (twoFormPushforward_modelOneDbar_smooth E hE a F hF hc hs)
    (oneFormPushforward_representsDbar E hE a F hF hc hs)

end Yau.LeafProofs.L14Aux
