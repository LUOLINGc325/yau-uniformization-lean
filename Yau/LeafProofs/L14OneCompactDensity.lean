import Yau.LeafProofs.L14LocalSystem
import Yau.LeafProofs.L14PairTestAlgebra

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder ENNReal
open MeasureTheory Bundle Filter Module
namespace Yau.LeafProofs.L14Aux
open BundleDbar
variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem coefficients_ae_zero_of_chartOneDual_ae_zero
    (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (u : NQForm E 1) (a : M.Carrier)
    (hu : ∀ i α, (fun z => chartOneDual (r := r) E g h φ a
      (fun w j => coefficients (r := r) E u a w (fun _ => j)) z i α) =ᵐ[
        (lebesgueC n).restrict (localDomain (r := r) E a)] 0)
    (i : Fin n) (α : Fin r) :
    (fun z => coefficients (r := r) E u a z (fun _ => i) α) =ᵐ[
      (lebesgueC n).restrict (localDomain (r := r) E a)] 0 := by
  have hall := ae_all_iff.mpr (fun j => ae_all_iff.mpr (hu j))
  filter_upwards [hall, ae_restrict_mem (localDomain_isOpen E a).measurableSet] with z hz hzo
  let H := chartOneMetricMatrix (r := r) E g h a z
  let U := fun c : Fin n × Fin r => coefficients (r := r) E u a z (fun _ => c.1) c.2
  have hρ : (Real.exp (-φ (chartInv a z)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.exp_pos _))
  have hzero : H *ᵥ U = 0 := by
    funext c
    have he := hz c.1 c.2
    rw [chartOneDual_eq_weighted_matrix] at he
    exact (mul_eq_zero.mp he).resolve_left hρ
  have hH : H.PosDef := chartOneMetricMatrix_posDef (r := r) E g h a z hzo
  have he := congrArg (fun W : (Fin n × Fin r) → ℂ => H⁻¹ *ᵥ W) hzero
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hH.isUnit.map Matrix.detMonoidHom),
    Matrix.one_mulVec, Matrix.mulVec_zero] at he
  exact congrFun he (i, α)

variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
  (hE : Holomorphic (r := r) E)

/-- The actual compactly supported smooth chart one-forms are total in the
weighted one-form Hilbert space. -/
theorem weightedOneHilbert_eq_zero_of_chart_tests
    (B : WeightedOneHilbert E g μ hμ h hh φ hφ)
    (hB : ∀ (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r)
      (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
      (hs : tsupport F ⊆ localDomain (r := r) E a),
      inner ℂ B (realizeWeightedOneSection E g μ hμ h hh φ hφ
        (weightedOneChartSection E g μ hμ h hh φ hφ hE a F hF hc hs)) = 0) :
    B = 0 := by
  classical
  let V := weightedOneHilbertRepresentative E g μ hμ h hh φ hφ B
  have hVreal : realizeWeightedOneSection E g μ hμ h hh φ hφ V = B :=
    weightedOneHilbertRepresentative_realize E g μ hμ h hh φ hφ B
  have hdual (a : M.Carrier) (i : Fin n) (α : Fin r) :
      (fun z => chartOneDual (r := r) E g.form h φ a
        (fun w j => coefficients (r := r) E V.1 a w (fun _ => j)) z i α) =ᵐ[
          (lebesgueC n).restrict (localDomain (r := r) E a)] 0 := by
    let O := localDomain (r := r) E a
    let A := fun w j => coefficients (r := r) E V.1 a w (fun _ => j)
    let W := fun z => chartOneDual (r := r) E g.form h φ a A z i α
    have hW : LocallyIntegrableOn W O (lebesgueC n) :=
      chartOneDual_locallyIntegrableOn E g h hh φ hφ V.1 V.2.1 a i α
    have hstarW : LocallyIntegrableOn (fun z => star (W z)) O (lebesgueC n) :=
      Complex.conjCLE.toContinuousLinearMap.locallyIntegrableOn_comp hW
    have htest (ψ : ComplexVector n → ℝ) (hψ : ContDiff ℝ ∞ ψ)
        (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ O) :
        (∫ z, ψ z • star (W z) ∂lebesgueC n) = 0 := by
      let G := oneRowModelTest (i, α) (fun z => (ψ z : ℂ))
      have hψC : ContDiff ℝ ∞ (fun z => (ψ z : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp hψ
      obtain ⟨hG, hcG, hsGψ⟩ := oneRowModelTest_properties (i, α)
        (fun z => (ψ z : ℂ)) hψC (hcψ.comp_left Complex.ofReal_zero)
      have hsG : tsupport G ⊆ O := hsGψ.trans
        ((tsupport_comp_subset (g := fun t : ℝ => (t : ℂ)) Complex.ofReal_zero ψ).trans hsψ)
      let U := weightedOneChartSection E g μ hμ h hh φ hφ hE a G hG hcG hsG
      have hi : inner ℂ (realizeWeightedOneSection E g μ hμ h hh φ hφ V)
          (realizeWeightedOneSection E g μ hμ h hh φ hφ U) = 0 := by
        rw [hVreal]
        exact hB a G hG hcG hsG
      have hphys : weightedOneInner E g.form μ h φ V.1
          (oneFormPushforward (r := r) E a G) = 0 :=
        (realizeWeightedOneSection_inner E g μ hμ h hh φ hφ V U).symm.trans hi
      have hformula := weightedOneInner_oneFormPushforward_right E g μ hμ h hh φ hφ hE
        a G hG hcG hsG V
      have hprod : (2 : ℝ)^n • (∫ z, ψ z • star (W z) ∂lebesgueC n) = 0 := by
        rw [← hphys, hformula]
        congr 1
        apply integral_congr_ae
        apply Eventually.of_forall
        intro z
        change ψ z • star (W z) =
          ∑ j, ∑ β, star (A z j β) * chartOneDual (r := r) E g.form h φ a G z j β
        by_cases hzo : z ∈ O
        · rw [chartOneDual_conj_symm E g.form h φ a z hzo A G]
          rw [← Fintype.sum_prod_type (f := fun c : Fin n × Fin r =>
            star (chartOneDual (r := r) E g.form h φ a A z c.1 c.2) * G z c.1 c.2)]
          simp only [G, oneRowModelTest_apply, mul_ite, mul_zero,
            Finset.sum_ite_eq', Finset.mem_univ, ite_true]
          simp only [W, Complex.real_smul, mul_comm]
        · have hψz : ψ z = 0 := image_eq_zero_of_notMem_tsupport
            (fun ht => hzo (hsψ ht))
          simp only [chartOneDual, G, oneRowModelTest_apply, hψz,
            Complex.ofReal_zero, ite_self, mul_zero, Finset.sum_const_zero, zero_smul]
      exact (smul_eq_zero.mp hprod).resolve_left
        (ne_of_gt (pow_pos (by norm_num : (0 : ℝ) < 2) n))
    have hzero : ∀ᵐ z ∂lebesgueC n, z ∈ O → star (W z) = 0 :=
      (localDomain_isOpen E a).ae_eq_zero_of_integral_contDiff_smul_eq_zero hstarW htest
    apply (ae_restrict_iff' (localDomain_isOpen E a).measurableSet).mpr
    filter_upwards [hzero] with z hz
    intro hzo
    exact star_eq_zero.mp (hz hzo)
  have hcoeff (a : M.Carrier) (i : Fin n) (α : Fin r) :
      (fun z => coefficients (r := r) E V.1 a z (fun _ => i) α) =ᵐ[
        (lebesgueC n).restrict (localDomain (r := r) E a)] 0 :=
    coefficients_ae_zero_of_chartOneDual_ae_zero E g.form h φ V.1 a (hdual a) i α
  have hVae : ∀ᵐ x ∂μ, V.1 x = (0 : NQForm E 1) x :=
    oneForm_ae_zero_of_coefficients_ae_zero E g.form μ hμ V.1 hcoeff
  have hn : ‖V‖ = 0 := (weightedOneSection_norm_eq_zero_iff E g μ hμ h hh φ hφ V).mpr hVae
  have hBnorm : ‖B‖ = 0 := by
    rw [← hVreal]
    change ‖(V : UniformSpace.Completion (WeightedOneSection E g μ hμ h hh φ hφ))‖ = 0
    rw [UniformSpace.Completion.norm_coe, hn]
  exact norm_eq_zero.mp hBnorm

/-- Totality also holds with the compact chart tests in the first slot. -/
theorem weightedOneHilbert_eq_zero_of_chart_tests_left
    (B : WeightedOneHilbert E g μ hμ h hh φ hφ)
    (hB : ∀ (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r)
      (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
      (hs : tsupport F ⊆ localDomain (r := r) E a),
      inner ℂ (realizeWeightedOneSection E g μ hμ h hh φ hφ
        (weightedOneChartSection E g μ hμ h hh φ hφ hE a F hF hc hs)) B = 0) :
    B = 0 := by
  apply weightedOneHilbert_eq_zero_of_chart_tests E g μ hμ h hh φ hφ hE B
  intro a F hF hc hs
  rw [← inner_conj_symm B _, hB a F hF hc hs, map_zero]

/-- Span of the realized genuine smooth compactly supported chart one-forms. -/
def weightedOneChartTestSpan : Submodule ℂ (WeightedOneHilbert E g μ hμ h hh φ hφ) :=
  Submodule.span ℂ {v | ∃ (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ localDomain (r := r) E a),
    realizeWeightedOneSection E g μ hμ h hh φ hφ
      (weightedOneChartSection E g μ hμ h hh φ hφ hE a F hF hc hs) = v}

theorem weightedOneChartTestSpan_orthogonal_eq_bot :
    (weightedOneChartTestSpan E g μ hμ h hh φ hφ hE)ᗮ = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro B hB
  apply weightedOneHilbert_eq_zero_of_chart_tests E g μ hμ h hh φ hφ hE B
  intro a F hF hc hs
  apply ((weightedOneChartTestSpan E g μ hμ h hh φ hφ hE).mem_orthogonal' B).mp hB
  apply Submodule.subset_span
  exact ⟨a, F, hF, hc, hs, rfl⟩

theorem weightedOneChartTestSpan_dense :
    Dense (weightedOneChartTestSpan E g μ hμ h hh φ hφ hE :
      Set (WeightedOneHilbert E g μ hμ h hh φ hφ)) := by
  let D := weightedOneChartTestSpan E g μ hμ h hh φ hφ hE
  have hz : Dᗮ = ⊥ := weightedOneChartTestSpan_orthogonal_eq_bot E g μ hμ h hh φ hφ hE
  have hclosure : D.topologicalClosure = ⊤ := by
    rw [← D.orthogonal_orthogonal_eq_closure, hz, Submodule.bot_orthogonal_eq_top]
  apply dense_iff_closure_eq.mpr
  change (D.topologicalClosure : Set (WeightedOneHilbert E g μ hμ h hh φ hφ)) = Set.univ
  rw [hclosure]
  rfl

end Yau.LeafProofs.L14Aux
