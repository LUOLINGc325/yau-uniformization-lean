import Yau.LeafProofs.L14PairFirstOrder
import Yau.LeafProofs.L14ModelLocalization

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder ENNReal
open MeasureTheory Bundle Filter Module
namespace Yau.LeafProofs.L14Aux
open BundleDbar

def oneRowModelTest {n r : ℕ} (row : Fin n × Fin r) (ψ : ComplexVector n → ℂ)
    (z : ComplexVector n) (i : Fin n) : ComplexVector r :=
  WithLp.toLp 2 (fun α => if (i,α) = row then ψ z else 0)

theorem oneRowModelTest_apply {n r : ℕ} (row : Fin n × Fin r) (ψ : ComplexVector n → ℂ)
    (z : ComplexVector n) (i : Fin n) (α : Fin r) :
    oneRowModelTest row ψ z i α = if (i,α) = row then ψ z else 0 := rfl

theorem oneRowModelTest_properties {n r : ℕ} (row : Fin n × Fin r) (ψ : ComplexVector n → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    ContDiff ℝ ∞ (oneRowModelTest row ψ) ∧ HasCompactSupport (oneRowModelTest row ψ) ∧
      tsupport (oneRowModelTest row ψ) ⊆ tsupport ψ := by
  have hs : tsupport (oneRowModelTest row ψ) ⊆ tsupport ψ := by
    apply closure_minimal _ (isClosed_tsupport _)
    intro z hz
    by_contra hn
    have hψz : ψ z = 0 := image_eq_zero_of_notMem_tsupport hn
    apply hz
    funext i
    apply PiLp.ext
    intro α
    simp only [oneRowModelTest_apply, hψz, ite_self, Pi.zero_apply, PiLp.zero_apply]
  refine ⟨?_,hcψ.of_isClosed_subset (isClosed_tsupport _) hs,hs⟩
  apply contDiff_pi.mpr
  intro i
  apply (contDiff_piLp 2).mpr
  intro α
  by_cases hi : (i,α) = row
  · simpa only [oneRowModelTest_apply,ite_eq_left hi] using hψ
  · simpa only [oneRowModelTest_apply,ite_eq_right hi] using (contDiff_const : ContDiff ℝ ∞ (fun _ : ComplexVector n => (0 : ℂ)))

theorem modelOneDbar_oneRowModelTest {n r : ℕ} (row : Fin n × Fin r) (ψ : ComplexVector n → ℂ)
    (z : ComplexVector n) (i j : Fin n) (α : Fin r) :
    modelOneDbar (oneRowModelTest row ψ) z i j α =
      (if (j,α) = row then wirtBar ψ z (stdVec i) else 0) -
      (if (i,α) = row then wirtBar ψ z (stdVec j) else 0) := by
  have hz0 (v : ComplexVector n) : wirtBar (fun _ : ComplexVector n => (0 : ℂ)) z v = 0 := by
    unfold wirtBar
    rw [(hasFDerivAt_const (𝕜 := ℝ) (0 : ℂ) z).fderiv]
    simp
  by_cases hj : (j,α) = row <;> by_cases hi : (i,α) = row <;>
    simp only [modelOneDbar,localCurlMatrix,oneRowModelTest_apply,hj,hi,ite_true,ite_false,hz0,zero_sub,sub_zero]

theorem barPrincipal_formal_test_row {n : ℕ} {α β : Type*}
    (C : β → α → Fin n → ComplexVector n → ℂ) (row : β) (c : α)
    (z : ComplexVector n) (hC : ∀ i,DifferentiableAt ℝ (C row c i) z)
    (ψ : ComplexVector n → ℝ) (hψ : DifferentiableAt ℝ ψ z) :
    complexFormalAdjointTestRow realVec
      (fun row c d w => C row c d.1 w * wirtBarRealCoefficient d.2)
      (fun _ _ _ => 0) row c ψ z =
      -∑ i,wirtBar (fun w => C row c i w * (ψ w : ℂ)) z (stdVec i) := by
  have hψC : DifferentiableAt ℝ (fun w => (ψ w : ℂ)) z :=
    Complex.ofRealCLM.differentiableAt.comp z hψ
  have hψd (v : ComplexVector n) : fderiv ℝ (fun w => (ψ w : ℂ)) z v = ((fderiv ℝ ψ z v : ℝ) : ℂ) := by
    have he := (Complex.ofRealCLM.hasFDerivAt.comp z hψ.hasFDerivAt).fderiv
    exact congrArg (fun L : ComplexVector n →L[ℝ] ℂ => L v) he
  have hd (d : RIdx n) (v : ComplexVector n) :
      fderiv ℝ (fun w => C row c d.1 w * wirtBarRealCoefficient d.2) z v =
        fderiv ℝ (C row c d.1) z v * wirtBarRealCoefficient d.2 := by
    have he := ((hC d.1).hasFDerivAt.mul_const' (wirtBarRealCoefficient d.2)).fderiv
    exact congrArg (fun L : ComplexVector n →L[ℝ] ℂ => L v) he
  have hp (i : Fin n) (v : ComplexVector n) :
      fderiv ℝ (fun w => C row c i w * (ψ w : ℂ)) z v =
        C row c i z * (fderiv ℝ ψ z v : ℂ) + fderiv ℝ (C row c i) z v * (ψ z : ℂ) := by
    rw [fderiv_fun_mul (hC i) hψC]
    simp only [add_apply,smul_apply,smul_eq_mul,hψd]
    ring
  unfold complexFormalAdjointTestRow
  simp only [zero_mul,add_zero]
  congr 1
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_two,wirtBar_eq_real_directions]
  dsimp only
  rw [hd (i,0),hd (i,1)]
  simp only [hp]
  ring

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)] [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem chartOneDual_oneRowModelTest (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (a : M.Carrier) (row : Fin n × Fin r) (ψ : ComplexVector n → ℂ)
    (z : ComplexVector n) (i : Fin n) (α : Fin r) :
    chartOneDual (r := r) E g h φ a (oneRowModelTest row ψ) z i α =
      (Real.exp (-φ (chartInv a z)) : ℂ) * chartOneMetricMatrix (r := r) E g h a z (i,α) row * ψ z := by
  classical
  rw [chartOneDual_eq_weighted_matrix]
  simp only [Matrix.mulVec,dotProduct,oneRowModelTest_apply]
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  ring

theorem chartTwoDual_modelOneDbar_oneRowModelTest (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (a : M.Carrier) (row : Fin n × Fin r) (ψ : ComplexVector n → ℂ)
    (z : ComplexVector n) (i j : Fin n) (α : Fin r) :
    chartTwoDual E g h φ a (modelOneDbar (oneRowModelTest row ψ)) z i j α =
      (Real.exp (-φ (chartInv a z)) : ℂ) * ∑ k,
        (chartTwoMetricMatrix (r := r) E g h a z ((α,i),j) ((row.2,k),row.1) * wirtBar ψ z (stdVec k) -
          chartTwoMetricMatrix (r := r) E g h a z ((α,i),j) ((row.2,row.1),k) * wirtBar ψ z (stdVec k)) := by
  classical
  rcases row with ⟨j0,α0⟩
  simp only [chartTwoDual,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,modelOneDbar_oneRowModelTest,
    mul_sub,Finset.sum_sub_distrib,mul_ite,mul_zero,Prod.mk.injEq]
  simp [ite_and,Finset.sum_ite_irrel]

theorem star_chartTwoMetricMatrix (g : HermitianField M) (h : Metric E)
    (a : M.Carrier) (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a)
    (p q : TwoCoefficientIndex n r) :
    star (chartTwoMetricMatrix (r := r) E g h a z p q) = chartTwoMetricMatrix (r := r) E g h a z q p := by
  have he := congrArg (fun A : Matrix (TwoCoefficientIndex n r) (TwoCoefficientIndex n r) ℂ => A q p)
    (chartTwoMetricMatrix_posDef E g h a z hz).isHermitian.eq
  exact he

def alternatingTwoDualDivergenceCoefficient (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (a : M.Carrier) (row : Fin n × Fin r)
    (p : TwoCoefficientIndex n r) (i : Fin n) (z : ComplexVector n) : ℂ :=
  (1/2 : ℂ) * (twoDualDivergenceCoefficient (r := r) E g h φ a row p i z -
    twoDualDivergenceCoefficient (r := r) E g h φ a row (twoCoefficientFlip n r p) i z)

theorem alternatingTwoDualDivergenceCoefficient_eq (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (a : M.Carrier) (row : Fin n × Fin r)
    (p : TwoCoefficientIndex n r) (i : Fin n) (z : ComplexVector n) :
    alternatingTwoDualDivergenceCoefficient (r := r) E g h φ a row p i z =
      (1/2 : ℂ) * (Real.exp (-φ (chartInv a z)) : ℂ) *
        (chartTwoMetricMatrix (r := r) E g h a z ((row.2,i),row.1) p -
          chartTwoMetricMatrix (r := r) E g h a z ((row.2,row.1),i) p) := by
  have hf : chartTwoMetricMatrix (r := r) E g h a z ((row.2,i),row.1) (twoCoefficientFlip n r p) =
      chartTwoMetricMatrix (r := r) E g h a z ((row.2,row.1),i) p :=
    chartTwoMetricMatrix_flip E g h a z ((row.2,row.1),i) p
  simp only [alternatingTwoDualDivergenceCoefficient,twoDualDivergenceCoefficient,hf]
  ring

theorem chartTwoDual_curl_oneRowModelTest_star (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (a : M.Carrier) (row : Fin n × Fin r) (ψ : ComplexVector n → ℂ)
    (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) (p : TwoCoefficientIndex n r) :
    (1/2 : ℂ) * star (chartTwoDual E g h φ a (modelOneDbar (oneRowModelTest row ψ)) z p.1.2 p.2 p.1.1) =
      ∑ i,alternatingTwoDualDivergenceCoefficient (r := r) E g h φ a row p i z *
        wirt (fun w => star (ψ w)) z (stdVec i) := by
  rw [chartTwoDual_modelOneDbar_oneRowModelTest]
  simp only [star_mul,star_sum,star_sub,Complex.star_def,Complex.conj_ofReal]
  simp only [← Complex.star_def,star_chartTwoMetricMatrix E g h a z hz,← wirt_star,
    alternatingTwoDualDivergenceCoefficient_eq]
  simp only [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem alternatingTwoDualDivergenceCoefficient_contDiffOn (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (row : Fin n × Fin r) (p : TwoCoefficientIndex n r) (i : Fin n) :
    ContDiffOn ℝ ∞ (alternatingTwoDualDivergenceCoefficient (r := r) E g.form h φ a row p i)
      (localDomain (r := r) E a) :=
  ((twoDualDivergenceCoefficient_contDiffOn E g h hh φ hφ a row p i).sub
    (twoDualDivergenceCoefficient_contDiffOn E g h hh φ hφ a row (twoCoefficientFlip n r p) i)).const_smul (1/2 : ℂ)

theorem alternatingTwoDual_formal_test_row (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (row : Fin n × Fin r) (p : TwoCoefficientIndex n r)
    (ψ : ComplexVector n → ℝ) (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a)
    (hψ : DifferentiableAt ℝ ψ z) :
    complexFormalAdjointTestRow realVec
      (wirtDivergenceDerivative (alternatingTwoDualDivergenceCoefficient (r := r) E g.form h φ a))
      (wirtDivergenceValue (alternatingTwoDualDivergenceCoefficient (r := r) E g.form h φ a)) row p ψ z =
      (1/2 : ℂ) * star (chartTwoDual E g.form h φ a
        (modelOneDbar (oneRowModelTest row (fun w => (ψ w : ℂ)))) z p.1.2 p.2 p.1.1) := by
  have hC (i : Fin n) : DifferentiableAt ℝ
      (alternatingTwoDualDivergenceCoefficient (r := r) E g.form h φ a row p i) z :=
    ((alternatingTwoDualDivergenceCoefficient_contDiffOn E g h hh φ hφ a row p i).contDiffAt
      ((localDomain_isOpen E a).mem_nhds hz)).differentiableAt (by simp)
  unfold complexFormalAdjointTestRow
  rw [wirtDivergence_formal_test_row _ row p z hC ψ hψ,
    chartTwoDual_curl_oneRowModelTest_star E g.form h φ a row _ z hz p]
  have he : (fun w => star ((ψ w : ℝ) : ℂ)) = fun w => ((ψ w : ℝ) : ℂ) := by
    funext w
    exact Complex.conj_ofReal (ψ w)
  rw [he]

theorem star_chartOneMetricMatrix (g : HermitianField M) (h : Metric E)
    (a : M.Carrier) (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a)
    (p q : Fin n × Fin r) :
    star (chartOneMetricMatrix (r := r) E g h a z p q) = chartOneMetricMatrix (r := r) E g h a z q p := by
  exact congrArg (fun A : Matrix (Fin n × Fin r) (Fin n × Fin r) ℂ => A q p)
    (chartOneMetricMatrix_posDef E g h a z hz).isHermitian.eq

theorem chartOneDual_oneRowModelTest_star (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (a : M.Carrier) (row : Fin n × Fin r) (ψ : ComplexVector n → ℂ)
    (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) (i : Fin n) (α : Fin r) :
    star (chartOneDual (r := r) E g h φ a (oneRowModelTest row ψ) z i α) =
      (Real.exp (-φ (chartInv a z)) : ℂ) * chartOneMetricMatrix (r := r) E g h a z row (i,α) * star (ψ z) := by
  rw [chartOneDual_oneRowModelTest]
  simp only [star_mul]
  rw [star_chartOneMetricMatrix E g h a z hz]
  have he : star ((Real.exp (-φ (chartInv a z)) : ℝ) : ℂ) = ((Real.exp (-φ (chartInv a z)) : ℝ) : ℂ) :=
    Complex.conj_ofReal _
  rw [he]
  ring

theorem topDualFirstOrder_formal_test_row (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (row : Fin n × Fin r) (β : Fin r)
    (ψ : ComplexVector n → ℝ) (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a)
    (hψ : DifferentiableAt ℝ ψ z) :
    complexFormalAdjointTestRow realVec (topDualFirstOrderDerivative (r := r) E g.form h φ a)
      (fun _ _ _ => 0) row β ψ z =
      star ((∑ γ,BundleDbar.metricMatrix (r := r) E h a z β γ *
        chartDbarAdjoint (r := r) E g.form h φ a (oneRowModelTest row (fun w => (ψ w : ℂ))) z γ) *
          (Real.exp (-φ (chartInv a z)) : ℂ)) := by
  let C := fun row (β : Fin r) (i : Fin n) (w : ComplexVector n) =>
    (Real.exp (-φ (chartInv a w)) : ℂ) * chartOneMetricMatrix (r := r) E g.form h a w row (i,β)
  have he : ContDiffOn ℝ ∞ (fun w => (Real.exp (-φ (chartInv a w)) : ℂ))
      (localDomain (r := r) E a) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      (Real.contDiff_exp.comp_contDiffOn (((hφ a).mono Set.inter_subset_left).neg))
  have hC (i : Fin n) : DifferentiableAt ℝ (C row β i) z :=
    ((he.mul (chartOneMetricMatrix_contDiffOn E g h hh a row (i,β))).contDiffAt
      ((localDomain_isOpen E a).mem_nhds hz)).differentiableAt (by simp)
  change complexFormalAdjointTestRow realVec
    (fun row β d w => C row β d.1 w * wirtBarRealCoefficient d.2) (fun _ _ _ => 0) row β ψ z = _
  rw [barPrincipal_formal_test_row C row β z hC ψ hψ,chartDbarAdjoint_dual E g.form h φ a _ z hz β]
  simp only [star_neg,star_sum,← wirtBar_star]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hf : (fun w => C row β i w * (ψ w : ℂ)) =ᶠ[𝓝 z]
      (fun w => star (chartOneDual (r := r) E g.form h φ a (oneRowModelTest row (fun w => (ψ w : ℂ))) w i β)) := by
    filter_upwards [(localDomain_isOpen (r := r) E a).mem_nhds hz] with w hw
    rw [chartOneDual_oneRowModelTest_star E g.form h φ a row _ w hw]
    have hs : star ((ψ w : ℝ) : ℂ) = ((ψ w : ℝ) : ℂ) := Complex.conj_ofReal _
    rw [hs]
  unfold wirtBar
  rw [hf.fderiv_eq]

end Yau.LeafProofs.L14Aux
