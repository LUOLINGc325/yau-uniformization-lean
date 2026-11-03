import Yau.LeafProofs.L14PairTestAlgebra

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder ENNReal
open MeasureTheory Bundle Filter Module
namespace Yau.LeafProofs.L14Aux
open BundleDbar

theorem twoCoefficient_alternating_sum {n r : ℕ} (C V : TwoCoefficientIndex n r → ℂ) :
    (∑ p,(1/2 : ℂ)*(C p-C (twoCoefficientFlip n r p))*V p) =
      ∑ p,C p*((1/2 : ℂ)*(V p-V (twoCoefficientFlip n r p))) := by
  classical
  have hs : (∑ p,C (twoCoefficientFlip n r p)*V p) = ∑ p,C p*V (twoCoefficientFlip n r p) := by
    apply Fintype.sum_equiv (twoCoefficientFlip n r)
    intro p
    rcases p with ⟨⟨α,i⟩,j⟩
    rfl
  calc
    _ = (1/2 : ℂ)*((∑ p,C p*V p)-(∑ p,C (twoCoefficientFlip n r p)*V p)) := by
      rw [mul_sub,Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = (1/2 : ℂ)*((∑ p,C p*V p)-(∑ p,C p*V (twoCoefficientFlip n r p))) := by rw [hs]
    _ = _ := by
      rw [mul_sub,Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro p _
      ring

def alternatingTwoModel {n r : ℕ} (F : ComplexVector n → Fin n → Fin n → ComplexVector r)
    (z : ComplexVector n) (i j : Fin n) : ComplexVector r := (1/2 : ℂ) • (F z i j-F z j i)

theorem alternatingTwoModel_apply {n r : ℕ} (F : ComplexVector n → Fin n → Fin n → ComplexVector r)
    (z : ComplexVector n) (i j : Fin n) (α : Fin r) :
    alternatingTwoModel F z i j α = (1/2 : ℂ)*(F z i j α-F z j i α) := rfl

theorem alternatingTwoModel_skew {n r : ℕ} (F : ComplexVector n → Fin n → Fin n → ComplexVector r)
    (z : ComplexVector n) (i j : Fin n) : alternatingTwoModel F z j i = -alternatingTwoModel F z i j := by
  ext α
  simp only [alternatingTwoModel_apply,PiLp.neg_apply]
  ring

theorem alternatingTwoModel_properties {n r : ℕ} (F : ComplexVector n → Fin n → Fin n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F) :
    ContDiff ℝ ∞ (alternatingTwoModel F) ∧ HasCompactSupport (alternatingTwoModel F) ∧
      tsupport (alternatingTwoModel F) ⊆ tsupport F := by
  have hs : tsupport (alternatingTwoModel F) ⊆ tsupport F := by
    apply closure_minimal _ (isClosed_tsupport _)
    intro z hz
    by_contra hn
    have hzF : F z = 0 := image_eq_zero_of_notMem_tsupport hn
    apply hz
    funext i j
    simp only [alternatingTwoModel,hzF,Pi.zero_apply,sub_self,smul_zero]
  refine ⟨?_,hcF.of_isClosed_subset (isClosed_tsupport _) hs,hs⟩
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact (((contDiff_pi.mp ((contDiff_pi.mp hF) i)) j).sub
    ((contDiff_pi.mp ((contDiff_pi.mp hF) j)) i)).const_smul (1/2 : ℂ)

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)] [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

def alternatingPairFirstOrderDerivative (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (a : M.Carrier) (row : Fin n × Fin r)
    (c : PairSystemInputIndex n r) (d : RIdx n) (z : ComplexVector n) : ℂ :=
  match c with
  | .inl β => topDualFirstOrderDerivative (r := r) E g h φ a row β d z
  | .inr p => wirtDivergenceDerivative (alternatingTwoDualDivergenceCoefficient (r := r) E g h φ a) row p d z

def alternatingPairFirstOrderValue (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (a : M.Carrier) (row : Fin n × Fin r)
    (c : PairSystemInputIndex n r) (z : ComplexVector n) : ℂ :=
  match c with
  | .inl _ => 0
  | .inr p => wirtDivergenceValue (alternatingTwoDualDivergenceCoefficient (r := r) E g h φ a) row p z

theorem alternatingPairFirstOrderDerivative_contDiffOn (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (row : Fin n × Fin r) (c : PairSystemInputIndex n r) (d : RIdx n) :
    ContDiffOn ℝ ∞ (alternatingPairFirstOrderDerivative (r := r) E g.form h φ a row c d)
      (localDomain (r := r) E a) := by
  cases c with
  | inl β => exact topDualFirstOrderDerivative_contDiffOn E g h hh φ hφ a row β d
  | inr p =>
    exact contDiffOn_const.mul
      (alternatingTwoDualDivergenceCoefficient_contDiffOn E g h hh φ hφ a row p d.1)

theorem alternatingPairFirstOrderValue_contDiffOn (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (row : Fin n × Fin r) (c : PairSystemInputIndex n r) :
    ContDiffOn ℝ ∞ (alternatingPairFirstOrderValue (r := r) E g.form h φ a row c)
      (localDomain (r := r) E a) := by
  cases c with
  | inl β => exact contDiffOn_const
  | inr p =>
    apply ContDiffOn.neg
    apply ContDiffOn.sum
    intro i _
    exact wirt_contDiffOn (localDomain_isOpen E a) _
      (alternatingTwoDualDivergenceCoefficient_contDiffOn E g h hh φ hφ a row p i) (stdVec i)

theorem alternatingTwoDual_contraction_eq (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (a : M.Carrier) (row : Fin n × Fin r)
    (F : ComplexVector n → Fin n → Fin n → ComplexVector r) (z : ComplexVector n) (i : Fin n) :
    (∑ p,alternatingTwoDualDivergenceCoefficient (r := r) E g h φ a row p i z * F z p.1.2 p.2 p.1.1) =
      chartTwoDual E g h φ a (alternatingTwoModel F) z i row.1 row.2 := by
  rw [show (∑ p,alternatingTwoDualDivergenceCoefficient (r := r) E g h φ a row p i z * F z p.1.2 p.2 p.1.1) =
    ∑ p,twoDualDivergenceCoefficient (r := r) E g h φ a row p i z *
      ((1/2 : ℂ)*(F z p.1.2 p.2 p.1.1-F z p.2 p.1.2 p.1.1)) from
      twoCoefficient_alternating_sum _ _]
  simp only [twoDualDivergenceCoefficient,chartTwoDual,alternatingTwoModel_apply,Matrix.mulVec,dotProduct,
    Finset.mul_sum,mul_assoc]

theorem alternatingPairFirstOrder_apply (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (A : ComplexVector n → ComplexVector r)
    (F : ComplexVector n → Fin n → Fin n → ComplexVector r) (hF : ContDiff ℝ ∞ F)
    (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) (row : Fin n × Fin r) :
    complexFirstOrderSystemApply realVec (alternatingPairFirstOrderDerivative (r := r) E g.form h φ a)
      (alternatingPairFirstOrderValue (r := r) E g.form h φ a) (pairSystemInput A F) z row =
      chartOneDual (r := r) E g.form h φ a (modelTopDbar A) z row.1 row.2 +
        chartOneDual (r := r) E g.form h φ a (chartTwoDbarAdjoint E g.form h φ a (alternatingTwoModel F)) z row.1 row.2 := by
  classical
  change (∑ c : PairSystemInputIndex n r,_) = _
  rw [Fintype.sum_sum_type]
  apply congrArg₂ (· + ·) (topDualFirstOrder_apply E g.form h φ a A z row)
  change complexFirstOrderSystemApply realVec
    (wirtDivergenceDerivative (alternatingTwoDualDivergenceCoefficient (r := r) E g.form h φ a))
    (wirtDivergenceValue (alternatingTwoDualDivergenceCoefficient (r := r) E g.form h φ a))
    (fun w p => F w p.1.2 p.2 p.1.1) z row = _
  have hC (p : TwoCoefficientIndex n r) (i : Fin n) : DifferentiableAt ℝ
      (alternatingTwoDualDivergenceCoefficient (r := r) E g.form h φ a row p i) z :=
    ((alternatingTwoDualDivergenceCoefficient_contDiffOn E g h hh φ hφ a row p i).contDiffAt
      ((localDomain_isOpen E a).mem_nhds hz)).differentiableAt (by simp)
  have hFc (p : TwoCoefficientIndex n r) : DifferentiableAt ℝ (fun w => F w p.1.2 p.2 p.1.1) z :=
    ((contDiff_piLp 2).mp ((contDiff_pi.mp ((contDiff_pi.mp hF) p.1.2)) p.2) p.1.1).differentiable (by simp) z
  rw [wirtDivergence_system_apply _ _ z row hC hFc,
    chartTwoDbarAdjoint_dual E g.form h φ a (alternatingTwoModel F) z hz row.1 row.2]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  funext w
  exact alternatingTwoDual_contraction_eq E g.form h φ a row F w i

theorem alternatingPair_formal_test_row (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (row : Fin n × Fin r) (c : PairSystemInputIndex n r)
    (ψ : ComplexVector n → ℝ) (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a)
    (hψ : DifferentiableAt ℝ ψ z) :
    complexFormalAdjointTestRow realVec (alternatingPairFirstOrderDerivative (r := r) E g.form h φ a)
      (alternatingPairFirstOrderValue (r := r) E g.form h φ a) row c ψ z =
      match c with
      | .inl β => star ((∑ γ,BundleDbar.metricMatrix (r := r) E h a z β γ *
          chartDbarAdjoint (r := r) E g.form h φ a (oneRowModelTest row (fun w => (ψ w : ℂ))) z γ) *
            (Real.exp (-φ (chartInv a z)) : ℂ))
      | .inr p => (1/2 : ℂ)*star (chartTwoDual E g.form h φ a
          (modelOneDbar (oneRowModelTest row (fun w => (ψ w : ℂ)))) z p.1.2 p.2 p.1.1) := by
  cases c with
  | inl β => exact topDualFirstOrder_formal_test_row E g h hh φ hφ a row β ψ z hz hψ
  | inr p => exact alternatingTwoDual_formal_test_row E g h hh φ hφ a row p ψ z hz hψ

theorem chartOneDual_source_oneRowModelTest_star (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (a : M.Carrier) (row : Fin n × Fin r) (ψ : ComplexVector n → ℂ)
    (F : ComplexVector n → Fin n → ComplexVector r) (z : ComplexVector n)
    (hz : z ∈ localDomain (r := r) E a) :
    star (∑ i,∑ α,star (F z i α)*chartOneDual (r := r) E g h φ a (oneRowModelTest row ψ) z i α) =
      chartOneDual (r := r) E g h φ a F z row.1 row.2 * star (ψ z) := by
  simp only [star_sum,star_mul,star_star,chartOneDual_oneRowModelTest_star E g h φ a row ψ z hz]
  rw [chartOneDual_eq_weighted_matrix]
  simp only [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro α _
  ring

end Yau.LeafProofs.L14Aux
