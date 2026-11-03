import Yau.LeafProofs.L14RieszChartPair
import Yau.LeafProofs.L14AlternatingPairSystem
import Yau.LeafProofs.L14CompactLpFields
import Yau.LeafProofs.L14ComplexRows

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

def pairForcingDual (f : NQForm E 1) (a : M.Carrier) (z : ComplexVector n) (row : Fin n × Fin r) : ℂ :=
  chartOneDual (r := r) E g.form h φ a (fun w j => coefficients (r := r) E f a w (fun _ => j)) z row.1 row.2

include hh hφ in
theorem alternatingPair_formal_test_properties (a : M.Carrier) (row : Fin n × Fin r)
    (c : PairSystemInputIndex n r) (ψ : ComplexVector n → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ localDomain (r := r) E a) :
    let θ := complexFormalAdjointTestRow realVec (alternatingPairFirstOrderDerivative (r := r) E g.form h φ a)
      (alternatingPairFirstOrderValue (r := r) E g.form h φ a) row c ψ
    ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧ tsupport θ ⊆ tsupport ψ := by
  let θ := complexFormalAdjointTestRow realVec (alternatingPairFirstOrderDerivative (r := r) E g.form h φ a)
    (alternatingPairFirstOrderValue (r := r) E g.form h φ a) row c ψ
  have hs : tsupport θ ⊆ tsupport ψ := complexFormalAdjointTestRow_tsupport_subset _ _ _ row c ψ
  refine ⟨?_,hcψ.of_isClosed_subset (isClosed_tsupport _) hs,hs⟩
  apply contDiff_of_contDiffOn_of_tsupport_subset (localDomain_isOpen (r := r) E a) _ _ (hs.trans hsψ)
  exact complexFormalAdjointTestRow_contDiffOn (localDomain_isOpen E a) realVec _ _
    (alternatingPairFirstOrderDerivative_contDiffOn E g h hh φ hφ a)
    (alternatingPairFirstOrderValue_contDiffOn E g h hh φ hφ a) row c ψ hψ

variable (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K)
  (hKO : K ⊆ localDomain (r := r) E a)

theorem compactPairHilbertField_zero_off
    (u : WeightedTopHilbert E g μ hμ h hh φ hφ) (w : WeightedTwoHilbert E g μ hμ h hh φ hφ)
    (c : PairSystemInputIndex n r) (z : ComplexVector n) (hz : z ∉ K) :
    compactPairHilbertField E g μ hμ h hh φ hφ a K hK hKO u w z c = 0 :=
  image_eq_zero_of_notMem_tsupport (f := fun y => compactPairHilbertField E g μ hμ h hh φ hφ a K hK hKO u w y c) (fun ht => hz (compactPairHilbertField_tsupport E g μ hμ h hh φ hφ a K hK hKO u w c ht))

include hE in
theorem compact_joint_pair_complex_row
    (f : NQForm E 1) (hf : LocallyL2 (r := r) E f)
    (u : WeightedTopHilbert E g μ hμ h hh φ hφ) (w : WeightedTwoHilbert E g μ hμ h hh φ hφ)
    (hrep : ∀ t : CompactJointTriple E g μ hμ h hh φ hφ,
      IsCompactJointTriple E g μ hμ h hh φ hφ t →
      inner ℂ u (realizeWeightedTopSection E g μ hμ h hh φ hφ t.2.1) +
        inner ℂ w (realizeWeightedTwoSection E g μ hμ h hh φ hφ t.2.2) = weightedOneInner E g.form μ h φ f t.1.1)
    (row : Fin n × Fin r) (ψ : ComplexVector n → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ K) :
    (∫ z,(ψ z : ℂ)*pairForcingDual E g h φ f a z row ∂lebesgueC n) =
      ∫ z,∑ c,compactPairHilbertField E g μ hμ h hh φ hφ a K hK hKO u w z c *
        complexFormalAdjointTestRow realVec (alternatingPairFirstOrderDerivative (r := r) E g.form h φ a)
          (alternatingPairFirstOrderValue (r := r) E g.form h φ a) row c ψ z ∂lebesgueC n := by
  classical
  let G := oneRowModelTest row (fun z => (ψ z : ℂ))
  let U := weightedTopHilbertRepresentative E g μ hμ h hh φ hφ u
  let X := compactPairHilbertField E g μ hμ h hh φ hφ a K hK hKO u w
  let θ := fun c => complexFormalAdjointTestRow realVec (alternatingPairFirstOrderDerivative (r := r) E g.form h φ a)
    (alternatingPairFirstOrderValue (r := r) E g.form h φ a) row c ψ
  have hψC : ContDiff ℝ ∞ (fun z => (ψ z : ℂ)) := Complex.ofRealCLM.contDiff.comp hψ
  obtain ⟨hG,hcG,hsGψ⟩ := oneRowModelTest_properties row (fun z => (ψ z : ℂ)) hψC (hcψ.comp_left Complex.ofReal_zero)
  have hsG : tsupport G ⊆ K := hsGψ.trans ((tsupport_comp_subset (g := fun t : ℝ => (t : ℂ)) Complex.ofReal_zero ψ).trans hsψ)
  have hT (c : PairSystemInputIndex n r) : Integrable (fun z => X z c*θ c z) (lebesgueC n) := by
    obtain ⟨hθ,hcθ,_⟩ := alternatingPair_formal_test_properties E g h hh φ hφ a row c ψ hψ hcψ (hsψ.trans hKO)
    have hmθ : MemLp (θ c) 2 (lebesgueC n) := by
      rw [lebesgueC_eq_volume]
      exact hθ.continuous.memLp_of_hasCompactSupport hcθ
    exact test_mul_integrable_of_memLp _ _ _ (compactPairHilbertField_memLp E g μ hμ h hh φ hφ a K hK hKO u w c) hmθ
  let S := fun z => ∑ i,∑ α,star (coefficients (r := r) E f a z (fun _ => i) α)*chartOneDual E g.form h φ a G z i α
  let T := fun z => ∑ α,star (coefficients (r := r) E U.1 a z Fin.elim0 α)*
    ((∑ β,BundleDbar.metricMatrix (r := r) E h a z α β*chartDbarAdjoint E g.form h φ a G z β)*(Real.exp (-φ (chartInv a z)) : ℂ))
  have hSzero (z : ComplexVector n) (hz : z ∉ K) : S z = 0 := by
    have hn : z ∉ tsupport G := fun ht => hz (hsG ht)
    have hzG : G z = 0 := image_eq_zero_of_notMem_tsupport hn
    simp only [S,chartOneDual,hzG,Pi.zero_apply,PiLp.zero_apply,mul_zero,Finset.sum_const_zero]
  have hTzero (z : ComplexVector n) (hz : z ∉ K) : T z = 0 := by
    have hzδ : chartDbarAdjoint E g.form h φ a G z = 0 := image_eq_zero_of_notMem_tsupport
      (fun ht => hz (hsG (tsupport_chartDbarAdjoint_subset E g.form h φ a G ht)))
    simp only [T,hzδ,PiLp.zero_apply,mul_zero,Finset.sum_const_zero,zero_mul]
  have hSrestrict : (∫ z,S z ∂lebesgueC n) = ∫ z in K,S z ∂lebesgueC n :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hSzero).symm
  have hTrestrict : (∫ z,T z ∂lebesgueC n) = ∫ z in K,T z ∂lebesgueC n :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hTzero).symm
  have he := compact_joint_riesz_pair_chart_identity E g μ hμ h hh φ hφ hE a K hK hKO f hf u w hrep G hG hcG hsG
  change (∫ z,S z ∂lebesgueC n) = (∫ z,T z ∂lebesgueC n) + _ at he
  rw [hSrestrict,hTrestrict] at he
  have hc := congrArg star he
  have hhalf : star (1/2 : ℂ) = (1/2 : ℂ) := by norm_num
  simp only [star_add,star_mul,star_sum,hhalf,integral_star_complex] at hc
  have hsource : (∫ z in K,star (S z) ∂lebesgueC n) = ∫ z in K,(ψ z : ℂ)*pairForcingDual E g h φ f a z row ∂lebesgueC n := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    change star (∑ i,∑ α,star (coefficients (r := r) E f a z (fun _ => i) α)*
      chartOneDual E g.form h φ a (oneRowModelTest row (fun z => (ψ z : ℂ))) z i α) = _
    rw [chartOneDual_source_oneRowModelTest_star E g.form h φ a row (fun z => (ψ z : ℂ))
      (fun w j => coefficients (r := r) E f a w (fun _ => j)) z (hKO hz)]
    have hstar : star ((ψ z : ℝ) : ℂ) = ((ψ z : ℝ) : ℂ) := Complex.conj_ofReal _
    rw [hstar]
    exact mul_comm _ _
  have htop : (∫ z in K,star (T z) ∂lebesgueC n) = ∑ β,∫ z in K,X z (.inl β)*θ (.inl β) z ∂lebesgueC n := by
    have hcoef := ae_all_iff.mpr (fun β => compactTopHilbertField_representative_ae E g μ hμ h hh φ hφ a K hK hKO u β)
    calc
      _ = ∫ z in K,∑ β,X z (.inl β)*θ (.inl β) z ∂lebesgueC n := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hK.measurableSet,hcoef] with z hz hcoord
        simp only [T,star_sum,star_mul,star_star]
        apply Finset.sum_congr rfl
        intro β _
        have hθ := alternatingPair_formal_test_row E g h hh φ hφ a row (.inl β) ψ z (hKO hz) (hψ.differentiable (by simp) z)
        change θ (.inl β) z = _ at hθ
        rw [hθ]
        change _ = compactTopHilbertField E g μ hμ h hh φ hφ a K hK hKO u z β * _
        rw [hcoord β]
        dsimp only [U,G]
        simp only [star_mul,star_sum]
        ring
      _ = _ := integral_finsetSum _ fun β _ => (hT (.inl β)).mono_measure Measure.restrict_le_self
  have htwo (i j : Fin n) (α : Fin r) :
      (1/2 : ℂ)*(∫ z in K,star (star (weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hKO ((α,i),j) w z)*
        chartTwoDual E g.form h φ a (modelOneDbar G) z i j α) ∂lebesgueC n) =
      ∫ z in K,X z (.inr ((α,i),j))*θ (.inr ((α,i),j)) z ∂lebesgueC n := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hK.measurableSet,
      compactTwoHilbertField_ae_restrict E g μ hμ h hh φ hφ a K hK hKO w ((α,i),j)] with z hz hcoord
    have hθ := alternatingPair_formal_test_row E g h hh φ hφ a row (.inr ((α,i),j)) ψ z (hKO hz) (hψ.differentiable (by simp) z)
    change θ (.inr ((α,i),j)) z = _ at hθ
    rw [hθ]
    change _ = compactTwoHilbertField E g μ hμ h hh φ hφ a K hK hKO w z ((α,i),j)*_
    rw [hcoord]
    simp only [star_mul,star_star]
    ring
  have htwoSum : (1/2 : ℂ)*∑ i,∑ j,∑ α,∫ z in K,
      star (star (weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hKO ((α,i),j) w z)*
        chartTwoDual E g.form h φ a (modelOneDbar G) z i j α) ∂lebesgueC n =
      ∑ p : TwoCoefficientIndex n r,∫ z in K,X z (.inr p)*θ (.inr p) z ∂lebesgueC n := by
    simp only [Finset.mul_sum,htwo,Fintype.sum_prod_type]
    symm
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  have hrhs : (∫ z in K,∑ c,X z c*θ c z ∂lebesgueC n) =
      (∑ β,∫ z in K,X z (.inl β)*θ (.inl β) z ∂lebesgueC n) +
        ∑ p : TwoCoefficientIndex n r,∫ z in K,X z (.inr p)*θ (.inr p) z ∂lebesgueC n := by
    rw [integral_finsetSum Finset.univ (fun c _ => (hT c).mono_measure Measure.restrict_le_self),Fintype.sum_sum_type]
  have hglobalSource : (∫ z in K,(ψ z : ℂ)*pairForcingDual E g h φ f a z row ∂lebesgueC n) =
      ∫ z,(ψ z : ℂ)*pairForcingDual E g h φ f a z row ∂lebesgueC n := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hzero : ψ z = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hz (hsψ ht))
    rw [hzero,Complex.ofReal_zero,zero_mul]
  have hglobalRhs : (∫ z in K,∑ c,X z c*θ c z ∂lebesgueC n) =
      ∫ z,∑ c,X z c*θ c z ∂lebesgueC n := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    apply Finset.sum_eq_zero
    intro c _
    rw [show X z c = 0 from compactPairHilbertField_zero_off E g μ hμ h hh φ hφ a K hK hKO u w c z hz,zero_mul]
  rw [hsource,htop] at hc
  have htwoSum' : (∑ i,∑ j,∑ α,∫ z in K,
      star (star (weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hKO ((α,i),j) w z)*
        chartTwoDual E g.form h φ a (modelOneDbar G) z i j α) ∂lebesgueC n)*(1/2 : ℂ) =
      ∑ p : TwoCoefficientIndex n r,∫ z in K,X z (.inr p)*θ (.inr p) z ∂lebesgueC n := by
    rw [mul_comm]
    exact htwoSum
  simp only [star_mul] at htwoSum'
  rw [htwoSum',← hrhs,hglobalSource,hglobalRhs] at hc
  exact hc

end Yau.LeafProofs.L14Aux
