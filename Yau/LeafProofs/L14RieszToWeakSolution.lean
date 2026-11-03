import Yau.LeafProofs.L14RieszChartPair
import Yau.LeafProofs.L14OneDualInverse

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

theorem chartOneDual_oneWeightedDualInverse (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (a : M.Carrier) (w : ComplexVector n → (Fin n × Fin r) → ℂ)
    (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) (j : Fin n) (α : Fin r) :
    chartOneDual E g h φ a (oneWeightedDualInverse E g h φ a w) z j α = w z (j,α) := by
  classical
  let A := chartOneMetricMatrix (r := r) E g h a z
  let c : ℂ := Real.exp (φ (chartInv a z))
  let ρ : ℂ := Real.exp (-φ (chartInv a z))
  have hρc : ρ * c = 1 := by
    dsimp only [ρ,c]
    rw [← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one]
  have hcancel : A *ᵥ (A⁻¹ *ᵥ w z) = w z := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      ((chartOneMetricMatrix_posDef E g h a z hz).isUnit.map Matrix.detMonoidHom), Matrix.one_mulVec]
  have hR : (fun d : Fin n × Fin r => oneWeightedDualInverse E g h φ a w z d.1 d.2) =
      c • (A⁻¹ *ᵥ w z) := by
    funext d
    rfl
  rw [chartOneDual_eq_weighted_matrix, hR, Matrix.mulVec_smul, hcancel]
  change ρ * (c * w z (j,α)) = _
  rw [← mul_assoc,hρc,one_mul]

theorem oneWeightedDualInverse_contDiff (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (w : ComplexVector n → (Fin n × Fin r) → ℂ)
    (hw : ∀ c, ContDiff ℝ ∞ (fun z => w z c))
    (K : Set (ComplexVector n)) (hK : IsClosed K) (hKO : K ⊆ localDomain (r := r) E a)
    (hsw : ∀ c, tsupport (fun z => w z c) ⊆ K) :
    ContDiff ℝ ∞ (oneWeightedDualInverse E g.form h φ a w) := by
  have hs := oneWeightedDualInverse_tsupport E g.form h φ a w hK hsw
  apply contDiff_pi.mpr
  intro j
  apply (contDiff_piLp 2).mpr
  intro α
  apply contDiff_of_contDiffOn_of_tsupport_subset (localDomain_isOpen E a) _ _
    ((tsupport_comp_subset (g := fun F : Fin n → ComplexVector r => F j α) (by rfl) _).trans (hs.trans hKO))
  change ContDiffOn ℝ ∞ (fun z => (Real.exp (φ (chartInv a z)) : ℂ) *
    ∑ c, (chartOneMetricMatrix (r := r) E g.form h a z)⁻¹ (j,α) c * w z c) _
  simp_rw [Finset.mul_sum, ← mul_assoc]
  exact ContDiffOn.sum (fun c _ =>
    (oneWeightedDualInverse_coefficient_contDiffOn E g h hh φ hφ a (j,α) c).mul (hw c).contDiffOn)

variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
  (hE : Holomorphic (r := r) E)

include hE in
/-- Removing the degree-two Riesz term gives the actual scalar chart identity. -/
theorem compact_joint_riesz_annihilation_chart_identity
    (f : NQForm E 1) (hf : LocallyL2 (r := r) E f)
    (u : WeightedTopHilbert E g μ hμ h hh φ hφ)
    (w : WeightedTwoHilbert E g μ hμ h hh φ hφ)
    (hrep : ∀ t : CompactJointTriple E g μ hμ h hh φ hφ,
      IsCompactJointTriple E g μ hμ h hh φ hφ t →
      inner ℂ u (realizeWeightedTopSection E g μ hμ h hh φ hφ t.2.1) +
        inner ℂ w (realizeWeightedTwoSection E g μ hμ h hh φ hφ t.2.2) =
          weightedOneInner E g.form μ h φ f t.1.1)
    (hann : ∀ t : CompactJointTriple E g μ hμ h hh φ hφ,
      IsCompactJointTriple E g μ hμ h hh φ hφ t →
        inner ℂ w (realizeWeightedTwoSection E g μ hμ h hh φ hφ t.2.2) = 0)
    (a : M.Carrier) (G : ComplexVector n → Fin n → ComplexVector r)
    (hG : ContDiff ℝ ∞ G) (hcG : HasCompactSupport G)
    (hsG : tsupport G ⊆ localDomain (r := r) E a) :
    (∫ z, ∑ i, ∑ α, star (coefficients (r := r) E f a z (fun _ => i) α) *
      chartOneDual E g.form h φ a G z i α ∂lebesgueC n) =
    (∫ z, ∑ α,
      star (coefficients (r := r) E (weightedTopHilbertRepresentative E g μ hμ h hh φ hφ u).1 a z Fin.elim0 α) *
        ((∑ β, BundleDbar.metricMatrix (r := r) E h a z α β * chartDbarAdjoint E g.form h φ a G z β) *
          (Real.exp (-φ (chartInv a z)) : ℂ)) ∂lebesgueC n) := by
  classical
  let U := weightedTopHilbertRepresentative E g μ hμ h hh φ hφ u
  let δ := chartDbarAdjoint E g.form h φ a G
  have hδ := chartDbarAdjoint_contDiff E g h hh φ hφ a G hG hsG
  have hcδ := hcG.of_isClosed_subset (isClosed_tsupport _) (tsupport_chartDbarAdjoint_subset E g.form h φ a G)
  have hsδ := (tsupport_chartDbarAdjoint_subset E g.form h φ a G).trans hsG
  have ht := compactChartJointTriple_isCompact E g μ hμ h hh φ hφ hE a G hG hcG hsG
  have he := hrep _ ht
  rw [hann _ ht, add_zero] at he
  have htop : inner ℂ u (realizeWeightedTopSection E g μ hμ h hh φ hφ
      (weightedDbarAdjointChartSection E g μ hμ h hh φ hφ hE a G hG hcG hsG)) =
      (2 : ℝ)^n • (∫ z, ∑ α, star (coefficients (r := r) E U.1 a z Fin.elim0 α) *
        ((∑ β, BundleDbar.metricMatrix (r := r) E h a z α β * δ z β) *
          (Real.exp (-φ (chartInv a z)) : ℂ)) ∂lebesgueC n) := by
    rw [← weightedTopHilbertRepresentative_realize E g μ hμ h hh φ hφ u,realizeWeightedTopSection_inner]
    change weightedTopInner E g.form μ h φ U.1 (topFormPushforward E a δ) = _
    rw [weightedTopInner_topFormPushforward_right E g μ hμ h hh φ hφ hE a δ hδ hcδ hsδ U]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      simp only [Finset.sum_mul,Finset.mul_sum,mul_assoc]
  change inner ℂ u (realizeWeightedTopSection E g μ hμ h hh φ hφ
    (weightedDbarAdjointChartSection E g μ hμ h hh φ hφ hE a G hG hcG hsG)) =
      weightedOneInner E g.form μ h φ f (oneFormPushforward E a G) at he
  rw [htop,locallyL2_weightedOneInner_oneFormPushforward E g μ hμ h hh φ hφ hE f hf a G hG hcG hsG] at he
  exact smul_right_injective ℂ (pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)) he.symm

/-- The weighted adjoint divergence identity also holds off the chart for supported tests. -/
theorem chartDbarAdjoint_dual_of_tsupport_subset (a : M.Carrier)
    (G : ComplexVector n → Fin n → ComplexVector r)
    (hsG : tsupport G ⊆ localDomain (r := r) E a) (z : ComplexVector n) (α : Fin r) :
    (∑ β, BundleDbar.metricMatrix (r := r) E h a z α β * chartDbarAdjoint E g.form h φ a G z β) *
      (Real.exp (-φ (chartInv a z)) : ℂ) =
        -∑ i, wirt (fun y => chartOneDual E g.form h φ a G y i α) z (stdVec i) := by
  by_cases hz : z ∈ localDomain (r := r) E a
  · exact chartDbarAdjoint_dual E g.form h φ a G z hz α
  · have hn : z ∉ tsupport G := fun ht => hz (hsG ht)
    have hd : chartDbarAdjoint E g.form h φ a G z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun ht => hn (tsupport_chartDbarAdjoint_subset E g.form h φ a G ht))
    have hw (i : Fin n) : wirt (fun y => chartOneDual E g.form h φ a G y i α) z (stdVec i) = 0 :=
      image_eq_zero_of_notMem_tsupport
        (f := fun y => wirt (fun y => chartOneDual E g.form h φ a G y i α) y (stdVec i))
        (fun ht => hn (tsupport_chartOneDual_subset E g.form h φ a G i α (tsupport_wirt_subset _ _ ht)))
    simp only [hd, PiLp.zero_apply, mul_zero, Finset.sum_const_zero, zero_mul, hw, neg_zero]

include hE in
/-- The compact Riesz identity and annihilation of its actual degree-two graph term
imply the distributional Dolbeault equation for the original locally L² source. -/
theorem weakDbar_of_compact_joint_riesz_annihilation
    (f : NQForm E 1) (hf : LocallyL2 (r := r) E f)
    (u : WeightedTopHilbert E g μ hμ h hh φ hφ)
    (w : WeightedTwoHilbert E g μ hμ h hh φ hφ)
    (hrep : ∀ t : CompactJointTriple E g μ hμ h hh φ hφ,
      IsCompactJointTriple E g μ hμ h hh φ hφ t →
      inner ℂ u (realizeWeightedTopSection E g μ hμ h hh φ hφ t.2.1) +
        inner ℂ w (realizeWeightedTwoSection E g μ hμ h hh φ hφ t.2.2) =
          weightedOneInner E g.form μ h φ f t.1.1)
    (hann : ∀ t : CompactJointTriple E g μ hμ h hh φ hφ,
      IsCompactJointTriple E g μ hμ h hh φ hφ t →
        inner ℂ w (realizeWeightedTwoSection E g μ hμ h hh φ hφ t.2.2) = 0) :
    WeakDbar (r := r) E (weightedTopHilbertRepresentative E g μ hμ h hh φ hφ u).1 f := by
  classical
  let U := weightedTopHilbertRepresentative E g μ hμ h hh φ hφ u
  apply (weakDbar_zero_iff_component_tests E U.1 f).mpr
  refine ⟨U.2.1,hf,?_⟩
  intro a i α ψ hψ hcψ hsψ
  let v := fun z (c : Fin n × Fin r) => if c.1 = i then if c.2 = α then star (ψ z) else 0 else 0
  have hv (c : Fin n × Fin r) : ContDiff ℝ ∞ (fun z => v z c) := by
    dsimp only [v]
    split_ifs <;> first | exact Complex.conjCLE.contDiff.comp hψ | exact contDiff_const
  have hsv (c : Fin n × Fin r) : tsupport (fun z => v z c) ⊆ tsupport ψ := by
    dsimp only [v]
    split_ifs
    · exact tsupport_comp_subset (star_zero ℂ) ψ
    all_goals simp
  let G := oneWeightedDualInverse E g.form h φ a v
  have hsGK : tsupport G ⊆ tsupport ψ :=
    oneWeightedDualInverse_tsupport E g.form h φ a v (isClosed_tsupport ψ) hsv
  have hsG := hsGK.trans hsψ
  have hcG : HasCompactSupport G := hcψ.of_isClosed_subset (isClosed_tsupport G) hsGK
  have hG : ContDiff ℝ ∞ G :=
    oneWeightedDualInverse_contDiff E g h hh φ hφ a v hv (tsupport ψ) (isClosed_tsupport ψ) hsψ hsv
  have hB (z : ComplexVector n) (j : Fin n) (β : Fin r) :
      chartOneDual E g.form h φ a G z j β = v z (j,β) := by
    by_cases hz : z ∈ localDomain (r := r) E a
    · exact chartOneDual_oneWeightedDualInverse E g.form h φ a v z hz j β
    · have hn : z ∉ tsupport G := fun ht => hz (hsG ht)
      have hleft : chartOneDual E g.form h φ a G z j β = 0 :=
        image_eq_zero_of_notMem_tsupport (f := fun z => chartOneDual E g.form h φ a G z j β)
          (fun ht => hn (tsupport_chartOneDual_subset E g.form h φ a G j β ht))
      have hright : v z (j,β) = 0 := image_eq_zero_of_notMem_tsupport (f := fun z => v z (j,β))
        (fun ht => hz (hsψ (hsv (j,β) ht)))
      exact hleft.trans hright.symm
  have hBfun (j : Fin n) (β : Fin r) :
      (fun z => chartOneDual E g.form h φ a G z j β) =
      (fun z => if j = i then if β = α then star (ψ z) else 0 else 0) :=
    funext fun z => hB z j β
  have hwzero (z d : ComplexVector n) : wirt (fun _ : ComplexVector n => (0 : ℂ)) z d = 0 := by
    simp [wirt]
  have hBwirt (z : ComplexVector n) (j : Fin n) (β : Fin r) :
      wirt (fun y => chartOneDual E g.form h φ a G y j β) z (stdVec j) =
      if j = i then if β = α then star (wirtBar ψ z (stdVec i)) else 0 else 0 := by
    rw [hBfun]
    by_cases hji : j = i
    · subst j
      by_cases hβα : β = α
      · subst β
        simp only [ite_true]
        exact wirt_star ψ z (stdVec i)
      · simp only [hβα,ite_false,ite_true,hwzero]
    · simp only [hji,ite_false,hwzero]
  have hδ (z : ComplexVector n) (β : Fin r) :
      (∑ γ, BundleDbar.metricMatrix (r := r) E h a z β γ * chartDbarAdjoint E g.form h φ a G z γ) *
        (Real.exp (-φ (chartInv a z)) : ℂ) =
        if β = α then -(star (wirtBar ψ z (stdVec i))) else 0 := by
    rw [chartDbarAdjoint_dual_of_tsupport_subset E g h φ a G hsG z β]
    simp_rw [hBwirt]
    by_cases hβα : β = α <;> simp [hβα]
  have he := compact_joint_riesz_annihilation_chart_identity E g μ hμ h hh φ hφ hE
    f hf u w hrep hann a G hG hcG hsG
  have hleft : (∫ z, ∑ j, ∑ β, star (coefficients (r := r) E f a z (fun _ => j) β) *
      chartOneDual E g.form h φ a G z j β ∂lebesgueC n) =
      star (∫ z, coefficients (r := r) E f a z (fun _ => i) α * ψ z ∂lebesgueC n) := by
    rw [integral_star_complex]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [hB,v]
    simp [star_mul,mul_comm]
  have hright : (∫ z, ∑ β, star (coefficients (r := r) E U.1 a z Fin.elim0 β) *
      ((∑ γ, BundleDbar.metricMatrix (r := r) E h a z β γ * chartDbarAdjoint E g.form h φ a G z γ) *
        (Real.exp (-φ (chartInv a z)) : ℂ)) ∂lebesgueC n) =
      -(star (∫ z, coefficients (r := r) E U.1 a z Fin.elim0 α * wirtBar ψ z (stdVec i) ∂lebesgueC n)) := by
    rw [integral_star_complex, ← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [hδ]
    simp [star_mul,mul_comm]
  rw [hleft,hright] at he
  simpa only [star_star,star_neg] using congrArg star he

/-- The representative inherits the Hilbert squared norm bound without loss. -/
theorem weightedTopHilbertRepresentative_normSq_le
    (u : WeightedTopHilbert E g μ hμ h hh φ hφ) (A : ℝ≥0∞)
    (hA : A < ⊤) (hu : ‖u‖ ^ 2 ≤ A.toReal) :
    weightedNormSq (r := r) E g.form h μ φ
      (weightedTopHilbertRepresentative E g μ hμ h hh φ hφ u).1 ≤ A := by
  rw [weightedTopHilbertRepresentative_normSq E g μ hμ h hh φ hφ u]
  exact (ENNReal.ofReal_le_iff_le_toReal hA.ne).mpr hu

end Yau.LeafProofs.L14Aux
