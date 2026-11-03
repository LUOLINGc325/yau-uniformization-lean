import Yau.LeafProofs.L14AlternatingPairSystem
import Yau.LeafProofs.L14OneDualInverse
import Yau.LeafProofs.L14OneChartCauchy

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder ENNReal
open MeasureTheory Bundle Filter Module
namespace Yau.LeafProofs.L14Aux
open BundleDbar

def pairModelTop {n r : ℕ} (F : ComplexVector n → PairSystemInputIndex n r → ℂ)
    (z : ComplexVector n) : ComplexVector r := WithLp.toLp 2 (fun α => F z (.inl α))

def pairModelTwo {n r : ℕ} (F : ComplexVector n → PairSystemInputIndex n r → ℂ)
    (z : ComplexVector n) (i j : Fin n) : ComplexVector r := WithLp.toLp 2 (fun α => F z (.inr ((α,i),j)))

theorem pairSystemInput_pairModels {n r : ℕ} (F : ComplexVector n → PairSystemInputIndex n r → ℂ) :
    pairSystemInput (pairModelTop F) (pairModelTwo F) = F := by
  funext z c
  cases c <;> rfl

theorem pairModels_properties {n r : ℕ} (F : ComplexVector n → PairSystemInputIndex n r → ℂ)
    (hF : ∀ c,ContDiff ℝ ∞ (fun z => F z c)) {K : Set (ComplexVector n)}
    (hK : IsClosed K) (hsF : ∀ c,tsupport (fun z => F z c) ⊆ K) :
    ContDiff ℝ ∞ (pairModelTop F) ∧ ContDiff ℝ ∞ (pairModelTwo F) ∧
      tsupport (pairModelTop F) ⊆ K ∧ tsupport (pairModelTwo F) ⊆ K := by
  have hz (z : ComplexVector n) (hn : z ∉ K) (c : PairSystemInputIndex n r) : F z c = 0 :=
    image_eq_zero_of_notMem_tsupport (f := fun w => F w c) (fun ht => hn (hsF c ht))
  refine ⟨(contDiff_piLp 2).mpr (fun α => hF (.inl α)),?_,?_,?_⟩
  · apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    exact (contDiff_piLp 2).mpr fun α => hF (.inr ((α,i),j))
  · apply closure_minimal _ hK
    intro z hzne
    by_contra hn
    apply hzne
    apply PiLp.ext
    intro α
    simp only [pairModelTop,WithLp.ofLp_toLp,hz z hn,PiLp.zero_apply]
  · apply closure_minimal _ hK
    intro z hzne
    by_contra hn
    apply hzne
    funext i j
    apply PiLp.ext
    intro α
    simp only [pairModelTwo,WithLp.ofLp_toLp,hz z hn,Pi.zero_apply,PiLp.zero_apply]

theorem complexFirstOrderSystemApply_tsupport_subset {n : ℕ} {α β ι : Type*} [Fintype α] [Fintype ι]
    (v : ι → ComplexVector n) (A : β → α → ι → ComplexVector n → ℂ)
    (B : β → α → ComplexVector n → ℂ) (F : ComplexVector n → α → ℂ)
    {K : Set (ComplexVector n)} (hK : IsClosed K) (hsF : ∀ c,tsupport (fun z => F z c) ⊆ K) (row : β) :
    tsupport (fun z => complexFirstOrderSystemApply v A B F z row) ⊆ K := by
  apply closure_minimal _ hK
  intro z hzne
  by_contra hn
  have hzero (c : α) : F z c = 0 := image_eq_zero_of_notMem_tsupport (f := fun w => F w c) (fun ht => hn (hsF c ht))
  have hd (c : α) : fderiv ℝ (fun w => F w c) z = 0 :=
    fderiv_of_notMem_tsupport (𝕜 := ℝ) (fun ht => hn (hsF c ht))
  apply hzne
  simp only [complexFirstOrderSystemApply,hzero,hd,zero_apply,mul_zero,Finset.sum_const_zero,zero_add]

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)] [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

def pairOneOutputModel (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (a : M.Carrier) (F : ComplexVector n → PairSystemInputIndex n r → ℂ)
    (z : ComplexVector n) (j : Fin n) : ComplexVector r :=
  modelTopDbar (pairModelTop F) z j + chartTwoDbarAdjoint E g h φ a (alternatingTwoModel (pairModelTwo F)) z j

theorem pairOneOutputModel_properties (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (F : ComplexVector n → PairSystemInputIndex n r → ℂ)
    (hF : ∀ c,ContDiff ℝ ∞ (fun z => F z c))
    (K : Set (ComplexVector n)) (hK : IsCompact K) (hKO : K ⊆ localDomain (r := r) E a)
    (hsF : ∀ c,tsupport (fun z => F z c) ⊆ K) :
    ContDiff ℝ ∞ (pairOneOutputModel (r := r) E g.form h φ a F) ∧
      tsupport (pairOneOutputModel (r := r) E g.form h φ a F) ⊆ K := by
  obtain ⟨hA,hB,hsA,hsB⟩ := pairModels_properties F hF hK.isClosed hsF
  have hcB : HasCompactSupport (pairModelTwo F) := hK.of_isClosed_subset (isClosed_tsupport _) hsB
  obtain ⟨hAlt,hcAlt,hsAlt⟩ := alternatingTwoModel_properties (pairModelTwo F) hB hcB
  have hδ := chartTwoDbarAdjoint_contDiff E g h hh φ hφ a (alternatingTwoModel (pairModelTwo F)) hAlt (hsAlt.trans (hsB.trans hKO))
  have hsδ : tsupport (chartTwoDbarAdjoint E g.form h φ a (alternatingTwoModel (pairModelTwo F))) ⊆ K :=
    (tsupport_chartTwoDbarAdjoint_subset E g.form h φ a _).trans (hsAlt.trans hsB)
  have hsT : tsupport (modelTopDbar (pairModelTop F)) ⊆ K := (tsupport_modelTopDbar_subset _).trans hsA
  refine ⟨(modelTopDbar_smooth _ hA).add hδ,?_⟩
  apply closure_minimal _ hK.isClosed
  intro z hz
  by_contra hn
  have hzT : modelTopDbar (pairModelTop F) z = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hn (hsT ht))
  have hzδ : chartTwoDbarAdjoint E g.form h φ a (alternatingTwoModel (pairModelTwo F)) z = 0 :=
    image_eq_zero_of_notMem_tsupport (fun ht => hn (hsδ ht))
  apply hz
  funext j
  simp only [pairOneOutputModel,hzT,hzδ,Pi.zero_apply,zero_add]

theorem chartOneDual_add_models (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (a : M.Carrier) (A B : ComplexVector n → Fin n → ComplexVector r)
    (z : ComplexVector n) (j : Fin n) (α : Fin r) :
    chartOneDual (r := r) E g h φ a (fun z j => A z j+B z j) z j α =
      chartOneDual (r := r) E g h φ a A z j α+chartOneDual (r := r) E g h φ a B z j α := by
  simp only [chartOneDual,PiLp.add_apply,mul_add,Finset.sum_add_distrib,add_mul]

theorem pairOneOutputModel_dual (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (F : ComplexVector n → PairSystemInputIndex n r → ℂ)
    (hF : ∀ c,ContDiff ℝ ∞ (fun z => F z c))
    (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) (row : Fin n × Fin r) :
    complexFirstOrderSystemApply realVec (alternatingPairFirstOrderDerivative (r := r) E g.form h φ a)
      (alternatingPairFirstOrderValue (r := r) E g.form h φ a) F z row =
      chartOneDual (r := r) E g.form h φ a (pairOneOutputModel (r := r) E g.form h φ a F) z row.1 row.2 := by
  have hB : ContDiff ℝ ∞ (pairModelTwo F) := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    exact (contDiff_piLp 2).mpr fun α => hF (.inr ((α,i),j))
  rw [← pairSystemInput_pairModels F,alternatingPairFirstOrder_apply E g h hh φ hφ a (pairModelTop F) (pairModelTwo F) hB z hz row]
  exact (chartOneDual_add_models E g.form h φ a _ _ z row.1 row.2).symm

theorem pairOneOutputModel_eq_inverse (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (F : ComplexVector n → PairSystemInputIndex n r → ℂ)
    (hF : ∀ c,ContDiff ℝ ∞ (fun z => F z c))
    (K : Set (ComplexVector n)) (hK : IsCompact K) (hKO : K ⊆ localDomain (r := r) E a)
    (hsF : ∀ c,tsupport (fun z => F z c) ⊆ K) (z : ComplexVector n) (j : Fin n) (α : Fin r) :
    pairOneOutputModel (r := r) E g.form h φ a F z j α =
      oneWeightedDualInverse (r := r) E g.form h φ a
        (complexFirstOrderSystemApply realVec (alternatingPairFirstOrderDerivative (r := r) E g.form h φ a)
          (alternatingPairFirstOrderValue (r := r) E g.form h φ a) F) z j α := by
  by_cases hz : z ∈ localDomain (r := r) E a
  · have he : (fun y c => complexFirstOrderSystemApply realVec (alternatingPairFirstOrderDerivative (r := r) E g.form h φ a)
        (alternatingPairFirstOrderValue (r := r) E g.form h φ a) F y c) z =
      fun c => chartOneDual (r := r) E g.form h φ a (pairOneOutputModel (r := r) E g.form h φ a F) z c.1 c.2 :=
      funext fun c => pairOneOutputModel_dual E g h hh φ hφ a F hF z hz c
    change _ = (Real.exp (φ (chartInv a z)) : ℂ)*∑ c,(chartOneMetricMatrix (r := r) E g.form h a z)⁻¹ (j,α) c*_
    simp_rw [congrFun he]
    exact (oneWeightedDualInverse_chartOneDual E g.form h φ a (pairOneOutputModel (r := r) E g.form h φ a F) z hz j α).symm
  · have hn : z ∉ K := fun ht => hz (hKO ht)
    have hRz : pairOneOutputModel (r := r) E g.form h φ a F z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun ht => hn ((pairOneOutputModel_properties E g h hh φ hφ a F hF K hK hKO hsF).2 ht))
    have hPz (c : Fin n × Fin r) : complexFirstOrderSystemApply realVec (alternatingPairFirstOrderDerivative (r := r) E g.form h φ a)
        (alternatingPairFirstOrderValue (r := r) E g.form h φ a) F z c = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun y => complexFirstOrderSystemApply realVec (alternatingPairFirstOrderDerivative (r := r) E g.form h φ a)
        (alternatingPairFirstOrderValue (r := r) E g.form h φ a) F y c)
        (fun ht => hn (complexFirstOrderSystemApply_tsupport_subset realVec _ _ F hK.isClosed hsF c ht))
    simp only [hRz,Pi.zero_apply,PiLp.zero_apply,oneWeightedDualInverse,WithLp.ofLp_toLp,hPz,mul_zero,Finset.sum_const_zero]

theorem pairOneOutputModel_cauchySeq_of_graph_errors
    (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (hE : Holomorphic (r := r) E)
    (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K) (hKO : K ⊆ localDomain (r := r) E a)
    (F : ℕ → ComplexVector n → PairSystemInputIndex n r → ℂ)
    (hF : ∀ m c,ContDiff ℝ ∞ (fun z => F m z c)) (hsF : ∀ m c,tsupport (fun z => F m z c) ⊆ K)
    (v : ComplexVector n → (Fin n × Fin r) → ℂ) (hsv : ∀ row,tsupport (fun z => v z row) ⊆ K)
    (he : ∀ m row,MemLp (fun z => complexFirstOrderSystemApply realVec
      (alternatingPairFirstOrderDerivative (r := r) E g.form h φ a) (alternatingPairFirstOrderValue (r := r) E g.form h φ a)
      (F m) z row-v z row) 2 (lebesgueC n))
    (ht : ∀ row,Tendsto (fun m => ∫ z,‖complexFirstOrderSystemApply realVec
      (alternatingPairFirstOrderDerivative (r := r) E g.form h φ a) (alternatingPairFirstOrderValue (r := r) E g.form h φ a)
      (F m) z row-v z row‖^2 ∂lebesgueC n) atTop (𝓝 0)) :
    let hR := fun m => pairOneOutputModel_properties E g h hh φ hφ a (F m) (hF m) K hK hKO (hsF m)
    CauchySeq (fun m => realizeWeightedOneSection E g μ hμ h hh φ hφ
      (weightedOneChartSection E g μ hμ h hh φ hφ hE a (pairOneOutputModel (r := r) E g.form h φ a (F m)) (hR m).1
        (hK.of_isClosed_subset (isClosed_tsupport _) (hR m).2) ((hR m).2.trans hKO))) := by
  dsimp only
  let P := fun m => complexFirstOrderSystemApply realVec
    (alternatingPairFirstOrderDerivative (r := r) E g.form h φ a) (alternatingPairFirstOrderValue (r := r) E g.form h φ a) (F m)
  have hsP (m : ℕ) (row : Fin n × Fin r) : tsupport (fun z => P m z row) ⊆ K :=
    complexFirstOrderSystemApply_tsupport_subset realVec _ _ (F m) hK.isClosed (hsF m) row
  have hval (m : ℕ) (z : ComplexVector n) (row : Fin n × Fin r) :
      oneWeightedDualInverse (r := r) E g.form h φ a (P m) z row.1 row.2 =
        pairOneOutputModel (r := r) E g.form h φ a (F m) z row.1 row.2 :=
    (pairOneOutputModel_eq_inverse E g h hh φ hφ a (F m) (hF m) K hK hKO (hsF m) z row.1 row.2).symm
  have hlim (row : Fin n × Fin r) := oneWeightedDualInverse_l2_errors E g h hh φ hφ a K hK hKO P v hsP hsv he ht row
  apply weightedOneChartSection_cauchySeq_of_model_errors E g μ hμ h hh φ hφ hE a K hK hKO
    (fun m => pairOneOutputModel (r := r) E g.form h φ a (F m))
    (fun m => (pairOneOutputModel_properties E g h hh φ hφ a (F m) (hF m) K hK hKO (hsF m)).1)
    (fun m => (pairOneOutputModel_properties E g h hh φ hφ a (F m) (hF m) K hK hKO (hsF m)).2)
    (oneWeightedDualInverse (r := r) E g.form h φ a v)
  · intro m row
    simpa only [hval] using (hlim row).1 m
  · intro row
    simpa only [hval] using (hlim row).2

end Yau.LeafProofs.L14Aux
