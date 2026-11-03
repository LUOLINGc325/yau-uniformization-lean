import Yau.LeafProofs.L14BundleFriedrichs

noncomputable section
open scoped Manifold Topology ContDiff
open MeasureTheory Bundle Filter Module

namespace Yau.LeafProofs.L14Aux
open BundleDbar

def unflattenOneModel {n r : ℕ} (V : ComplexVector n → (Fin n × Fin r) → ℂ) :
    ComplexVector n → Fin n → ComplexVector r := fun z i => WithLp.toLp 2 (fun α => V z (i, α))

theorem unflattenOneModel_contDiff {n r : ℕ} (V : ComplexVector n → (Fin n × Fin r) → ℂ)
    (hV : ∀ c, ContDiff ℝ ∞ (fun z => V z c)) : ContDiff ℝ ∞ (unflattenOneModel V) :=
  contDiff_pi.mpr (fun i => (contDiff_piLp 2).mpr (fun α => hV (i, α)))

theorem unflattenOneModel_tsupport_subset {n r : ℕ}
    (V : ComplexVector n → (Fin n × Fin r) → ℂ) {K : Set (ComplexVector n)}
    (hK : IsClosed K) (hV : ∀ c, tsupport (fun z => V z c) ⊆ K) :
    tsupport (unflattenOneModel V) ⊆ K := by
  apply closure_minimal _ hK
  intro z hz
  by_contra hn
  apply hz
  funext i
  apply PiLp.ext
  intro α
  exact image_eq_zero_of_notMem_tsupport (f := fun w => V w (i, α))
    (fun hs => hn (hV (i, α) hs))

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

def bundleModelSystemOutput (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r)
    (z : ComplexVector n) (row : BundleSystemRow n r) : ℂ := match row with
  | .inl α => (∑ β, BundleDbar.metricMatrix (r := r) E h a z α β *
      chartDbarAdjoint (r := r) E g h φ a F z β) * (Real.exp (-φ (chartInv a z)) : ℂ)
  | .inr k => modelOneDbar F z k.1.1 k.1.2 k.2

theorem bundleModelSystemOutput_tsupport_subset (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r)
    (row : BundleSystemRow n r) : tsupport (fun z => bundleModelSystemOutput E g h φ a F z row) ⊆ tsupport F := by
  apply closure_minimal _ (isClosed_tsupport F)
  intro z hz
  by_contra hn
  apply hz
  cases row with
  | inl α =>
    have hd : chartDbarAdjoint (r := r) E g h φ a F z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hs => hn (tsupport_chartDbarAdjoint_subset E g h φ a F hs))
    simp only [bundleModelSystemOutput, hd, PiLp.zero_apply, mul_zero, Finset.sum_const_zero, zero_mul]
  | inr k =>
    have hd : modelOneDbar F z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hs => hn (tsupport_modelOneDbar_subset F hs))
    change modelOneDbar F z k.1.1 k.1.2 k.2 = 0
    rw [hd]
    rfl

theorem bundleFirstOrder_apply_global (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r) (hF : ContDiff ℝ ∞ F)
    (hsF : tsupport F ⊆ localDomain (r := r) E a) (z : ComplexVector n) (row : BundleSystemRow n r) :
    complexFirstOrderSystemApply realVec (bundleFirstOrderDerivative (r := r) E g.form h φ a)
      (bundleFirstOrderValue (r := r) E g.form h φ a) (fun w c => F w c.1 c.2) z row =
      bundleModelSystemOutput E g.form h φ a F z row := by
  by_cases hz : z ∈ localDomain (r := r) E a
  · exact bundleFirstOrder_apply E g h hh φ hφ a F hF z hz row
  · have hn : z ∉ tsupport F := fun hs => hz (hsF hs)
    have hzero : F z = 0 := image_eq_zero_of_notMem_tsupport hn
    have hd (c : Fin n × Fin r) : fderiv ℝ (fun w => F w c.1 c.2) z = 0 :=
      fderiv_of_notMem_tsupport (𝕜 := ℝ) (fun hs => hn
        (tsupport_comp_subset (g := fun V : Fin n → ComplexVector r => V c.1 c.2) (by rfl) F hs))
    have hout : bundleModelSystemOutput E g.form h φ a F z row = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun w => bundleModelSystemOutput E g.form h φ a F w row)
        (fun hs => hn (bundleModelSystemOutput_tsupport_subset E g.form h φ a F row hs))
    simp only [complexFirstOrderSystemApply, hd, hzero, hout, Pi.zero_apply, PiLp.zero_apply,
      ContinuousLinearMap.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]

variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
  (hE : Holomorphic (r := r) E)

include hE in
/-- The Friedrichs approximants are actual smooth bundle coefficient arrays,
and their computed weighted adjoints and exterior derivatives converge jointly. -/
theorem exists_localized_bundle_model_graph_approx
    (U : WeightedOneSection E g μ hμ h hh φ hφ)
    (S : WeightedTopSection E g μ hμ h hh φ hφ)
    (hUS : (realizeWeightedOneSection E g μ hμ h hh φ hφ U,
      realizeWeightedTopSection E g μ hμ h hh φ hφ S) ∈
      (weightedMaximalDbar E g μ hμ h hh φ hφ).adjoint.graph)
    (f : NQForm E 2) (huf : WeakDbar (r := r) E U.1 f)
    (a : M.Carrier) (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ localDomain (r := r) E a) :
    ∃ (L : Set (ComplexVector n)) (F : ℕ → ComplexVector n → Fin n → ComplexVector r),
      IsCompact L ∧ L ⊆ localDomain (r := r) E a ∧
      (∀ j, ContDiff ℝ ∞ (F j) ∧ tsupport (F j) ⊆ L) ∧
      (∀ c : Fin n × Fin r, (∀ j, MemLp (fun z => F j z c.1 c.2 - localizedBundleSystemInput (r := r) E U.1 a χ z c)
        2 (lebesgueC n)) ∧
        Tendsto (fun j => ∫ z, ‖F j z c.1 c.2 - localizedBundleSystemInput (r := r) E U.1 a χ z c‖ ^ 2
          ∂lebesgueC n) atTop (𝓝 0)) ∧
      ∀ row, (∀ j, MemLp (fun z => bundleModelSystemOutput E g.form h φ a (F j) z row -
        localizedBundleSystemOutput (r := r) E g.form h φ U.1 S.1 f a χ z row) 2 (lebesgueC n)) ∧
        Tendsto (fun j => ∫ z, ‖bundleModelSystemOutput E g.form h φ a (F j) z row -
          localizedBundleSystemOutput (r := r) E g.form h φ U.1 S.1 f a χ z row‖ ^ 2 ∂lebesgueC n)
          atTop (𝓝 0) := by
  obtain ⟨L, V, hcL, hLO, hV, htV, htP⟩ :=
    exists_localized_bundle_graph_approx E g μ hμ h hh φ hφ hE U S hUS f huf a χ hχ hcχ hsχ
  let F := fun j => unflattenOneModel (V j)
  have hF (j : ℕ) : ContDiff ℝ ∞ (F j) ∧ tsupport (F j) ⊆ L :=
    ⟨unflattenOneModel_contDiff (V j) (fun c => (hV j c).1),
      unflattenOneModel_tsupport_subset (V j) hcL.isClosed (fun c => (hV j c).2)⟩
  refine ⟨L, F, hcL, hLO, hF, htV, ?_⟩
  intro row
  have he (j : ℕ) (z : ComplexVector n) :
      bundleModelSystemOutput E g.form h φ a (F j) z row =
        complexFirstOrderSystemApply realVec (bundleFirstOrderDerivative (r := r) E g.form h φ a)
          (bundleFirstOrderValue (r := r) E g.form h φ a) (V j) z row :=
    (bundleFirstOrder_apply_global E g h hh φ hφ a (F j) (hF j).1 ((hF j).2.trans hLO) z row).symm
  simpa only [he] using htP row

end Yau.LeafProofs.L14Aux
