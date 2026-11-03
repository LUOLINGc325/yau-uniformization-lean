import Yau.Proofs.P03WeakFormSubtraction
import Yau.Proofs.P03WeightedHolomorphicRepresentative
import Yau.Proofs.P03SingularNormBounds

open scoped Manifold Topology ContDiff ENNReal
open Set Filter MeasureTheory

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar Yau.LeafProofs.L14Aux

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (Bundle.TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem singularTopIntegrand_congr_ae (g : HermitianField M) (h : Metric (M := M) E)
    (μ : Measure M.Carrier) (φ : ℕ → M.Carrier → ℝ) (u v : NQForm E 0)
    (heq : ∀ᵐ x ∂μ, u x = v x) :
    (fun x => singularTopIntegrand (r := r) E g h φ u x) =ᵐ[μ]
      (fun x => singularTopIntegrand (r := r) E g h φ v x) := by
  filter_upwards [heq] with x hx
  change (⨆ j, ENNReal.ofReal (BundleDbar.formNormSq (r := r) E g h u x * Real.exp (-φ j x))) =
    (⨆ j, ENNReal.ofReal (BundleDbar.formNormSq (r := r) E g h v x * Real.exp (-φ j x)))
  apply iSup_congr
  intro j
  exact congrArg ENNReal.ofReal (congrArg (fun t : ℝ => t * Real.exp (-φ j x))
    (formNormSq_congr_at E g h u v x hx))

/-- The weak correction produces one global holomorphic interpolant.
Its complementary correction is equal to the one Hilbert solution almost
everywhere and hence preserves all original weighted norms at once. -/
theorem exists_holomorphic_complement (g : Yau.SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (hE : Holomorphic (r := r) E) (s u : NQForm E 0) (f : NQForm E 1)
    (hs : WeakDbar (r := r) E s f) (hu : WeakDbar (r := r) E u f) :
    ∃ w : NQForm E 0, HolomorphicTopForm (r := r) E w ∧
      (∀ᵐ x ∂μ, subForm E s w x = u x) ∧
      LocallyL2 (r := r) E (subForm E s w) ∧
      ∀ (h : Metric (M := M) E) (φ : M.Carrier → ℝ),
        weightedNormSq (r := r) E g.form h μ φ (subForm E s w) =
          weightedNormSq (r := r) E g.form h μ φ u := by
  obtain ⟨w, hw, heq⟩ := weakDbar_zero_holomorphic_top_representative E g μ hμ hE
    (subForm E s u) (weakDbar_subForm_same_source E s u f hs hu)
  have hv : ∀ᵐ x ∂μ, subForm E s w x = u x := by
    filter_upwards [heq] with x hx
    have he : subForm E s w x = subForm E s (subForm E s u) x := by
      simp only [subForm, hx]
    exact he.trans (congrFun (subForm_subForm_cancel E s u) x)
  refine ⟨w, hw, hv, ?_, fun h φ => weightedNormSq_congr_ae E g.form h μ φ _ u hv⟩
  exact locallyL2_of_ae_eq E g μ hμ u (subForm E s w) hu.1 (hv.mono fun _ hx => hx.symm)

end Yau.NodeProofs.P03Aux
