import Yau.Proofs.P06HodgeRegularityHilbertJets
import Yau.Proofs.P06HodgeRegularityCoordinateJets

/-! Every compact chart component of every positive-time strong Hodge
path has an actual smooth representative in the original chart measure. -/
noncomputable section
open MeasureTheory Filter Module
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs Yau.LeafProofs.L03 Yau.LeafProofs.L16Aux

variable {n k : ℕ} {M : ComplexManifold n}

theorem hodgeStrongPath_cutoff_smooth_representative {α : Type} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (h : ℝ → L2FormHilbert g μ k)
    (hheat : ∀ t, 0 < t → ∃ w, HasDerivAt h w t ∧
      (h t,(-2 : ℝ) • w) ∈ (hodgeCoreOperator g μ hμ k).closure.graph)
    {t : ℝ} (ht : 0 < t)
    (A : RealForm M k) (hA : L2RealForm g.form μ A) (hAt : realizeActualForm g μ A hA = h t)
    (x : M.Carrier) (b : Basis α ℝ (HodgeJets.Fiber n k))
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ chartTarget x) (c : α) :
    ∃ f : ComplexVector n → ℝ, ContDiff ℝ ∞ f ∧
      f =ᵐ[lebesgueC n] (fun z => χ z * hodgeRegularityCoord b A x z c) := by
  have hfinite (N : ℕ) : ∃ J : List (Fin (Fintype.card (RIdx n))) →
        (Fin (Fintype.card (RIdx n)) → ℝ) → ℝ,
      FiniteCoordinateWeakJet N
        (fun y => χ ((hodgeRegularityFinEquiv n).symm y) *
          hodgeRegularityCoord b A x ((hodgeRegularityFinEquiv n).symm y) c) J := by
    obtain ⟨J,hJ,hJK⟩ := hodgeStrongPath_cutoff_weakJet g μ hμ h hheat ht N A hA hAt x b χ hχ hcχ hχO
    exact ⟨_,hodgeRegularityFiniteCoordinateWeakJet N _ J hJ
      (fun w _ c => hcχ.of_isClosed_subset (isClosed_tsupport _) (hJK w c)) c⟩
  obtain ⟨v,hv,hAE⟩ := smooth_representative_of_finite_coordinate_weak_jets hfinite
  refine ⟨fun z => v (hodgeRegularityFinEquiv n z),hv.comp (hodgeRegularityFinEquiv n).contDiff,?_⟩
  have hh := (hodgeRegularityFinEquiv_measurePreserving n).quasiMeasurePreserving.ae hAE
  filter_upwards [hh] with z hz
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using hz

end Yau.NodeProofs.P06Aux
