import Yau.Proofs.P06CylinderRegularityHilbertCauchy
import Yau.Proofs.P06CutoffTail

/-! The proved Tail theorem, applied to the actual smooth canonical
representatives, gives Cauchy convergence of all original joint jets. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.CylinderReg
open Yau Yau.Blueprint Yau.Parabolic Yau.LeafProofs.L03

theorem cutoff_actual_joint_jets_cauchy {n k : ℕ} (X : KahlerManifold n)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (o o' : Pt X) (χ χ' : ℕ → Pt X → ℝ)
    (hχ : MetricCutoffFamily X.metric.form o χ)
    (hχ' : MetricCutoffFamily X.metric.form o' χ')
    (A : RealForm X.manifold k) (hA : SmoothRealForm A)
    (B : ℝ) (hb : ∀ x, formNormSq X.metric.form A x ≤ B^2)
    (U V : ℕ → ℝ → RealForm X.manifold k)
    (hUs : ∀ j, 1 ≤ j → SmoothFormTime (U j) (Set.Ioi 0))
    (hVs : ∀ j, 1 ≤ j → SmoothFormTime (V j) (Set.Ioi 0))
    (hUPDE : ∀ j, 1 ≤ j → FormHeatEquation X.metric.form (U j))
    (hVPDE : ∀ j, 1 ≤ j → FormHeatEquation X.metric.form (V j))
    (hUL : ∀ j, 1 ≤ j → ∀ t, 0 < t → L2RealForm X.metric.form μ (U j t))
    (hVL : ∀ j, 1 ≤ j → ∀ t, 0 < t → L2RealForm X.metric.form μ (V j t))
    (hUR : ∀ j (hj : 1 ≤ j) t (ht : 0 < t),
      realizeActualForm X.metric μ (U j t) (hUL j hj t ht) =
      hodgeHeatHilbert X.metric μ hμ k t (CutoffTail.cutoffDatum X.metric μ hμ o χ hχ A hA j))
    (hVR : ∀ j (hj : 1 ≤ j) t (ht : 0 < t),
      realizeActualForm X.metric μ (V j t) (hVL j hj t ht) =
      hodgeHeatHilbert X.metric μ hμ k t (CutoffTail.cutoffDatum X.metric μ hμ o' χ' hχ' A hA j)) :
    ∀ x (K : Set (ComplexVector n)), IsCompact K → K ⊆ chartTarget x →
    ∀ eps T, 0 < eps → eps < T → ∀ (m : ℕ) (I : Fin k → RIdx n) η, 0 < η →
    ∃ N : ℕ, 1 ≤ N ∧ ∀ j l, N ≤ j → N ≤ l → ∀ z ∈ K, ∀ t ∈ Set.Icc eps T,
      ‖iteratedFDeriv ℝ m (fun p : Point n =>
        formComponents (U j p.2) x p.1 I-formComponents (V l p.2) x p.1 I) (z,t)‖ < η := by
  apply localized_Hilbert_Cauchy_form_jets X.metric μ hμ U V hUs hVs hUPDE hVPDE hUL hVL
  intro F hF T hT η hη
  obtain ⟨N,hNpos,hN⟩ := CutoffTail.localizedCauchy X μ hμ o o' χ χ' hχ hχ' A hA B hb F hF T hT η hη
  refine ⟨N,hNpos,?_⟩
  intro j l hj hl hjN hlN t ht htT
  rw [hUR j hj t ht,hVR l hl t ht]
  exact hN j l hjN hlN t ht htT

end Yau.NodeProofs.P06Aux.CylinderReg
