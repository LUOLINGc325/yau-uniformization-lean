import Yau.Proofs.C01FlowPathRicciBound
import Yau.Proofs.C01CutoffSupportEstimate
import Yau.Proofs.C01PathEnergySupport

/-! For an actual boundary minimizing path, a weighted index estimate
gives the required lower derivative bound for its genuine energy support. -/

noncomputable section
open MeasureTheory
open scoped Topology ContDiff Manifold

namespace Yau.NodeProofs.C01Aux
open Yau Yau.Blueprint Yau.LeafProofs.L12Aux
variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_pathSupport_index_estimate
    (hflow : LocalizedFlow X o h U P ρ) (hjoint : JointPositivity X h)
    (T B : ℝ) (hT : 0 ≤ T) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ a L : ℝ, 0 < a → a ≤ T → 0 < L →
      ∀ β : ℝ → Pt X,
      letI := manifold_realSmooth X.manifold
      ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 3 β →
      β 0 = o → β 1 ∈ initialDistanceSphere X.metric o L →
      (∀ u ∈ Set.Icc (0 : ℝ) 1,
        realTangentSpeedSq (h a) (β u) (realCurveVelocity β u) =
          exitDistanceProfile X.metric (h a) o L ^ 2) →
      (∀ κ : ℝ, 0 < κ → κ ≤ 1 / 2 →
        (∫ u in Set.Icc (0 : ℝ) 1, indexCutoff κ u ^ 2 *
          actualRealRicciQuadratic (h a) (β u) (realCurveVelocity β u)) ≤ B / κ) →
      ∃ (f : ℝ → ℝ) (D : ℝ),
        f a = exitDistanceProfile X.metric (h a) o L ∧
        (∀ t, 0 ≤ t → exitDistanceProfile X.metric (h t) o L ≤ f t) ∧
        HasDerivAt f D a ∧
        -(C / Real.sqrt a) * (1 + exitDistanceProfile X.metric (h a) o L) ≤ D := by
  obtain ⟨C, hC, hbound⟩ := localizedFlow_constant_path_Ricci_bound hflow hjoint T hT
  refine ⟨B + C + 1, by linarith, ?_⟩
  intro a L ha haT hL β
  letI := manifold_realSmooth X.manifold
  intro hβ hβ0 hβ1 hspeed hindex
  let d := exitDistanceProfile X.metric (h a) o L
  let R : ℝ → ℝ := fun u => actualRealRicciQuadratic (h a) (β u) (realCurveVelocity β u)
  have hd : 0 < d := exitDistanceProfile_pos X.metric (h a)
    (localizedFlow_metricSmooth_nonneg hflow a ha.le) o L hL
  have hpoint := (hbound a ha haT β d hd.le hβ0 hspeed hβ).1
  have hcont : ContinuousOn R (Set.Icc (0 : ℝ) 1) :=
    (localizedFlow_pathRicci_continuousOn hflow β Set.univ isOpen_univ a ha hβ.contMDiffOn).mono
      (Set.subset_univ _)
  have HI := cutoff_integral_support_estimate R hcont a d B C ha hd hB hC.le hpoint hindex
  obtain ⟨f, hfa, hupper, hf⟩ := localizedFlow_path_energy_upper_support hflow L a hL ha
    β hβ hβ0 hβ1 hspeed
  refine ⟨f, -(∫ u in Set.Icc (0 : ℝ) 1, R u) / (2 * d), hfa, hupper, hf, ?_⟩
  have H := neg_le_neg HI
  convert H using 1 <;> ring

end Yau.NodeProofs.C01Aux
