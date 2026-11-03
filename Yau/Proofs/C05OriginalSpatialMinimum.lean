import Yau.Proofs.C05OriginalIntrinsicHeatDecay
import Yau.Proofs.C05EventualSpatialMinimum

/-! The geometric near-minimum estimate is applied to the identical original
normalized metric and Harnack function, with a uniform radius chosen first. -/
noncomputable section
open Filter
open scoped Topology Manifold ContDiff ComplexOrder
namespace Yau.Proofs.C05Aux
open Yau Blueprint C04Aux C04RescaledTubeAux Yau.LeafProofs
variable {n : ℕ} {X : KahlerManifold n}
set_option backward.isDefEq.respectTransparency false

theorem original_sequence_laplacian_lower (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : FlowStage X o h U P ρ) (hH : HarnackCompleteness X o h)
    (tw : ℕ → ℝ) (htw : ∀ i, 0 < tw i)
    (hRi : ∀ i, 0 < scalarCurvature (h (tw i)) o) {r J : ℝ}
    (hr : 0 < r) (hJ : 0 ≤ J)
    (hdefect : Tendsto (fun i => scalarHarnackSum h o (tw i) /
      scalarCurvature (h (tw i)) o^2) atTop (𝓝 0))
    (hthird : ∀ᶠ i in atTop, ∀ x ∈ distBall (originalSequenceMetric o h tw hRi i) o r,
      scalarJetNorm (originalSequenceMetric o h tw hRi i)
        (intrinsicHarnackMinimum (originalSequenceMetric o h tw hRi i)
          (tw i*scalarCurvature (h (tw i)) o)⁻¹) 3 x ≤ J) :
    ∀ ε > 0, ∀ᶠ i in atTop, -ε ≤
      laplacian (originalSequenceMetric o h tw hRi i)
        (intrinsicHarnackMinimum (originalSequenceMetric o h tw hRi i)
          (tw i*scalarCurvature (h (tw i)) o)⁻¹) o := by
  let k := originalSequenceMetric o h tw hRi
  let κ := fun i => (tw i*scalarCurvature (h (tw i)) o)⁻¹
  let g := fun i => completeRescaledFlowMetric X o h U P ρ hf hH
    (scalarCurvature (h (tw i)) o) (hRi i) (tw i) (htw i)
  let f := fun i => intrinsicHarnackMinimum (k i) (κ i)
  have hk (i : ℕ) : MetricSmooth (k i) := L12Aux.metricSmooth_of_smoothMetric (g i)
  have hK (i : ℕ) : KahlerClosed (k i) := (g i).kahler_equations
  have hA (i : ℕ) (x : Pt X) : (ricci (k i) x).PosDef := by
    change (ricci (scaleField _ (hRi i) (h (tw i))) x).PosDef
    rw [ricci_scaleField]
    exact hH.2.2.1 (tw i) (htw i).le x
  have hs (i : ℕ) : SmoothFn (f i) := intrinsicHarnackMinimum_smoothFn
    (k i) (hk i) (hK i) (hA i) (κ i)
  have he (i : ℕ) (x : Pt X) : f i x = normalizedHarnackMinimum h (tw i)
      (scalarCurvature (h (tw i)) o) x 0 := by
    have H := normalizedHarnackMinimum_eq_intrinsic o h U P ρ hf.1 hH (tw i)
      (scalarCurvature (h (tw i)) o) (hRi i) x 0
      (by simpa only [zero_div,add_zero] using htw i)
    simpa only [f,k,κ,originalSequenceMetric,zero_div,add_zero] using H.symm
  have hn (i : ℕ) (x : Pt X) : 0 ≤ f i x := by
    rw [he]
    exact normalizedHarnackMinimum_nonneg o h hH _ _ x 0
      (by simpa only [zero_div,add_zero] using htw i)
  have hz : Tendsto (fun i => f i o) atTop (𝓝 0) := by
    apply squeeze_zero (fun i => hn i o) _ hdefect
    intro i
    rw [he]
    have H := normalizedHarnackMinimum_le o h hH (tw i)
      (scalarCurvature (h (tw i)) o) o 0
      (by simpa only [zero_div,add_zero] using htw i)
    simpa only [zero_div,add_zero] using H
  exact eventually_laplacian_lower_of_eventual_jet_bound o g f hs hr hJ hthird
    (fun i x _ => hn i x) hz

end Yau.Proofs.C05Aux
