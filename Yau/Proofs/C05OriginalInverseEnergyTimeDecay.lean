import Yau.Proofs.C05IntrinsicInverseEnergyTimeLimit
import Yau.Proofs.C05NormalizedInverseEnergyDerivative
import Yau.Proofs.C05RicciPinchingCoercivity
import Yau.Proofs.C05ScalarTimeSourceBoundsJets

/-! On the original good sequence, the genuine normalized quadratic time
derivative tends to zero. The finite jet hypotheses are supplied by C04's
original intrinsic tubes. -/
noncomputable section
open Filter
open scoped Topology Manifold ContDiff Matrix ComplexOrder
namespace Yau.Proofs.C05Aux
open Yau Blueprint C04Aux C04RescaledTubeAux Yau.LeafProofs
open Yau.Proofs.C05NormalizedScalarTimeEvolutionAux Yau.Proofs.C05ScalarTimeSourceBoundsAux
variable {n : ℕ} {X : KahlerManifold n}
set_option backward.isDefEq.respectTransparency false

def originalSequenceMetric (o : Pt X) (h : Flow X) (tw : ℕ → ℝ)
    (hRi : ∀ i, 0 < scalarCurvature (h (tw i)) o) (i : ℕ) : HermitianField X.manifold :=
  scaleField (scalarCurvature (h (tw i)) o) (hRi i) (h (tw i))

theorem original_sequence_inverseEnergyTime_decay (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (hH : HarnackCompleteness X o h)
    (tw : ℕ → ℝ) (htw : ∀ i, 0 < tw i)
    (hRi : ∀ i, 0 < scalarCurvature (h (tw i)) o) {lam B : ℝ}
    (hlam : 0 < lam) (hB : 0 ≤ B)
    (hpin : ∀ i, lam ≤ relMinEigenvalue (gMat (originalSequenceMetric o h tw hRi i) o)
      (ricci (originalSequenceMetric o h tw hRi i) o))
    (hdefect : Tendsto (fun i => scalarHarnackSum h o (tw i) /
      scalarCurvature (h (tw i)) o^2) atTop (𝓝 0))
    (hjet : ∀ᶠ i in atTop,
      (∀ j ≤ 6, scalarJetNorm (originalSequenceMetric o h tw hRi i)
        (scalarCurvature (originalSequenceMetric o h tw hRi i)) j o ≤ B) ∧
      (∀ j ≤ 4, realRicciJetNorm (originalSequenceMetric o h tw hRi i) j o ≤ B)) :
    Tendsto (fun i => intrinsicInverseEnergyTime (originalSequenceMetric o h tw hRi i) o) atTop (𝓝 0) ∧
    Tendsto (fun i => deriv (fun z =>
      realRicciDifferentialEnergy (normalizedMetric h (tw i) (scalarCurvature (h (tw i)) o) (hRi i) z)
        (scalarCurvature (normalizedMetric h (tw i) (scalarCurvature (h (tw i)) o) (hRi i) z)) o) 0)
      atTop (𝓝 0) := by
  let k := originalSequenceMetric o h tw hRi
  have hk (i : ℕ) : MetricSmooth (k i) := metricSmooth_scale _ (hRi i) (h (tw i))
    (L23Aux.metricFamilySmooth_slice h hf.1.2.1 (htw i).le)
  have hK (i : ℕ) : KahlerClosed (k i) := kahlerClosed_scale _ (hRi i) (h (tw i))
    (L23Aux.metricFamilySmooth_slice h hf.1.2.1 (htw i).le) (hf.1.2.2.1 (tw i) (htw i).le)
  have hA (i : ℕ) (x : Pt X) : (ricci (k i) x).PosDef := by
    change (ricci (scaleField _ (hRi i) (h (tw i))) x).PosDef
    rw [ricci_scaleField]
    exact hH.2.2.1 (tw i) (htw i).le x
  have hC : ∀ᶠ i in atTop, metricTensorNorm (realMetricFn (k i) o (chartPt o o))
      (ricciInverseTensor (k i) o (chartPt o o)) ≤ Real.sqrt (2*n:ℕ)/lam :=
    Eventually.of_forall fun i => ricciInverseTensor_norm_le_of_relative_pinching
      (k i) (hk i) (hK i) o (hA i o) hlam (hpin i)
  have h2 : ∀ᶠ i in atTop, scalarJetNorm (k i) (scalarCurvature (k i)) 2 o ≤ B :=
    hjet.mono (fun i hi => hi.1 2 (by norm_num))
  have h1 : ∀ᶠ i in atTop, scalarJetNorm (k i) (scalarHarnackSource (k i) 0) 1 o ≤ b1 n B :=
    hjet.mono (fun i hi => source1_jet_bound (k i) (hk i) (hK i) 1 (by norm_num) o hB hi.1 hi.2)
  have hgrad : Tendsto (fun i => scalarJetNorm (k i) (scalarCurvature (k i)) 1 o) atTop (𝓝 0) :=
    normalized_center_gradient_tendsto_zero o h U P ρ hf hH tw htw hRi hdefect
  have htime := intrinsicInverseEnergyTime_tendsto_zero k hk hK o atTop
    (by positivity : (0:ℝ)≤Real.sqrt (2*n:ℕ)/lam) hB (b1_nonneg n hB) hC h2 h1 hgrad
  refine ⟨htime,htime.congr' (Eventually.of_forall fun i => ?_)⟩
  have hd := normalized_inverseEnergy_hasDerivAt o h U P ρ hf hH (tw i)
    (scalarCurvature (h (tw i)) o) (hRi i) o 0 (by simpa only [zero_div,add_zero] using htw i)
  simpa only [normalizedMetric,zero_div,add_zero,k,originalSequenceMetric] using hd.deriv.symm

end Yau.Proofs.C05Aux
