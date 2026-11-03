import Yau.Proofs.C05OriginalTimeDecayData
import Yau.Proofs.C05InverseRicciJetUniformBudget
import Yau.Proofs.C05IntrinsicHarnackHeat

/-! The actual intrinsic heat remainder vanishes on the original sequence.
All inverse bounds are computed from its original central Ricci pinching. -/
noncomputable section
open Filter
open scoped Topology Manifold ContDiff Matrix ComplexOrder
namespace Yau.Proofs.C05Aux
open Yau Blueprint C04Aux C04RescaledTubeAux Yau.LeafProofs
open Yau.Proofs.C05InverseRicciJetUniformBudgetAux
open Yau.Proofs.C05ScalarTimeSourceBoundsAux
open Yau.Proofs.C05NormalizedScalarTimeEvolutionAux
variable {n : ℕ} {X : KahlerManifold n}
set_option backward.isDefEq.respectTransparency false

theorem original_sequence_heatRemainder_tendsto_zero (o : Pt X) (h : Flow X) (U P ρ : STF X)
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
    Tendsto (fun i => intrinsicInverseEnergyHeatRemainder (originalSequenceMetric o h tw hRi i) o)
      atTop (𝓝 0) := by
  let k := originalSequenceMetric o h tw hRi
  have hk (i : ℕ) : MetricSmooth (k i) := metricSmooth_scale _ (hRi i) (h (tw i))
    (L23Aux.metricFamilySmooth_slice h hf.1.2.1 (htw i).le)
  have hK (i : ℕ) : KahlerClosed (k i) := kahlerClosed_scale _ (hRi i) (h (tw i))
    (L23Aux.metricFamilySmooth_slice h hf.1.2.1 (htw i).le) (hf.1.2.2.1 (tw i) (htw i).le)
  have hA (i : ℕ) (y : Pt X) : (ricci (k i) y).PosDef := by
    change (ricci (scaleField _ (hRi i) (h (tw i))) y).PosDef
    rw [ricci_scaleField]
    exact hH.2.2.1 (tw i) (htw i).le y
  obtain ⟨CA,hCA,hbudget⟩ := exists_uniform_inverseRicciJet_bound n lam B hlam hB
  have hC : ∀ᶠ i in atTop, ∀ j ≤ 2, ricciInverseJetNorm (k i) j o ≤ CA := by
    filter_upwards [hjet] with i hi
    have hiC := hbudget X.manifold (k i) (hk i) (hK i) (hA i) o
      (realRicci_coercive_of_relative_pinching (k i) (hk i) (hK i) o hlam (hpin i))
      (fun j hj => hi.2 j (by omega))
    intro j hj
    exact hiC j (by omega)
  have hB23 : ∀ᶠ i in atTop, scalarJetNorm (k i) (scalarCurvature (k i)) 2 o ≤ B ∧
      scalarJetNorm (k i) (scalarCurvature (k i)) 3 o ≤ B :=
    hjet.mono (fun i hi => ⟨hi.1 2 (by norm_num),hi.1 3 (by norm_num)⟩)
  have hQ : ∀ᶠ i in atTop, scalarJetNorm (k i) (scalarHarnackSource (k i) 0) 1 o ≤ b1 n B :=
    hjet.mono (fun i hi => source1_jet_bound (k i) (hk i) (hK i) 1 (by norm_num) o hB hi.1 hi.2)
  exact intrinsicInverseEnergyHeatRemainder_tendsto_zero k hk hK hA o atTop hCA.le hB
    (b1_nonneg n hB) hC hB23 hQ
    (normalized_center_gradient_tendsto_zero o h U P ρ hf hH tw htw hRi hdefect)

theorem original_sequence_intrinsic_time_decay (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (hH : HarnackCompleteness X o h)
    (tw : ℕ → ℝ) (htw : ∀ i, 0 < tw i)
    (hRi : ∀ i, 0 < scalarCurvature (h (tw i)) o)
    (hZt : Tendsto (fun i => deriv (originalHarnackMinimumProfile o h tw i) 0) atTop (𝓝 0)) :
    Tendsto (fun i => intrinsicScalarHarnackTime (originalSequenceMetric o h tw hRi i)
      (tw i*scalarCurvature (h (tw i)) o)⁻¹ o -
      intrinsicInverseEnergyTime (originalSequenceMetric o h tw hRi i) o) atTop (𝓝 0) := by
  apply hZt.congr'
  exact Eventually.of_forall fun i => by
    have hd := (normalized_minimum_hasDerivAt o h U P ρ hf hH (tw i)
      (scalarCurvature (h (tw i)) o) (hRi i) o 0
      (by simpa only [zero_div,add_zero] using htw i)).deriv
    change deriv (fun z => normalizedHarnackMinimum h (tw i)
      (scalarCurvature (h (tw i)) o) o z) 0 = _
    simpa only [originalSequenceMetric,normalizedMetric,zero_div,add_zero] using hd

end Yau.Proofs.C05Aux
