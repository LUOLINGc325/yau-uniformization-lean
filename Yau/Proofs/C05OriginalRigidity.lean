import Yau.Proofs.C05OriginalRigidityData
import Yau.Proofs.C05OriginalContraction
import Yau.Proofs.C05SpatialHarnackBudget
import Yau.Proofs.C05IntrinsicRigiditySequenceTail

/-! The original flow hypotheses alone imply simple connectivity, by the
actual temporal and spatial near-minimum estimates on the same good sequence. -/
noncomputable section
open Filter
open scoped Topology Manifold ContDiff Matrix ComplexOrder
namespace Yau.Proofs.C05Aux
open Yau Blueprint C04Aux C04RescaledTubeAux Yau.LeafProofs
open Yau.Proofs.C05SpatialHarnackBudgetAux
open Yau.Proofs.C05IntrinsicRigiditySequenceAux Yau.Proofs.C05HarnackFrameIdentitiesAux
open Yau.Proofs.C05GradientFlowAux
variable {n : ℕ} {X : KahlerManifold n}
set_option backward.isDefEq.respectTransparency false

theorem simplyConnected_of_original_flow (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : FlowStage X o h U P ρ) (hH : HarnackCompleteness X o h)
    (hW : RicciWindows X o h ρ) : SimplyConnectedSpace (Pt X) := by
  obtain ⟨tw,htw,htwinf,hRi,lam,hlam,b,hb,B,hB,K,hKcap,
    hnorm,hdefect,hZt,hE,hκnonneg,hκbound,hstatic⟩ :=
    original_good_sequence_with_rigidity_data o h U P ρ hf hH hW
  let k := originalSequenceMetric o h tw hRi
  let κ := fun i => (tw i*scalarCurvature (h (tw i)) o)⁻¹
  let g := fun i => completeRescaledFlowMetric X o h U P ρ hf hH
    (scalarCurvature (h (tw i)) o) (hRi i) (tw i) (htw i)
  have hk (i : ℕ) : MetricSmooth (k i) := L12Aux.metricSmooth_of_smoothMetric (g i)
  have hK (i : ℕ) : KahlerClosed (k i) := (g i).kahler_equations
  have hA (i : ℕ) (x : Pt X) : (ricci (k i) x).PosDef := by
    change (ricci (scaleField _ (hRi i) (h (tw i))) x).PosDef
    rw [ricci_scaleField]
    exact hH.2.2.1 (tw i) (htw i).le x
  obtain ⟨r,hr,hrb,J,hJ,hbudget⟩ := exists_spatial_harnack_jet_budget
    n lam B b K hlam hB.le hb hKcap.le
  have hthird : ∀ᶠ i in atTop, ∀ x ∈ distBall (k i) o r,
      scalarJetNorm (k i) (intrinsicHarnackMinimum (k i) (κ i)) 3 x ≤ J := by
    filter_upwards [hstatic,hκbound] with i hi hci
    apply hbudget X.manifold (g i) o (κ i) (hA i) (hnorm i).2
      (by simpa only [κ,abs_of_nonneg (hκnonneg i)] using hci)
    intro x hx
    exact ⟨fun j hj => (hi x hx).1 j (by omega),fun j hj => (hi x hx).2 j (by omega)⟩
  have hlap := original_sequence_laplacian_lower o h U P ρ hf hH tw htw hRi
    hr hJ.le hdefect hthird
  have htime := original_sequence_intrinsic_time_decay o h U P ρ hf.1 hH tw htw hRi hZt
  have hL := intrinsic_heat_upper_of_time_decay_and_laplacian_lower k κ o htime hlap
  have hPSD (i : ℕ) : (sliceHarnackMatrix (k i) (κ i) o).PosSemidef :=
    sliceHarnackMatrix_flow_posSemidef o h U P ρ hf.1 hH (tw i)
      (scalarCurvature (h (tw i)) o) (htw i) (hRi i) o
  have hS : Tendsto (fun i => scalarHarnackSource (k i) (κ i) o) atTop (𝓝 0) := by
    apply hdefect.congr'
    exact Eventually.of_forall fun i => by
      have H := normalizedScalarHarnackSum_eq_source o h U P ρ hf.1 (tw i)
        (scalarCurvature (h (tw i)) o) (hRi i) o 0
        (by simpa only [zero_div,add_zero] using htw i)
      simpa only [zero_div,add_zero,k,κ,originalSequenceMetric] using H
  have hcenter := eventually_intrinsic_realHess_negative_of_eventually_clock_le
    k hk hK hA o lam K hlam hKcap.le κ hκnonneg hκbound
    (fun i => (hnorm i).1) (fun i => (hnorm i).2) hPSD hS hE hL
  apply simplyConnected_of_original_center_negativity o h U P ρ hf hH tw htw htwinf hRi
    (a := lam^2/4) (by positivity) hb hB.le hdefect
    (hstatic.mono (fun i hi x hx => (hi x hx).1 3 (by norm_num)))
  filter_upwards [hcenter] with i hi
  intro w
  convert hi w using 1 <;> ring

end Yau.Proofs.C05Aux
