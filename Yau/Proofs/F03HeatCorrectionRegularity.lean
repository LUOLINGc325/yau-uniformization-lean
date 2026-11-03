import Yau.Proofs.F03KernelCenteredC1Time
import Yau.Proofs.F03CenteredCorrectionIdentity
import Yau.Proofs.F03HeatCorrectionSpatialSmooth

/-! Full original closed-slab joint C1 regularity of the same actual heat correction. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings HeatTargetCandidates
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem metricDefectHeatCorrection_smoothSpaceC1Time
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    {T : ℝ} (hT : 0 < T)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O) {L : ℝ} (hL : 0 < L) :
    SmoothSpaceC1Time (metricDefectHeatCorrection X h μ hμ O hO L) (Icc 0 T) := by
  refine ⟨fun s hs => metricDefectHeatCorrection_smooth X o h U P ρ hf μ hμ O hO L hs.1,?_⟩
  intro a
  have hTerminal : ContDiffOn ℝ 1 (fun p : ComplexVector n × ℝ =>
      metricDefectHeatCorrection X h μ hμ O hO L (chartInv a p.1) T) (chartTarget a ×ˢ Icc 0 T) :=
    (((metricDefectHeatCorrection_smooth X o h U P ρ hf μ hμ O hO L hT.le) a).comp
      contDiffOn_fst (fun p hp => hp.1)).of_le (by simp)
  have hHeat := dirichletMinimalKernel_centered_contDiffOn_one X o h U P ρ hf hT μ hμ O hO (sq_pos_of_pos hL) a
  have hW : ContDiffOn ℝ 1 (fun p : ComplexVector n × ℝ =>
      centeredFlowPotential X U T (chartInv a p.1) p.2) (chartTarget a ×ˢ Icc 0 T) :=
    (centeredFlowPotential_smooth X o h U P ρ hf hT a).of_le (by simp)
  have hRhs := ((((contDiffOn_snd.div_const T).mul hTerminal).add hHeat).sub hW)
  apply hRhs.congr
  intro p hp
  exact metricDefectHeatCorrection_centered_identity X o h U P ρ hf u hu hT hp.2 μ hμ O hO hL (chartInv a p.1)

end Yau.Proofs.F03Aux
