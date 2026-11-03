import Yau.Proofs.F03CenteredCorrectionIdentity
import Yau.Proofs.F03KernelPotentialTimeDerivative

/-! The original same-kernel correction has a genuine physical-time derivative on the closed slab. -/
noncomputable section
open MeasureTheory Set
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings HeatTargetCandidates
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def metricDefectHeatCorrectionTimeDerivative
    (X : KahlerManifold n) (h : Flow X) (U P : STF X)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O) (T L : ℝ) (x : Pt X) (s : ℝ) : ℝ :=
  metricDefectHeatCorrection X h μ hμ O hO L x T/T+
    (∫ y,dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO (L^2) x y*P y s ∂μ)-
    (∫ y,dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO (L^2) x y*U y T ∂μ)/T-
    P x s+U x T/T

theorem metricDefectHeatCorrection_hasDerivWithinAt
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    {T : ℝ} (hT : 0 < T)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O) {L : ℝ} (hL : 0 < L)
    (x : Pt X) {s : ℝ} (hs : s ∈ Icc 0 T) :
    HasDerivWithinAt (metricDefectHeatCorrection X h μ hμ O hO L x)
      (metricDefectHeatCorrectionTimeDerivative X h U P μ hμ O hO T L x s) (Icc 0 T) s := by
  have hLinear := (((hasDerivAt_id s).div_const T).mul_const
    (metricDefectHeatCorrection X h μ hμ O hO L x T)).hasDerivWithinAt (s := Icc 0 T)
  have hHeat := dirichletMinimalKernel_centered_hasDerivWithinAt X o h U P ρ hf hT.le μ hμ O hO
    (sq_pos_of_pos hL) x hs
  have hPotential := (centeredFlowPotential_hasDerivWithinAt X o h U P ρ hf T x hs.1).mono
    (show Icc (0:ℝ) T ⊆ Ici 0 from fun _ hr => hr.1)
  have hResult := ((hLinear.add hHeat).sub hPotential).congr_of_mem
    (fun r hr => metricDefectHeatCorrection_centered_identity X o h U P ρ hf u hu hT hr μ hμ O hO hL x) hs
  convert hResult using 1 <;> simp only [metricDefectHeatCorrectionTimeDerivative] <;> ring

end Yau.Proofs.F03Aux
