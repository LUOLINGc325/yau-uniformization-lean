import Yau.Proofs.F05SmoothTimeJets
import Yau.Proofs.F05FlowBarriers

/-! The supplied localized flow itself makes its actual scalar curvature
smooth up to the initial face, by the literal rho time-derivative identity. -/

open Set
open scoped ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.Blueprint
variable {n : ℕ} {X : KahlerManifold n}

theorem F05_flow_scalar_smooth (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) {S : ℝ} (hS : 0 < S) :
    SmoothSpaceTime (fun x t => scalarCurvature (h t) x) (Icc 0 S) := by
  intro x
  have hρ : ContDiffOn ℝ ∞ (fun q : ComplexVector n × ℝ => ρ (chartInv x q.1) q.2)
      (chartTarget x ×ˢ Icc 0 S) :=
    (hloc.2.2.2.1 x).mono (fun q hq => ⟨hq.1,hq.2.1⟩)
  have hTime := F05_joint_time_derivative_smooth (uniqueDiffOn_Icc hS) hρ
  apply hTime.congr
  intro q hq
  exact (Yau.F04Proof.rho_derivWithin_Icc o h U P ρ hloc S hS (chartInv x q.1) q.2 hq.2).symm

end Yau.Proofs.F05Aux
