import Yau.Proofs.F04SupportedSmoothProfile
import Yau.Proofs.F04InjectiveDerivativeLift
import Yau.Proofs.F04FiniteLpCurve

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint Yau.Proofs.F03Aux Yau.HeatConcreteBindings

variable {n : ℕ} {M : ComplexManifold n}

local instance (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) :
    CompleteSpace (DirichletEnergy g μ hμ O) := dirichletEnergy_completeSpace g μ hμ O

/-- A jointly smooth supported profile and its genuine time derivative
 define a C1 curve in the actual supported energy space, including both
 closed-time faces. The derivative is the actual supported derivative profile. -/
theorem supportedProfileCore_contDiffOn_one
    (g : SmoothMetric M) (hg : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O K : Set M.Carrier)
    (hO : MeasurableSet O) (hK : IsCompact K) (hOK : O ⊆ K) {S : ℝ} (hS : 0 < S)
    (v w : M.Carrier → ℝ → ℝ) (hv : SmoothSpaceTime v (Icc 0 S)) (hw : SmoothSpaceTime w (Icc 0 S))
    (hcv : ∀ t ∈ Icc 0 S, HasCompactSupport (v · t)) (hSv : ∀ t ∈ Icc 0 S, tsupport (v · t) ⊆ O)
    (hcw : ∀ t ∈ Icc 0 S, HasCompactSupport (w · t)) (hSw : ∀ t ∈ Icc 0 S, tsupport (w · t) ⊆ O)
    (hDeriv : ∀ x t, t ∈ Icc 0 S → HasDerivWithinAt (v x) (w x t) (Icc 0 S) t) :
    let V := fun t => dirichletCoreToEnergy g μ hμ O (supportedProfileCore g μ hμ O hS v hv hcv hSv t)
    let W := fun t => dirichletCoreToEnergy g μ hμ O (supportedProfileCore g μ hμ O hS w hw hcw hSw t)
    ContDiffOn ℝ 1 V (Icc 0 S) ∧ ∀ t ∈ Icc 0 S, HasDerivWithinAt V (W t) (Icc 0 S) t := by
  let := Yau.LeafProofs.L18Aux.riemannianVolume_locallyFinite g μ hμ
  let : IsFiniteMeasure (μ.restrict O) := ⟨by
    simpa only [Measure.restrict_apply_univ] using
      (lt_of_le_of_lt (measure_mono hOK) hK.measure_lt_top)⟩
  let V := fun t => dirichletCoreToEnergy g μ hμ O (supportedProfileCore g μ hμ O hS v hv hcv hSv t)
  let W := fun t => dirichletCoreToEnergy g μ hμ O (supportedProfileCore g μ hμ O hS w hw hcw hSw t)
  let j := dirichletL2 g μ hμ O
  obtain ⟨hf, hfc⟩ := compact_scalar_profile_L2 g μ hμ O K hO hK hOK hS.le v (smoothSpaceTime_continuousOn hv)
  obtain ⟨hd, _hdc⟩ := compact_scalar_profile_L2 g μ hμ O K hO hK hOK hS.le w (smoothSpaceTime_continuousOn hw)
  have hJv (t : ℝ) : j (V t) = (hf t).toLp (fun x => v x (timeClamp S hS.le t)) :=
    supportedProfileCore_L2 g μ hμ O hS v hv hcv hSv hf t
  have hJw (t : ℝ) : j (W t) = (hd t).toLp (fun x => w x (timeClamp S hS.le t)) :=
    supportedProfileCore_L2 g μ hμ O hS w hw hcw hSw hd t
  have hWC : Continuous W := continuous_supportedProfileCore g μ hμ O K hO hK hOK hS w hw hcw hSw
  have hJVC : Continuous (fun t => j (V t)) := hfc.congr (fun t => (hJv t).symm)
  obtain ⟨C, hC, hCb⟩ := compact_scalar_profile_bound hS.le w (smoothSpaceTime_continuousOn hw) K hK
  have hdPoint : ∀ᵐ x ∂μ.restrict O, ∀ t ∈ Icc 0 S,
      HasDerivWithinAt (fun s => v x (timeClamp S hS.le s))
        (w x (timeClamp S hS.le t)) (Icc 0 S) t := by
    apply ae_of_all
    intro x t ht
    have he : EqOn (fun s => v x (timeClamp S hS.le s)) (v x) (Icc 0 S) :=
      fun s hs => congrArg (v x) (timeClamp_eq_of_mem S hS.le hs)
    simpa only [timeClamp_eq_of_mem S hS.le ht] using (hDeriv x t ht).congr_of_mem he ht
  have hdBound : ∀ᵐ x ∂μ.restrict O, ∀ t ∈ Icc 0 S, ‖w x (timeClamp S hS.le t)‖ ≤ C := by
    filter_upwards [ae_restrict_mem hO] with x hx
    exact fun t _ => hCb x (hOK hx) t
  have hJVd (t : ℝ) (ht : t ∈ Icc 0 S) : HasDerivWithinAt (fun s => j (V s)) (j (W t)) (Icc 0 S) t := by
    have hScalar := finiteLpCurve_hasDerivWithinAt (μ.restrict O)
      (fun t x => v x (timeClamp S hS.le t)) (fun t x => w x (timeClamp S hS.le t))
      hf hd hS C hC hdPoint hdBound t ht
    rw [← hJw t] at hScalar
    exact hScalar.congr_of_mem (fun s _ => hJv s) ht
  exact injective_derivative_lift_on_closed_interval j (dirichletL2_injective g hg μ hμ O hO)
    hS V W hWC hJVC.continuousOn hJVd

end Yau.F04Proof
