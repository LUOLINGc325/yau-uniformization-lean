import Yau.Proofs.P06ScalarSmoothHeatCutoffs
import Yau.Proofs.P06TraceHilbertScalarHeat
import Yau.Proofs.P06CompactInitial

/-! The actual L19 compact scalar flow is the original degree-zero
Hodge heat at the same time, with its original geometric initial datum. -/
noncomputable section
open MeasureTheory Filter Module
open scoped Topology ContDiff InnerProductSpace

namespace Yau.NodeProofs.P06Aux.ScalarSmooth
open Yau Yau.LeafProofs Yau.LeafProofs.L03 L19Aux L12Aux G04Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem scalarForm_compact (f : M.Carrier → ℝ) (hf : HasCompactSupport f) :
    CompactlySupportedRealForm (scalarForm f) := by
  apply hf.of_isClosed_subset isClosed_closure
  apply closure_mono
  intro x hx hfx
  apply hx
  ext V
  exact hfx

theorem compactHeat_scalar_l2 (g : SmoothMetric M) (hk : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (f : ScalarEnergyDomain g μ hμ) (t : ℝ) (ht : 0 < t) :
    L2RealForm g.form μ (scalarForm (compactHeat g hk μ hμ f t)) := by
  have hAE : ∀ᵐ x ∂μ, scalarForm (scalarHeatFamily g μ hμ t (scalarEnergyDomainL2 g μ hμ f)) x =
      scalarForm (compactHeat g hk μ hμ f t) x := by
    rw [compactHeat_pos g hk μ hμ f ht]
    filter_upwards [scalarClassicalHeat_ae (complexDimension_pos M) g hk μ hμ
      (scalarEnergyDomainL2 g μ hμ f) ht] with x hx
    ext V
    exact hx.symm
  exact l2RealForm_of_ae_eq g.form hAE (TraceHilbert.scalar_l2 g μ _)

theorem compactHeat_realizes (g : SmoothMetric M) (hk : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (f : ScalarEnergyDomain g μ hμ) (t : ℝ) (ht : 0 < t) :
    realizeActualForm g μ (scalarForm (compactHeat g hk μ hμ f t))
      (compactHeat_scalar_l2 g hk μ hμ f t ht) =
      hodgeHeatHilbert g μ hμ 0 t
        (compactHodgeIterateHilbert g μ hμ (scalarForm f) (scalarForm_smooth f f.2.1)
          (scalarForm_compact f f.2.2) 0) := by
  have hAE : scalarHeatFamily g μ hμ t (scalarEnergyDomainL2 g μ hμ f) =ᵐ[μ]
      compactHeat g hk μ hμ f t := by
    rw [compactHeat_pos g hk μ hμ f ht]
    exact (scalarClassicalHeat_ae (complexDimension_pos M) g hk μ hμ
      (scalarEnergyDomainL2 g μ hμ f) ht).symm
  rw [← TraceHilbert.scalarLift_realize g μ _ _ (compactHeat_scalar_l2 g hk μ hμ f t ht) hAE,
    TraceHilbert.scalarHeat_eq_hodgeHeat g μ hμ hk _ t ht.le]
  congr 1
  exact TraceHilbert.scalarLift_realize g μ _ f
    (compactHodgeIterate_l2 g μ hμ (scalarForm f) (scalarForm_smooth f f.2.1)
      (scalarForm_compact f f.2.2) 0) (scalarEnergyDomainL2_coe g μ hμ f)

end Yau.NodeProofs.P06Aux.ScalarSmooth
