import Yau.Proofs.P06HodgeClippingTransfer

noncomputable section
open MeasureTheory
open scoped Topology

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs.L03
variable {n : ℕ} {M : ComplexManifold n}

/-- The actual same-C interval clip preserves the original closed Hodge
energy domain and decreases q for every real (1,1) L² representative. -/
theorem hodgeEnergy_intervalForm (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (hHBC : ∀ x u v, 0 ≤ paperHolomorphicBisectionalCurvature g.form x u v)
    (u : HodgeEnergySpace g μ hμ) (A : RealForm M 2)
    (hA : L2RealForm g.form μ A) (h11 : RealOneOne A)
    (hu : hodgeEnergyValue g μ hμ u = realizeActualForm g μ A hA) {C : ℝ} (hC : 0 ≤ C) :
    ∃ v : HodgeEnergySpace g μ hμ,
      hodgeEnergyValue g μ hμ v = realizeActualForm g μ (Clip.intervalForm g.form C A)
        (FiberApprox.intervalForm_l2_of_l2 g μ A hA h11 hC) ∧
      hodgeEnergy g μ hμ v ≤ hodgeEnergy g μ hμ u := by
  apply hodgeEnergy_raw_map_of_core_contraction g μ hμ hk
    (fun A => Clip.intervalForm g.form C A)
    (fun A hA h11 => FiberApprox.intervalForm_l2_of_l2 g μ A hA h11 hC)
    (fun A B hA hB x => Clip.intervalForm_nonexpansive_sq g.form hC A B hA hB x)
    ?_ u A hA h11 hu
  intro B hB hcB h11B
  obtain ⟨hL, v, hv, hq⟩ := hodgeEnergy_intervalForm_core g μ hμ hk hHBC B hB hcB h11B hC
  exact ⟨v, hv, hq⟩

/-- Positive part is a genuine q contraction on the original energy
domain; no smoothness or closedness of its L² representative is imposed. -/
theorem hodgeEnergy_positiveForm (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (hHBC : ∀ x u v, 0 ≤ paperHolomorphicBisectionalCurvature g.form x u v)
    (u : HodgeEnergySpace g μ hμ) (A : RealForm M 2)
    (hA : L2RealForm g.form μ A) (h11 : RealOneOne A)
    (hu : hodgeEnergyValue g μ hμ u = realizeActualForm g μ A hA) :
    ∃ v : HodgeEnergySpace g μ hμ,
      hodgeEnergyValue g μ hμ v = realizeActualForm g μ (Clip.positiveForm g.form A)
        (FiberApprox.positiveForm_l2_of_l2 g μ A hA h11) ∧
      hodgeEnergy g μ hμ v ≤ hodgeEnergy g μ hμ u := by
  apply hodgeEnergy_raw_map_of_core_contraction g μ hμ hk
    (fun A => Clip.positiveForm g.form A)
    (fun A hA h11 => FiberApprox.positiveForm_l2_of_l2 g μ A hA h11)
    (fun A B hA hB x => Clip.positiveForm_nonexpansive_sq g.form A B hA hB x)
    ?_ u A hA h11 hu
  intro B hB hcB h11B
  obtain ⟨hL, v, hv, hq⟩ := hodgeEnergy_positiveForm_core g μ hμ hk hHBC B hB hcB h11B
  exact ⟨v, hv, hq⟩

end Yau.NodeProofs.P06Aux
