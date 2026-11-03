import Yau.Proofs.P06L2PositiveCone

noncomputable section
open MeasureTheory
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs.L03
variable {n : ℕ} {M : ComplexManifold n}

theorem hodgeImplicitResolvent_positive (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (hHBC : ∀ x u v, 0 ≤ paperHolomorphicBisectionalCurvature g.form x u v)
    (s : ℝ) (hs : 0 < s) (f : L2FormHilbert g μ 2) (hf : f ∈ hodgeL2PositiveCone g μ) :
    hodgeImplicitResolvent g μ hμ 2 s hs f ∈ hodgeL2PositiveCone g μ := by
  obtain ⟨u, hu, hvar⟩ := hodgeImplicitResolvent_energy g μ hμ s hs f
  have htyped : oneOneProjectionHilbert g μ (hodgeEnergyValue g μ hμ u) = hodgeEnergyValue g μ hμ u := by
    rw [hu]
    exact hodgeImplicitResolvent_oneOne g μ hμ hk s hs f hf.1
  obtain ⟨A, hA, h11, hrep⟩ := exists_oneOneL2_representative g μ (hodgeEnergyValue g μ hμ u) htyped
  obtain ⟨v, hv, hq⟩ := hodgeEnergy_positiveForm g μ hμ hk hHBC u A hA h11 hrep.symm
  have hd : ‖hodgeEnergyValue g μ hμ v - f‖ ^ 2 ≤ ‖hodgeEnergyValue g μ hμ u - f‖ ^ 2 -
      ‖hodgeEnergyValue g μ hμ u - hodgeEnergyValue g μ hμ v‖ ^ 2 := by
    rw [← hrep, hv]
    exact Clip.distance_sq_le_of_normal_inequality _ _ _ (positiveForm_Hilbert_normal g μ A hA h11 f hf)
  have he := hodgeEnergy_competitor_eq g μ hμ f s⁻¹ (inv_pos.mpr hs) u v hvar hq hd
  rw [← hu, he, hv]
  exact realizeActualForm_mem_hodgeL2PositiveCone g μ _ _ (Clip.positiveForm_oneOne g.form A)
    (Clip.positiveForm_nonnegative g.form A)

/-- The same complete CFC Hodge heat preserves the genuine closed L²
positive cone, by actual Friedrichs resolvents and their Euler limit. -/
theorem hodgeHeatHilbert_positive (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (hHBC : ∀ x u v, 0 ≤ paperHolomorphicBisectionalCurvature g.form x u v)
    (f : L2FormHilbert g μ 2) (hf : f ∈ hodgeL2PositiveCone g μ) (t : ℝ) (ht : 0 ≤ t) :
    hodgeHeatHilbert g μ hμ 2 t f ∈ hodgeL2PositiveCone g μ :=
  hodgeHeat_mem_of_resolvent_invariant g μ hμ 2 (hodgeL2PositiveCone g μ)
    (hodgeL2PositiveCone_isClosed g μ)
    (fun s hs u hu => hodgeImplicitResolvent_positive g μ hμ hk hHBC s hs u hu) f hf t ht

end Yau.NodeProofs.P06Aux
