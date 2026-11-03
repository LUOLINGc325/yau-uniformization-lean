import Yau.Proofs.P06IntervalConeNormal

noncomputable section
open MeasureTheory
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs.L03
variable {n : ℕ} {M : ComplexManifold n}

/-- The original Friedrichs resolvent preserves the paper's exact same C,
including C=0; its projection competitor lies in the original q-domain. -/
theorem hodgeImplicitResolvent_interval (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (hHBC : ∀ x u v, 0 ≤ paperHolomorphicBisectionalCurvature g.form x u v)
    {C : ℝ} (hC : 0 ≤ C) (s : ℝ) (hs : 0 < s)
    (f : L2FormHilbert g μ 2) (hf : f ∈ hodgeL2IntervalCone g μ C) :
    hodgeImplicitResolvent g μ hμ 2 s hs f ∈ hodgeL2IntervalCone g μ C := by
  obtain ⟨u, hu, hvar⟩ := hodgeImplicitResolvent_energy g μ hμ s hs f
  have htyped : oneOneProjectionHilbert g μ (hodgeEnergyValue g μ hμ u) = hodgeEnergyValue g μ hμ u := by
    rw [hu]
    exact hodgeImplicitResolvent_oneOne g μ hμ hk s hs f hf.1
  obtain ⟨A, hA, h11, hrep⟩ := exists_oneOneL2_representative g μ (hodgeEnergyValue g μ hμ u) htyped
  obtain ⟨v, hv, hq⟩ := hodgeEnergy_intervalForm g μ hμ hk hHBC u A hA h11 hrep.symm hC
  have hd : ‖hodgeEnergyValue g μ hμ v - f‖ ^ 2 ≤ ‖hodgeEnergyValue g μ hμ u - f‖ ^ 2 -
      ‖hodgeEnergyValue g μ hμ u - hodgeEnergyValue g μ hμ v‖ ^ 2 := by
    rw [← hrep, hv]
    exact Clip.distance_sq_le_of_normal_inequality _ _ _
      (intervalForm_Hilbert_normal g μ hμ A hA h11 hC f hf)
  have he := hodgeEnergy_competitor_eq g μ hμ f s⁻¹ (inv_pos.mpr hs) u v hvar hq hd
  rw [← hu, he, hv]
  exact realizeActualForm_mem_hodgeL2IntervalCone g μ _ _ (Clip.intervalForm_oneOne g.form C A)
    (Clip.intervalForm_orderBound g.form hC A h11)

/-- The same complete CFC heat preserves the exact signed interval bound,
by the genuine same-C resolvents and the original t/2 Euler limit. -/
theorem hodgeHeatHilbert_interval (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (hHBC : ∀ x u v, 0 ≤ paperHolomorphicBisectionalCurvature g.form x u v)
    {C : ℝ} (hC : 0 ≤ C) (f : L2FormHilbert g μ 2)
    (hf : f ∈ hodgeL2IntervalCone g μ C) (t : ℝ) (ht : 0 ≤ t) :
    hodgeHeatHilbert g μ hμ 2 t f ∈ hodgeL2IntervalCone g μ C :=
  hodgeHeat_mem_of_resolvent_invariant g μ hμ 2 (hodgeL2IntervalCone g μ C)
    (hodgeL2IntervalCone_isClosed g μ C)
    (fun s hs u hu => hodgeImplicitResolvent_interval g μ hμ hk hHBC hC s hs u hu) f hf t ht

end Yau.NodeProofs.P06Aux
