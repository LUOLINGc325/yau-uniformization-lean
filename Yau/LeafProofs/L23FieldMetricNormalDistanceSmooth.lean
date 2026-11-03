import Yau.LeafProofs.L23FieldMetricNormalPhase
import Yau.LeafProofs.L23FieldMetricBranchFirstVariation

/-! Squared project distance is the actual C3 energy in a normal endpoint chart. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux L23LocalDistanceContract
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 600000

theorem normalEndpoint_distanceSq_eq_energy
    (h : HermitianField M) (c : M.Carrier)
    (X : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n)
    (e : OpenPartialHomeomorph (ComplexVector n × ComplexVector n) (ComplexVector n × ComplexVector n))
    (he : Set.EqOn e (fun p => (p.1,X p 1)) e.source)
    (hmin : ∀ p ∈ e.source,
      inducedDistance h (chartInv c p.1) (chartInv c (X p 1))^2 = realMetricInChart h c p.1 p.2 p.2)
    {q : ComplexVector n × ComplexVector n} (hq : q ∈ e.target) :
    inducedDistance h (chartInv c q.1) (chartInv c q.2)^2 =
      chartGeodesicEnergy h c (e.symm q) := by
  have H := (he (e.map_target hq)).symm.trans (e.right_inv hq)
  have Hfirst := congrArg Prod.fst H
  have Hlast := congrArg Prod.snd H
  change (e.symm q).1 = q.1 at Hfirst
  change X (e.symm q) 1 = q.2 at Hlast
  calc
    _ = inducedDistance h (chartInv c (e.symm q).1) (chartInv c (X (e.symm q) 1))^2 := by
      rw [Hfirst,Hlast]
    _ = _ := hmin _ (e.map_target hq)

theorem normalEndpoint_distanceSq_contDiffOn
    (h : HermitianField M) (hh : MetricSmooth h) (c : M.Carrier)
    (X : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n)
    (e : OpenPartialHomeomorph (ComplexVector n × ComplexVector n) (ComplexVector n × ComplexVector n))
    (he : Set.EqOn e (fun p => (p.1,X p 1)) e.source)
    (hinv : ContDiffOn ℝ 3 e.symm e.target)
    (hbase : ∀ p ∈ e.source, p.1 ∈ chartTarget c)
    (hmin : ∀ p ∈ e.source,
      inducedDistance h (chartInv c p.1) (chartInv c (X p 1))^2 = realMetricInChart h c p.1 p.2 p.2) :
    ContDiffOn ℝ 3 (fun q : ComplexVector n × ComplexVector n =>
      inducedDistance h (chartInv c q.1) (chartInv c q.2)^2) e.target := by
  have HE : ContDiffOn ℝ 3 (fun q => chartGeodesicEnergy h c (e.symm q)) e.target :=
    ((chartGeodesicEnergy_contDiffOn h hh c).of_le (by simp)).comp hinv
      (fun q hq => ⟨hbase _ (e.map_target hq),Set.mem_univ _⟩)
  exact HE.congr (fun q hq => normalEndpoint_distanceSq_eq_energy h c X e he hmin hq)

end Yau.LeafProofs.L23Aux
