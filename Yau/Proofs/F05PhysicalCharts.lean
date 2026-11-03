import Yau.Proofs.F05BufferedBoundary
import Yau.Proofs.F05BufferedInterior

/-! Every point of the actual compact closure has an interior or genuine physical
boundary chart. All geometry is obtained from SmoothPrecompactDomain. -/

open Set
open scoped Topology ContDiff Manifold
noncomputable section

namespace Yau.Proofs.F05Aux

open Yau.Parabolic Yau.HeatConcreteBindings
variable {n : ℕ} {M : ComplexManifold n}

def F05PhysicalChart (O : Set M.Carrier) (p x : M.Carrier) (ν : Option (RIdx n))
    (c : OpenPartialHomeomorph (Space n) (Space n)) : Prop :=
  p ∈ (extChartAt (ComplexModel n) x).source ∧ chartPt x p ∈ c.source ∧
  c (chartPt x p) = 0 ∧ c.source ⊆ chartTarget x ∧ Metric.closedBall 0 4 ⊆ c.target ∧
  ContDiffOn ℝ ∞ c c.source ∧ ContDiffOn ℝ ∞ c.symm c.target ∧
  ∀ z ∈ c.source,
    (chartInv x z ∈ O ↔ match ν with | none => True | some j => realCoord (c z) j < 0) ∧
    (chartInv x z ∈ closure O ↔ match ν with | none => True | some j => realCoord (c z) j ≤ 0) ∧
    (chartInv x z ∈ frontier O ↔ match ν with | none => False | some j => realCoord (c z) j = 0)

theorem smoothPrecompact_physical_chart {O : Set M.Carrier}
    (hO : SmoothPrecompactDomain O) (p : M.Carrier) (hp : p ∈ closure O) :
    ∃ (x : M.Carrier) (ν : Option (RIdx n)) (c : OpenPartialHomeomorph (Space n) (Space n)),
      F05PhysicalChart O p x ν c := by
  by_cases hpO : p ∈ O
  · obtain ⟨c,hpc,hcp,hcT,hbuffer,hc,hci,hinside⟩ := open_buffered_interior_chart hO.1 hpO
    refine ⟨p,none,c,mem_extChartAt_source p,hpc,hcp,hcT,hbuffer,hc,hci,?_⟩
    intro z hz
    have hzO := hinside z hz
    have hzK := subset_closure hzO
    have hzF : chartInv p z ∉ frontier O := by
      intro hh
      rw [frontier,hO.1.interior_eq] at hh
      exact hh.2 hzO
    exact ⟨iff_true_intro hzO,iff_true_intro hzK,iff_false_intro hzF⟩
  · have hpF : p ∈ frontier O := by
      rw [frontier,hO.1.interior_eq]
      exact ⟨hp,hpO⟩
    obtain ⟨x,j,c,hpx,hpc,hcp,hcT,hbuffer,hc,hci,hfaces⟩ :=
      smoothPrecompact_buffered_boundary_chart hO hpF
    exact ⟨x,some j,c,hpx,hpc,hcp,hcT,hbuffer,hc,hci,hfaces⟩

end Yau.Proofs.F05Aux
