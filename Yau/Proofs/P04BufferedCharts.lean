import Yau.Proofs.P04CutoffModel

noncomputable section
open Set
open scoped Topology Manifold ContDiff

namespace Yau.Proofs.P04Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

/-- A genuine countable cover by inner chart balls, each with a smooth
compact cutoff equal to one on a larger ball and buffered inside its chart. -/
theorem exists_countable_buffered_charts :
    ∃ a : ℕ → M.Carrier, ∃ ρ : ℕ → ℝ, ∃ β : ℕ → ComplexVector n → ℝ,
      (∀ j, 0 < ρ j ∧
        Metric.closedBall (chartPt (a j) (a j)) (2*ρ j) ⊆ chartTarget (a j) ∧
        ContDiff ℝ ∞ (β j) ∧ HasCompactSupport (β j) ∧
        tsupport (β j) ⊆ Metric.closedBall (chartPt (a j) (a j)) (3*ρ j/2) ∧
        ∀ z ∈ Metric.closedBall (chartPt (a j) (a j)) (ρ j), β j z=1) ∧
      ∀ x : M.Carrier, ∃ j, x ∈ (extChartAt (ComplexModel n) (a j)).source ∧
        chartPt (a j) x ∈ Metric.ball (chartPt (a j) (a j)) (ρ j/2) := by
  classical
  choose ρ hρ _hsmall htarget β hβ hcompact hsupp hone _hbounded using
    (fun p : M.Carrier => exists_pole_cutoff p)
  let U : M.Carrier → Set M.Carrier := fun p => (extChartAt (ComplexModel n) p).source ∩
    (chartPt p) ⁻¹' Metric.ball (chartPt p p) (ρ p/2)
  have hU (p : M.Carrier) : IsOpen (U p) :=
    (continuousOn_extChartAt (I := ComplexModel n) p).isOpen_inter_preimage
      (isOpen_extChartAt_source p) Metric.isOpen_ball
  have hself (p : M.Carrier) : p ∈ U p :=
    ⟨mem_extChartAt_source p,Metric.mem_ball_self (half_pos (hρ p))⟩
  have hcover : (⋃ p, U p)=univ := eq_univ_of_forall (fun x => mem_iUnion.mpr ⟨x,hself x⟩)
  obtain ⟨T,hT,hTU⟩ := TopologicalSpace.isOpen_iUnion_countable U hU
  have hcoverT : (⋃ p ∈ T, U p)=univ := hTU.trans hcover
  have hTne : T.Nonempty := by
    let x : M.Carrier := Classical.choice inferInstance
    have hx : x ∈ ⋃ p ∈ T, U p := by rw [hcoverT]; trivial
    obtain ⟨p,hp⟩ := mem_iUnion.mp hx
    obtain ⟨hpT,_⟩ := mem_iUnion.mp hp
    exact ⟨p,hpT⟩
  obtain ⟨a,ha⟩ := hT.exists_eq_range hTne
  refine ⟨a,fun j => ρ (a j),fun j => β (a j),fun j =>
    ⟨hρ _,htarget _,hβ _,hcompact _,hsupp _,hone _⟩,fun x => ?_⟩
  have hx : x ∈ ⋃ p ∈ T, U p := by rw [hcoverT]; trivial
  obtain ⟨p,hp⟩ := mem_iUnion.mp hx
  obtain ⟨hpT,hpU⟩ := mem_iUnion.mp hp
  rw [ha] at hpT
  obtain ⟨j,rfl⟩ := hpT
  exact ⟨j,hpU⟩

end Yau.Proofs.P04Aux
