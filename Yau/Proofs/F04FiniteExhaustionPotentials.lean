import Yau.Proofs.F04FinitePotentialData
import Yau.Proofs.F04ExhaustionDomains

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace
noncomputable section
namespace Yau.F04Proof
open Yau.Blueprint

/-- On the GIVEN controlled exhaustion, actual finite classical potentials
 with a compact source form a monotone sequence on the SAME time horizon.
 Their original weak/form/source records and one uniform Mt bound are kept. -/
theorem flow_finite_exhaustion_potentials
    {n : ℕ} (hn : 0 < n) (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    {T : ℝ} (hT : 0 < T) (q : Pt X → ℝ) (hq : SmoothFn q)
    (hqRange : ∀ x, 0 ≤ q x ∧ q x ≤ 1) (hcq : HasCompactSupport q) :
    ∃ M : ℝ, 0 ≤ M ∧ ∃ v : ℕ → STF X,
      (∀ j, IsFiniteClassicalPotential X h ρ μ hμ T hT q M (potentialDomain u j) (v j)) ∧
      ∀ x t, t ∈ Icc 0 T → Monotone (fun j => v j x t) := by
  classical
  obtain ⟨M,hM,hDomains⟩ := flow_uniform_finite_potential_data hn X o h U P ρ hloc μ hμ hT q hq hqRange hcq
  have hData (j : ℕ) := hDomains (potentialDomain u j) (closure (potentialDomain u j))
    (potentialDomain_open X o u hu j) (potentialDomain_compact_closure X o u hu j) subset_closure
  choose v hv using hData
  refine ⟨M,hM,v,hv,?_⟩
  intro x t ht
  apply monotone_nat_of_le_succ
  intro j
  exact finite_potential_data_le X o h U P ρ hloc μ hμ hT (fun _ => le_rfl)
    (potentialDomain_open X o u hu j) (potentialDomain_compact_closure X o u hu j)
    (potentialDomain_open X o u hu (j+1)) (potentialDomain_closure_succ X o u hu j)
    (hv j) (hv (j+1)) x t ht

end Yau.F04Proof
