import Yau.Proofs.F04FiniteExhaustionPotentials
import Yau.Proofs.F04MonotonePotentialLimit

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace
noncomputable section
namespace Yau.F04Proof
open Yau.Blueprint

/-- The actual finite-domain construction gives a finite monotone
 exhaustion limit with the SAME supplied rho and one uniform Mt bound.
 Original weak records remain available before all chart regularization. -/
theorem flow_finite_exhaustion_potential_limit
    {n : ℕ} (hn : 0 < n) (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    {T : ℝ} (hT : 0 < T) (q : Pt X → ℝ) (hq : SmoothFn q)
    (hqRange : ∀ x, 0 ≤ q x ∧ q x ≤ 1) (hcq : HasCompactSupport q) :
    ∃ M : ℝ, 0 ≤ M ∧ ∃ (v : ℕ → STF X) (z : STF X),
      (∀ j, IsFiniteClassicalPotential X h ρ μ hμ T hT q M (potentialDomain u j) (v j)) ∧
      (∀ x t, t ∈ Icc 0 T → Monotone (fun j => v j x t)) ∧
      (∀ x t, t ∈ Icc 0 T → Tendsto (fun j => v j x t) atTop (𝓝 (z x t))) ∧
      (∀ x t, t ∈ Icc 0 T → 0 ≤ z x t ∧ z x t ≤ ρ x t ∧ z x t ≤ M*t) ∧
      (∀ j x t, t ∈ Icc 0 T → v j x t ≤ z x t) ∧ (∀ x, z x 0 = 0) := by
  obtain ⟨M,hM,v,hData,hMono⟩ := flow_finite_exhaustion_potentials hn X o h U P ρ hloc μ hμ u hu hT q hq hqRange hcq
  have hBound : ∀ j x t, t ∈ Icc 0 T → 0 ≤ v j x t ∧ v j x t ≤ ρ x t ∧ v j x t ≤ M*t := by
    intro j
    rcases hData j with ⟨_B,_C,_shift,_f,_uE,_wE,_A,_hForm,_hSol,_hF,_hv,_hTrace,hBound,_h0,_hOff,_hPDE⟩
    exact hBound
  have h0 : ∀ j x, v j x 0 = 0 := by
    intro j
    rcases hData j with ⟨_B,_C,_shift,_f,_uE,_wE,_A,_hForm,_hSol,_hF,_hv,_hTrace,_hBound,h0,_hOff,_hPDE⟩
    exact h0
  obtain ⟨z,hTend,hzBound,hLe,hz0⟩ := monotone_potential_limit X hT ρ v hMono hBound h0
  exact ⟨M,hM,v,z,hData,hMono,hTend,hzBound,hLe,hz0⟩

end Yau.F04Proof
