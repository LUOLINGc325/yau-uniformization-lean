import Yau.Proofs.F04FiniteClassicalPotential
import Yau.Proofs.F04FiniteDomainComparison

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace
noncomputable section
namespace Yau.F04Proof
open Yau.Blueprint Yau.Proofs.F03Aux Yau.MassTargetStatements Yau.HeatConcreteBindings
variable {n : ℕ}

local instance (X : KahlerManifold n) (μ : Measure (Pt X))
    (hμ : IsRiemannianVolume X.metric.form μ) (O : Set (Pt X)) :
    CompleteSpace (DirichletEnergy X.metric μ hμ O) := dirichletEnergy_completeSpace X.metric μ hμ O

/-- An internal record of the genuine finite potential AND its original
 energy solution. This is only a repackaging of the constructed output,
 including the same larger-horizon source and every closed-time trace. -/
def IsFiniteClassicalPotential
    (X : KahlerManifold n) (h : Flow X) (ρ : STF X)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (T : ℝ) (hT : 0 < T) (q : Pt X → ℝ) (M : ℝ) (Ω : Set (Pt X)) (v : STF X) : Prop :=
  ∃ (B : ℝ → DirichletEnergy X.metric μ hμ Ω →L[ℝ] EnergyDual (DirichletEnergy X.metric μ hμ Ω))
    (C shift : ℝ) (f : ℝ → FixedPivot μ Ω) (uE : ℝ → DirichletEnergy X.metric μ hμ Ω)
    (wE : ℝ → EnergyDual (DirichletEnergy X.metric μ hμ Ω)) (A : ℝ → FixedPivot μ Ω),
    IntrinsicFormBinding X.metric.form μ Ω h (2*T) C (1/2) shift
      (dirichletL2 X.metric μ hμ Ω) (energyRepresentative X.metric μ hμ Ω) B ∧
    VariationalSolution μ Ω (2*T) (dirichletL2 X.metric μ hμ Ω) B f uE wE A ∧
    (∀ t, (f t : Pt X → ℝ) =ᵐ[μ.restrict Ω]
      (fun x => q x * source X h x (timeClamp (2*T) (by positivity) t))) ∧
    (∀ c, ContDiffOn ℝ ∞ (fun p : Yau.Parabolic.Point n => v (chartInv c p.1) p.2)
      ((chartTarget c ∩ chartInv c ⁻¹' Ω) ×ˢ Icc 0 T)) ∧
    (∀ t ∈ Icc 0 T, (fun x => v x t) =ᵐ[μ.restrict Ω] (A t : Pt X → ℝ)) ∧
    (∀ x t, t ∈ Icc 0 T → 0 ≤ v x t ∧ v x t ≤ ρ x t ∧ v x t ≤ M*t) ∧
    (∀ x, v x 0 = 0) ∧ (∀ x ∉ Ω, ∀ t, v x t = 0) ∧
    (∀ x ∈ Ω, ∀ t ∈ Icc 0 T, heatOp h (Icc 0 T) v x t = q x * source X h x t)

/-- The internal finite-potential record is genuinely produced from the
 original localized flow, with ONE constant before every finite domain. -/
theorem flow_uniform_finite_potential_data
    (hn : 0 < n) (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    {T : ℝ} (hT : 0 < T) (q : Pt X → ℝ) (hq : SmoothFn q)
    (hqRange : ∀ x, 0 ≤ q x ∧ q x ≤ 1) (hcq : HasCompactSupport q) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (Ω K : Set (Pt X)), IsOpen Ω → IsCompact K → Ω ⊆ K →
      ∃ v : STF X, IsFiniteClassicalPotential X h ρ μ hμ T hT q M Ω v := by
  obtain ⟨M,hM,hDomains⟩ := flow_uniform_finite_classical_potential hn X o h U P ρ hloc μ hμ hT q hq hqRange hcq
  refine ⟨M,hM,?_⟩
  intro Ω K hΩ hK hΩK
  obtain ⟨B,C,shift,f,uE,wE,A,v,hData⟩ := hDomains Ω K hΩ hK hΩK
  exact ⟨v,B,C,shift,f,uE,wE,A,hData⟩

/-- Actual constructed finite-potential records retain enough information
 for both domain and cutoff-source comparison. -/
theorem finite_potential_data_le
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    {T : ℝ} (hT : 0 < T) {q r : Pt X → ℝ} (hqr : ∀ x, q x ≤ r x)
    {M N : ℝ} {Ω Γ : Set (Pt X)} (hΩ : IsOpen Ω) (hΩC : IsCompact (closure Ω))
    (hΓ : IsOpen Γ) (hΩΓ : closure Ω ⊆ Γ) {v z : STF X}
    (hv : IsFiniteClassicalPotential X h ρ μ hμ T hT q M Ω v)
    (hz : IsFiniteClassicalPotential X h ρ μ hμ T hT r N Γ z) :
    ∀ x t, t ∈ Icc 0 T → v x t ≤ z x t := by
  rcases hv with ⟨B,C,shift,f,uE,wE,A,hForm,hSol,hF,hv,hTrace,_hBound,_h0,hOff,_hPDE⟩
  rcases hz with ⟨_B,_C,_shift,_f,_uE,_wE,_A,_hForm,_hSol,_hF,hz,_hTrace,hBound,_h0,_hOff,hPDE⟩
  exact finite_classical_potential_domain_source_le X o h U P ρ hloc μ hμ Ω Γ hΩ hΩC hΓ hΩΓ hT
    B hForm f uE wE A hSol q r hqr hF v z hv hTrace hOff hz (fun x t ht => (hBound x t ht).1) hPDE

end Yau.F04Proof
