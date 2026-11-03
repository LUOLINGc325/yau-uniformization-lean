import Yau.Proofs.F04FiniteDomainPotential
import Yau.Proofs.F04FlowChartLinearBound
import Yau.Proofs.F04CompactSourceBound

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.F04Proof
open Yau.Blueprint Yau.Parabolic Yau.ParabolicCandidates Yau.Proofs.F03Aux
  Yau.MassTargetStatements Yau.LeafProofs.L19Aux Yau.LeafProofs.L16Aux Yau.HeatConcreteBindings
variable {n : ℕ}

local instance (X : KahlerManifold n) (μ : Measure (Pt X))
    (hμ : IsRiemannianVolume X.metric.form μ) (Ω : Set (Pt X)) :
    CompleteSpace (DirichletEnergy X.metric μ hμ Ω) := dirichletEnergy_completeSpace X.metric μ hμ Ω

/-- A genuine compact cutoff has ONE uniform source constant BEFORE all
 finite domains. Each domain receives its actual zero-initial solution
 BEFORE all charts, and every actual chart representative is bounded by
 the SAME Mt as well as the original rho. No source norm, solver or
 classical bound is an inlet. -/
theorem flow_finite_domain_cutoff_potential_uniform_bound
    (hn : 0 < n) (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    {S : ℝ} (hS : 0 < S) (q : Pt X → ℝ) (hq : SmoothFn q)
    (hqRange : ∀ x, 0 ≤ q x ∧ q x ≤ 1) (hcq : HasCompactSupport q) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (Ω K : Set (Pt X)) (hΩ : IsOpen Ω) (hK : IsCompact K) (hΩK : Ω ⊆ K),
    ∃ (hv : ∀ t, ScalarL2 (μ.restrict Ω) (fun x => q x * source X h x (timeClamp S hS.le t)))
      (B : ℝ → DirichletEnergy X.metric μ hμ Ω →L[ℝ] EnergyDual (DirichletEnergy X.metric μ hμ Ω))
      (C shift : ℝ) (uE : ℝ → DirichletEnergy X.metric μ hμ Ω)
      (wE : ℝ → EnergyDual (DirichletEnergy X.metric μ hμ Ω)) (A : ℝ → FixedPivot μ Ω),
      IntrinsicFormBinding X.metric.form μ Ω h S C (1/2) shift
        (dirichletL2 X.metric μ hμ Ω) (energyRepresentative X.metric μ hμ Ω) B ∧
      VariationalSolution μ Ω S (dirichletL2 X.metric μ hμ Ω) B (fun t => scalarToLp (hv t)) uE wE A ∧
      ∀ (c : Pt X) (O V : Set (Space n)) (hO : IsOpen O) (hOC : IsCompact (closure O))
        (hOt : closure O ⊆ chartTarget c) (hV : IsOpen V) (hVC : IsCompact (closure V))
        (hVO : closure V ⊆ O), chartInv c '' V ⊆ Ω →
      ∃ (u uc : Point n → ℝ),
        MemLp u 2 (productVolume V (Ioo 0 S)) ∧
        ContDiffOn ℝ ∞ uc (V ×ˢ Ioo 0 S) ∧
        u =ᵐ[productVolume V (Ioo 0 S)] uc ∧
        (∀ z ∈ V ×ˢ Ioo 0 S,
          linearOp (V ×ˢ Icc 0 S) (flowChartPrincipal h c) (fun _ _ => 0) uc z =
            q (chartInv c z.1) * source X h (chartInv c z.1) z.2) ∧
        (∀ z ∈ V ×ˢ Ioo 0 S, 0 ≤ uc z ∧ uc z ≤ ρ (chartInv c z.1) z.2) ∧
        (∀ z ∈ V ×ˢ Ioo 0 S, uc z ≤ M*z.2) ∧
        (∀ᵐ t ∂volume.restrict (Ioo 0 S),
          (fun z => u (z,t)) =ᵐ[volume.restrict V]
            scalarEnergy_chartRestrictionCLM X.metric μ hμ c hV hVC
              (hVO.trans (subset_closure.trans hOt))
              (scalarEnergyL2 X.metric μ hμ (uE t).val)) ∧
        ∀ W : Set (Space n), IsOpen W → IsCompact (closure W) → closure W ⊆ V →
          ∃ s : ℝ, 0 < s ∧ s < S ∧ ContDiffOn ℝ ∞ (zeroPast uc) (W ×ˢ Icc 0 s) := by
  obtain ⟨M,hM,hMb⟩ := flow_compact_cutoff_source_bound X o h U P ρ hloc hS q hq hcq
  refine ⟨M,hM,?_⟩
  intro Ω K hΩ hK hΩK
  obtain ⟨hv,B,C,shift,uE,wE,A,hForm,hSol,hCharts⟩ := flow_finite_domain_cutoff_potential hn
    X o h U P ρ hloc μ hμ Ω K hΩ hK hΩK hS q hq hqRange
  have hSrcM : ∀ᵐ t ∂volume.restrict (Ioo 0 S), ∀ᵐ x ∂μ.restrict Ω,
      0 ≤ scalarToLp (hv t) x ∧ scalarToLp (hv t) x ≤ M := by
    apply ae_of_all
    intro t
    filter_upwards [scalarToLp_coe (hv t)] with x hx
    rw [hx]
    have hτ := timeClamp_mem S hS.le t
    have hF : 0 ≤ source X h x (timeClamp S hS.le t) :=
      source_nonneg o h U P ρ hloc x _ hτ.1
    exact ⟨mul_nonneg (hqRange x).1 hF,
      (le_abs_self _).trans (hMb x (timeClamp S hS.le t) hτ)⟩
  refine ⟨hv,B,C,shift,uE,wE,A,hForm,hSol,?_⟩
  intro c O V hO hOC hOt hV hVC hVO hMap
  obtain ⟨u,uc,huL,huc,hAE,hPDE,hBounds,hSlices,hInitial⟩ := hCharts c O V hO hOC hOt hV hVC hVO hMap
  have hLin := flow_variational_smooth_chart_linear_bound X o h U P ρ hloc μ hμ Ω K hΩ hK hΩK hS hM
    B hForm (fun t => scalarToLp (hv t)) uE wE A hSol hSrcM c hV hVC
    (hVO.trans (subset_closure.trans hOt)) hMap huL huc hAE hSlices
  exact ⟨u,uc,huL,huc,hAE,hPDE,hBounds,(fun z hz => (hLin z hz).2),hSlices,hInitial⟩

end Yau.F04Proof
