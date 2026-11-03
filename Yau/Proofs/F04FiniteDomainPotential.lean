import Yau.Proofs.F04ConcreteEvolution
import Yau.Proofs.F04CutoffSourceProfile
import Yau.Proofs.F04FlowVariationalInitialRegularity

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

/-- An actual finite-domain zero-initial cutoff potential is constructed
 BEFORE all charts. The source, genuine concrete V/J/B evolution and
 ONE original continuous pivot trace are produced internally. Every
 interior chart then has actual forced classical representatives with
 SAME-rho bounds and one-sided initial C-infinity. No weak solver,
 source-L2, regularity or classical bound is an input. -/
theorem flow_finite_domain_cutoff_potential
    (hn : 0 < n) (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (Ω K : Set (Pt X)) (hΩ : IsOpen Ω) (hK : IsCompact K) (hΩK : Ω ⊆ K)
    {S : ℝ} (hS : 0 < S) (q : Pt X → ℝ) (hq : SmoothFn q)
    (hqRange : ∀ x, 0 ≤ q x ∧ q x ≤ 1) :
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
        (∀ᵐ t ∂volume.restrict (Ioo 0 S),
          (fun z => u (z,t)) =ᵐ[volume.restrict V]
            scalarEnergy_chartRestrictionCLM X.metric μ hμ c hV hVC
              (hVO.trans (subset_closure.trans hOt))
              (scalarEnergyL2 X.metric μ hμ (uE t).val)) ∧
        ∀ W : Set (Space n), IsOpen W → IsCompact (closure W) → closure W ⊆ V →
          ∃ s : ℝ, 0 < s ∧ s < S ∧ ContDiffOn ℝ ∞ (zeroPast uc) (W ×ˢ Icc 0 s) := by
  obtain ⟨hv,_hfC,hf,hSrc⟩ := flow_cutoff_source_L2_profile X o h U P ρ hloc μ hμ Ω K
    hΩ.measurableSet hK hΩK hS q hq hqRange
  obtain ⟨B,C,shift,E,hForm,hEvolution⟩ := flow_dirichlet_evolution_output X o h U P ρ hloc
    μ hμ Ω K hΩ hK hΩK hS
  obtain ⟨uE,wE,A,hSol,_hEnergy,_hTrace,_hUnique⟩ := hEvolution.2 (fun t => scalarToLp (hv t)) hf
  refine ⟨hv,B,C,shift,uE,wE,A,hForm,hSol,?_⟩
  intro c O V hO hOC hOt hV hVC hVO hMap
  have hSourceSmooth := flow_cutoff_source_smooth_closed X o h U P ρ hloc hS q hq
  have hvSmooth : ContDiffOn ℝ ∞
      (fun z : Point n => q (chartInv c z.1) * source X h (chartInv c z.1) (timeClamp S hS.le z.2))
      (O ×ˢ Icc 0 S) := by
    apply ((hSourceSmooth c).mono (prod_mono (subset_closure.trans hOt) (Subset.refl _))).congr
    intro z hz
    rw [timeClamp_eq_of_mem S hS.le hz.2]
  obtain ⟨u,uc,huL,huc,hAE,hPDE,hBounds,hSlices,hInitial⟩ :=
    flow_variational_chart_initial_regularization hn X o h U P ρ hloc μ hμ Ω K hΩ hK hΩK hS
      B hForm (fun t => scalarToLp (hv t)) hf uE wE A hSol
      (fun x t => q x * source X h x (timeClamp S hS.le t)) hv (ae_of_all _ (fun _ => rfl))
      hSrc c hO hOC hOt hV hVC hVO hMap hvSmooth
  refine ⟨u,uc,huL,huc,hAE,?_,hBounds,hSlices,hInitial⟩
  intro z hz
  simpa only [timeClamp_eq_of_mem S hS.le (Ioo_subset_Icc_self hz.2)] using hPDE z hz

end Yau.F04Proof
