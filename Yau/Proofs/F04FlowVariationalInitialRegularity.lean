import Yau.Proofs.F04VariationalChartRegularity
import Yau.Proofs.F04FlowChartBounds
import Yau.Proofs.F04ForcedInitialRegularity

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

/-- The original localized-flow weak solution has an actual classical
 chart representative, the original pointwise rho bounds, and genuine
 one-sided C-infinity at its zero initial face. All WE, ellipticity,
 order, compact growth, particular solution, homogeneous subtraction and
 crossing extension are constructed from the ORIGINAL hSol and hloc.
 No regularity, classical bound or initial-growth oracle is an inlet. -/
theorem flow_variational_chart_initial_regularization
    (hn : 0 < n) (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (Ω K : Set (Pt X)) (hΩ : IsOpen Ω) (hK : IsCompact K) (hΩK : Ω ⊆ K)
    {S C α shift : ℝ} (hS : 0 < S)
    (B : ℝ → DirichletEnergy X.metric μ hμ Ω →L[ℝ] EnergyDual (DirichletEnergy X.metric μ hμ Ω))
    (hForm : IntrinsicFormBinding X.metric.form μ Ω h S C α shift
      (dirichletL2 X.metric μ hμ Ω) (energyRepresentative X.metric μ hμ Ω) B)
    (f : ℝ → FixedPivot μ Ω) (hf : MemLp f 2 (volume.restrict (Ioo 0 S)))
    (uE : ℝ → DirichletEnergy X.metric μ hμ Ω) (wE : ℝ → EnergyDual (DirichletEnergy X.metric μ hμ Ω))
    (A : ℝ → FixedPivot μ Ω)
    (hSol : VariationalSolution μ Ω S (dirichletL2 X.metric μ hμ Ω) B f uE wE A)
    (v : Pt X → ℝ → ℝ) (hv : ∀ t, ScalarL2 (μ.restrict Ω) (fun x => v x t))
    (hfActual : ∀ᵐ t ∂volume.restrict (Ioo 0 S), f t = scalarToLp (hv t))
    (hSrc : ∀ᵐ t ∂volume.restrict (Ioo 0 S), ∀ᵐ x ∂μ.restrict Ω,
      0 ≤ f t x ∧ f t x ≤ source X h x t)
    (c : Pt X) {O V : Set (Space n)} (hO : IsOpen O) (hOC : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget c) (hV : IsOpen V) (hVC : IsCompact (closure V))
    (hVO : closure V ⊆ O) (hMap : chartInv c '' V ⊆ Ω)
    (hvSmooth : ContDiffOn ℝ ∞ (fun q : Point n => v (chartInv c q.1) q.2) (O ×ˢ Icc 0 S)) :
    ∃ (u uc : Point n → ℝ),
      MemLp u 2 (productVolume V (Ioo 0 S)) ∧
      ContDiffOn ℝ ∞ uc (V ×ˢ Ioo 0 S) ∧
      u =ᵐ[productVolume V (Ioo 0 S)] uc ∧
      (∀ q ∈ V ×ˢ Ioo 0 S,
        linearOp (V ×ˢ Icc 0 S) (flowChartPrincipal h c) (fun _ _ => 0) uc q =
          v (chartInv c q.1) q.2) ∧
      (∀ q ∈ V ×ˢ Ioo 0 S, 0 ≤ uc q ∧ uc q ≤ ρ (chartInv c q.1) q.2) ∧
      (∀ᵐ t ∂volume.restrict (Ioo 0 S),
        (fun z => u (z,t)) =ᵐ[volume.restrict V]
          scalarEnergy_chartRestrictionCLM X.metric μ hμ c hV hVC (hVO.trans (subset_closure.trans hOt))
            (scalarEnergyL2 X.metric μ hμ (uE t).val)) ∧
      ∀ W : Set (Space n), IsOpen W → IsCompact (closure W) → closure W ⊆ V →
        ∃ s : ℝ, 0 < s ∧ s < S ∧ ContDiffOn ℝ ∞ (zeroPast uc) (W ×ˢ Icc 0 s) := by
  have hh : MetricFamilySmooth h (Icc 0 S) := fun c i j =>
    (hloc.1.2.1 c i j).mono (prod_mono (Subset.refl _) (fun _ ht => ht.1))
  obtain ⟨u,uc,huL,huc,hAE,hPDE,hSlices⟩ := variationalSolution_chart_smooth_representative hn
    X.metric X.kahler_metric μ hμ Ω K hΩ hK hΩK h hS hh B hForm f hf uE wE A hSol
    v hv hfActual c hO hOC hOt hV hVC hVO hMap hvSmooth
  have hVt : closure V ⊆ chartTarget c := hVO.trans (subset_closure.trans hOt)
  obtain ⟨hBounds,hGrowth⟩ := flow_variational_smooth_chart_bounds X o h U P ρ hloc μ hμ Ω K hΩ hK hΩK
    hS B hForm f uE wE A hSol hSrc c hV hVC hVt hMap huL huc hAE hSlices
  refine ⟨u,uc,huL,huc,hAE,hPDE,hBounds,hSlices,?_⟩
  intro W hW hWC hWV
  have hCoeff := flowChartPrincipal_smooth h hh c
  have hSub : V ×ˢ Icc (0 : ℝ) S ⊆ chartTarget c ×ˢ Icc 0 S :=
    prod_mono (subset_closure.trans hVt) (Subset.refl _)
  have hSV : SmoothCoefficients (V ×ˢ Icc 0 S) (flowChartPrincipal h c) (fun _ _ => 0) :=
    ⟨hCoeff.1.mono hSub,fun i => (hCoeff.2 i).mono hSub⟩
  obtain ⟨lam,upper,hEll⟩ := flowChartPrincipal_elliptic h hh c
    (hVC.prod isCompact_Icc) (prod_mono hVt (Subset.refl _))
  exact forced_linearGrowth_initial_regularization hn hV hS hSV
    (hvSmooth.mono (prod_mono (subset_closure.trans hVO) (Subset.refl _)))
    (elliptic_mono hEll (prod_mono subset_closure (Subset.refl _))) huc hPDE hGrowth W hW hWC hWV

end Yau.F04Proof
