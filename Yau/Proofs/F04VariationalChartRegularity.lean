import Yau.Proofs.F04VariationalChartWeakEquation
import Yau.Proofs.F04ChartSourceIdentification
import Yau.Proofs.F04ForcedInteriorRegularity
import Yau.Proofs.F04ChartEllipticity

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.F04Proof
open Yau.Blueprint Yau.Parabolic Yau.ParabolicCandidates Yau.Proofs.F03Aux
  Yau.MassTargetStatements Yau.LeafProofs.L19Aux Yau.LeafProofs.L16Aux Yau.HeatConcreteBindings
variable {n : ℕ} {M : ComplexManifold n}

local instance (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (Ω : Set M.Carrier) :
    CompleteSpace (DirichletEnergy g μ hμ Ω) := dirichletEnergy_completeSpace g μ hμ Ω

/-- An ORIGINAL variational solution with its actual smooth physical source
 has a genuine smooth representative on every precompact interior chart.
 Source representatives and the weak PDE are constructed, compact
 ellipticity is proved from the supplied metric, and forced weak
 regularization is applied to the actual constructed chart solution. -/
theorem variationalSolution_chart_smooth_representative
    (hn : 0 < n) (g : SmoothMetric M) (hg : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (Ω K : Set M.Carrier)
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hΩK : Ω ⊆ K)
    (h : ℝ → HermitianField M) {S C α shift : ℝ} (hS : 0 < S)
    (hh : MetricFamilySmooth h (Icc 0 S))
    (B : ℝ → DirichletEnergy g μ hμ Ω →L[ℝ] EnergyDual (DirichletEnergy g μ hμ Ω))
    (hForm : IntrinsicFormBinding g.form μ Ω h S C α shift
      (dirichletL2 g μ hμ Ω) (energyRepresentative g μ hμ Ω) B)
    (f : ℝ → FixedPivot μ Ω) (hf : MemLp f 2 (volume.restrict (Ioo 0 S)))
    (U : ℝ → DirichletEnergy g μ hμ Ω) (R : ℝ → EnergyDual (DirichletEnergy g μ hμ Ω))
    (a : ℝ → FixedPivot μ Ω)
    (hSol : VariationalSolution μ Ω S (dirichletL2 g μ hμ Ω) B f U R a)
    (v : M.Carrier → ℝ → ℝ) (hv : ∀ t, ScalarL2 (μ.restrict Ω) (fun x => v x t))
    (hfActual : ∀ᵐ t ∂volume.restrict (Ioo 0 S), f t = scalarToLp (hv t))
    (c : M.Carrier) {O V : Set (Space n)} (hO : IsOpen O) (hOC : IsCompact (closure O))
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
      (∀ᵐ t ∂volume.restrict (Ioo 0 S),
        (fun z => u (z,t)) =ᵐ[volume.restrict V]
          scalarEnergy_chartRestrictionCLM g μ hμ c hV hVC (hVO.trans (subset_closure.trans hOt))
            (scalarEnergyL2 g μ hμ (U t).val)) := by
  have hVt : closure V ⊆ chartTarget c := hVO.trans (subset_closure.trans hOt)
  obtain ⟨u,G,F,_huM,_hGM,_hFM,huL,hGL,hFL,huE,huEq,hSlices⟩ :=
    variationalSolution_chart_weakEquation g hg μ hμ Ω K hΩ hK hΩK h hS hh B hForm
      f hf U R a hSol c hV hVC hVt hMap
  have hvL : MemLp (fun q : Point n => v (chartInv c q.1) q.2) 2 (productVolume V (Ioo 0 S)) :=
    continuousOn_compactCylinder_memLp hV hVC
      (hvSmooth.continuousOn.mono (prod_mono hVO (Subset.refl _)))
  have hActual := chart_joint_source_eq_physical g μ hμ Ω hΩ.measurableSet c hV hVC hVt hMap
    v hv f hfActual hFL hvL (by
      filter_upwards [hSlices] with t ht
      exact ht.2.2)
  have hWE := weakEquation_source_congr_ae huEq hActual
  have hCoeff := flowChartPrincipal_smooth h hh c
  have hOSub : O ×ˢ Icc (0 : ℝ) S ⊆ chartTarget c ×ˢ Icc 0 S :=
    prod_mono (subset_closure.trans hOt) (Subset.refl _)
  have hSmooth : SmoothCoefficients (O ×ˢ Icc 0 S) (flowChartPrincipal h c) (fun _ _ => 0) :=
    ⟨hCoeff.1.mono hOSub, fun i => (hCoeff.2 i).mono hOSub⟩
  obtain ⟨lam,upper,hEll⟩ := flowChartPrincipal_elliptic h hh c
    (hOC.prod isCompact_Icc) (prod_mono hOt (Subset.refl _))
  have hEllO := elliptic_mono hEll (prod_mono subset_closure (Subset.refl _))
  obtain ⟨uc,p,w,huc,hAE,hPDE,_hp,_hp0,_hpGrowth,_hw,_hwEq,_hAdd⟩ :=
    forced_weak_interior_regularization hn hO hV hVC hVO hS hSmooth hvSmooth hEllO huL hGL huE hWE
  refine ⟨u,uc,huL,huc,hAE,hPDE,?_⟩
  filter_upwards [hSlices] with t ht
  exact ht.1

end Yau.F04Proof
