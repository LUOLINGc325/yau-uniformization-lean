import Yau.Proofs.F04FiniteUniformPotential
import Yau.Proofs.F04EveryTimeChartSlice
import Yau.Proofs.F04InteriorChartBuffers
import Yau.Proofs.F04ClosedSlabRegularity
import Yau.Proofs.F04ClosedEquation
import Yau.Proofs.F04ChartOperatorLocality

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.F04Proof
open Yau.Blueprint Yau.Parabolic Yau.ParabolicCandidates Yau.Proofs.F03Aux
  Yau.MassTargetStatements Yau.LeafProofs.L19Aux Yau.LeafProofs.L16Aux
variable {n : ℕ}

local instance (X : KahlerManifold n) (μ : Measure (Pt X))
    (hμ : IsRiemannianVolume X.metric.form μ) (Ω : Set (Pt X)) :
    CompleteSpace (DirichletEnergy X.metric μ hμ Ω) := dirichletEnergy_completeSpace X.metric μ hμ Ω

/-- Actual closed classical patches of ONE original continuous supported
 trace, with exact forcing and a uniform constant BEFORE all finite
 domains. All local data, every-time trace identities, initial-face and
 endpoint equations are constructed, not supplied as patch assumptions. The ORIGINAL form, weak solution and actual source representatives are retained for later domain comparison. -/
theorem flow_uniform_finite_domain_actual_patches
    (hn : 0 < n) (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    {T : ℝ} (hT : 0 < T) (q : Pt X → ℝ) (hq : SmoothFn q)
    (hqRange : ∀ x, 0 ≤ q x ∧ q x ≤ 1) (hcq : HasCompactSupport q) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (Ω K : Set (Pt X)) (hΩ : IsOpen Ω) (hK : IsCompact K) (hΩK : Ω ⊆ K),
      ∃ (B : ℝ → DirichletEnergy X.metric μ hμ Ω →L[ℝ] EnergyDual (DirichletEnergy X.metric μ hμ Ω))
        (C shift : ℝ) (f : ℝ → FixedPivot μ Ω) (uE : ℝ → DirichletEnergy X.metric μ hμ Ω)
        (wE : ℝ → EnergyDual (DirichletEnergy X.metric μ hμ Ω)) (A : ℝ → FixedPivot μ Ω),
        IntrinsicFormBinding X.metric.form μ Ω h (2*T) C (1/2) shift
          (dirichletL2 X.metric μ hμ Ω) (energyRepresentative X.metric μ hμ Ω) B ∧
        VariationalSolution μ Ω (2*T) (dirichletL2 X.metric μ hμ Ω) B f uE wE A ∧
        (∀ t, (f t : Pt X → ℝ) =ᵐ[μ.restrict Ω]
          (fun x => q x * source X h x (timeClamp (2*T) (by positivity) t))) ∧
        ContinuousOn A (Icc 0 T) ∧ A 0 = 0 ∧
      ∀ x ∈ Ω, ∃ (W : Set (Space n)) (v : Point n → ℝ),
        IsOpen W ∧ IsCompact (closure W) ∧ W ⊆ chartTarget x ∧ chartInv x '' W ⊆ Ω ∧
        chartPt x x ∈ W ∧ ContDiffOn ℝ ∞ v (W ×ˢ Icc 0 T) ∧
        (∀ t ∈ Icc 0 T, (fun z => v (z,t)) =ᵐ[volume.restrict W] (fun z => A t (chartInv x z))) ∧
        (∀ p ∈ W ×ˢ Icc 0 T, 0 ≤ v p ∧ v p ≤ ρ (chartInv x p.1) p.2 ∧ v p ≤ M*p.2) ∧
        (∀ p ∈ W ×ˢ Icc 0 T,
          linearOp (W ×ˢ Icc 0 T) (flowChartPrincipal h x) (fun _ _ => 0) v p =
            q (chartInv x p.1) * source X h (chartInv x p.1) p.2) ∧
        (∀ z, v (z,0) = 0) := by
  have h2T : 0 < 2*T := mul_pos (by norm_num) hT
  have hT2T : T < 2*T := by linarith
  obtain ⟨M,hM,hDomains⟩ := flow_finite_domain_cutoff_potential_uniform_bound hn X o h U P ρ hloc
    μ hμ h2T q hq hqRange hcq
  refine ⟨M,hM,?_⟩
  intro Ω K hΩ hK hΩK
  obtain ⟨hv,B,C,shift,uE,wE,A,hForm,hSol,hCharts⟩ := hDomains Ω K hΩ hK hΩK
  refine ⟨B,C,shift,(fun t => scalarToLp (hv t)),uE,wE,A,hForm,hSol,?_,
    hSol.2.2.1.mono (Icc_subset_Icc le_rfl hT2T.le),hSol.2.2.2.1,?_⟩
  · intro t
    exact scalarToLp_coe (hv t)
  · intro x hx
    obtain ⟨O,V,W,hO,hOC,hOt,hMapO,hV,hVC,hVO,hW,hWC,hWV,hxW⟩ := exists_interior_chart_buffers hΩ x hx
    have hMapV : chartInv x '' V ⊆ Ω := by
      rintro y ⟨z,hz,rfl⟩
      exact hMapO ⟨z,hVO (subset_closure hz),rfl⟩
    have hMapW : chartInv x '' W ⊆ Ω := by
      rintro y ⟨z,hz,rfl⟩
      exact hMapV ⟨z,hWV (subset_closure hz),rfl⟩
    obtain ⟨u,uc,huL,huc,hAE,hPDE,hBounds,hLinear,hSlices,hInitial⟩ := hCharts x O V hO hOC hOt hV hVC hVO hMapV
    have hVt : closure V ⊆ chartTarget x := hVO.trans (subset_closure.trans hOt)
    have hWt : W ⊆ chartTarget x := subset_closure.trans (hWV.trans (subset_closure.trans hVt))
    have hClosed := contDiffOn_closedSlab_of_local_initial hV hT2T huc hInitial
    have hTrace := supported_chart_smoothSlice_closed_of_joint X.metric μ hμ Ω hΩ.measurableSet x
      hV hVC hVt hW hWC hWV hMapW hT2T uE A (hSol.2.2.1.mono Ioo_subset_Icc_self)
      hSol.2.2.2.1 huc hAE hSlices hSol.2.2.2.2.1
    let v := zeroPast uc
    have hvClosed : ContDiffOn ℝ ∞ v (W ×ˢ Icc 0 T) :=
      hClosed.mono (prod_mono (subset_closure.trans hWV) (Subset.refl _))
    have hEqPos : ∀ p ∈ W ×ˢ Ioo 0 T,
        linearOp (W ×ˢ Icc 0 T) (flowChartPrincipal h x) (fun _ _ => 0) v p =
          q (chartInv x p.1) * source X h (chartInv x p.1) p.2 := by
      intro p hp
      have he : EqOn v uc (W ×ˢ Ioo 0 T) := fun z hz => zeroPast_of_pos uc hz.2.1
      rw [linearOp_product_time_eq hp.1 hp.1 (Icc_mem_nhds hp.2.1 hp.2.2) (isOpen_Ioo.mem_nhds hp.2),
        linearOp_congr_product_of_eqOn hW he hp,
        linearOp_product_time_eq hp.1 (hWV (subset_closure hp.1)) (isOpen_Ioo.mem_nhds hp.2)
          (Icc_mem_nhds hp.2.1 (hp.2.2.trans hT2T))]
      exact hPDE p ⟨hWV (subset_closure hp.1),hp.2.1,hp.2.2.trans hT2T⟩
    have hh : MetricFamilySmooth h (Icc 0 T) := fun c i j =>
      (hloc.1.2.1 c i j).mono (prod_mono (Subset.refl _) (fun _ ht => ht.1))
    have hc := flowChartPrincipal_smooth h hh x
    have hSV : SmoothCoefficients (W ×ˢ Icc 0 T) (flowChartPrincipal h x) (fun _ _ => 0) :=
      ⟨hc.1.mono (prod_mono hWt (Subset.refl _)),fun i => (hc.2 i).mono (prod_mono hWt (Subset.refl _))⟩
    have hFC := (flow_cutoff_source_smooth_closed X o h U P ρ hloc hT q hq x).continuousOn.mono
      (prod_mono hWt (Subset.refl _))
    have hEqClosed := forced_equation_closed_of_positive hW hT hSV hvClosed hFC hEqPos
    refine ⟨W,v,hW,hWC,hWt,hMapW,hxW,hvClosed,hTrace,?_,hEqClosed,?_⟩
    · intro p hp
      by_cases ht : 0 < p.2
      · have hpV : p ∈ V ×ˢ Ioo 0 (2*T) :=
          ⟨hWV (subset_closure hp.1),ht,hp.2.2.trans_lt hT2T⟩
        rw [show v p = uc p from zeroPast_of_pos uc ht]
        exact ⟨(hBounds p hpV).1,(hBounds p hpV).2,hLinear p hpV⟩
      · have ht0 : p.2 = 0 := le_antisymm (le_of_not_gt ht) hp.2.1
        rw [show v p = 0 from zeroPast_of_nonpos uc (le_of_not_gt ht),ht0,
          rho_initial o h U P ρ hloc,mul_zero]
        exact ⟨le_rfl,le_rfl,le_rfl⟩
    · intro z
      exact zeroPast_of_nonpos uc le_rfl

end Yau.F04Proof
