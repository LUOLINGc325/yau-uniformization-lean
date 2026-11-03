import Yau.Proofs.F04FinitePatchData
import Yau.Proofs.F04SmoothTraceGluing
import Yau.Proofs.F04PatchHeatEquation

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.F04Proof
open Yau.Blueprint Yau.Parabolic Yau.ParabolicCandidates Yau.Proofs.F03Aux
  Yau.MassTargetStatements Yau.LeafProofs.L19Aux
variable {n : ℕ}

local instance (X : KahlerManifold n) (μ : Measure (Pt X))
    (hμ : IsRiemannianVolume X.metric.form μ) (Ω : Set (Pt X)) :
    CompleteSpace (DirichletEnergy X.metric μ hμ Ω) := dirichletEnergy_completeSpace X.metric μ hμ Ω

/-- A genuine finite-domain physical classical potential is constructed
 from the original localized flow. One constant precedes ALL finite
 domains, one original weak trace precedes ALL charts, the true closed
 classical patches are constructed and glued, and the physical PDE holds
 at BOTH time faces. The original weak/form/source witnesses are retained
 for honest exhaustion-domain comparison. -/
theorem flow_uniform_finite_classical_potential
    (hn : 0 < n) (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    {T : ℝ} (hT : 0 < T) (q : Pt X → ℝ) (hq : SmoothFn q)
    (hqRange : ∀ x, 0 ≤ q x ∧ q x ≤ 1) (hcq : HasCompactSupport q) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (Ω K : Set (Pt X)) (hΩ : IsOpen Ω) (hK : IsCompact K) (hΩK : Ω ⊆ K),
      ∃ (B : ℝ → DirichletEnergy X.metric μ hμ Ω →L[ℝ] EnergyDual (DirichletEnergy X.metric μ hμ Ω))
        (C shift : ℝ) (f : ℝ → FixedPivot μ Ω) (uE : ℝ → DirichletEnergy X.metric μ hμ Ω)
        (wE : ℝ → EnergyDual (DirichletEnergy X.metric μ hμ Ω)) (A : ℝ → FixedPivot μ Ω) (v : STF X),
        IntrinsicFormBinding X.metric.form μ Ω h (2*T) C (1/2) shift
          (dirichletL2 X.metric μ hμ Ω) (energyRepresentative X.metric μ hμ Ω) B ∧
        VariationalSolution μ Ω (2*T) (dirichletL2 X.metric μ hμ Ω) B f uE wE A ∧
        (∀ t, (f t : Pt X → ℝ) =ᵐ[μ.restrict Ω]
          (fun x => q x * source X h x (timeClamp (2*T) (by positivity) t))) ∧
        (∀ a, ContDiffOn ℝ ∞ (fun p : Point n => v (chartInv a p.1) p.2)
          ((chartTarget a ∩ chartInv a ⁻¹' Ω) ×ˢ Icc 0 T)) ∧
        (∀ t ∈ Icc 0 T, (fun x => v x t) =ᵐ[μ.restrict Ω] (A t : Pt X → ℝ)) ∧
        (∀ x t, t ∈ Icc 0 T → 0 ≤ v x t ∧ v x t ≤ ρ x t ∧ v x t ≤ M*t) ∧
        (∀ x, v x 0 = 0) ∧ (∀ x ∉ Ω, ∀ t, v x t = 0) ∧
        (∀ x ∈ Ω, ∀ t ∈ Icc 0 T, heatOp h (Icc 0 T) v x t = q x * source X h x t) := by
  classical
  obtain ⟨M,hM,hDomains⟩ := flow_uniform_finite_domain_actual_patches hn X o h U P ρ hloc
    μ hμ hT q hq hqRange hcq
  refine ⟨M,hM,?_⟩
  intro Ω K hΩ hK hΩK
  obtain ⟨B,C,shift,f,uE,wE,A,hForm,hSol,hF,_hAc,_hA0,hPatches⟩ := hDomains Ω K hΩ hK hΩK
  have hLocal (y : Ω) := hPatches y.val y.property
  choose W pv hW hWC hWt hWΩ hz hv hSlice hBound hPDE h0 using hLocal
  let c : Ω → Pt X := fun y => y.val
  have hCover : Ω ⊆ ⋃ i : Ω, scalarChartRegion (c i) (W i) := by
    intro y hy
    apply mem_iUnion.mpr
    refine ⟨⟨y,hy⟩,chartPt y y,hz ⟨y,hy⟩,?_⟩
    exact Yau.LeafProofs.chartInv_chartPt_of_mem y y (mem_chart_source _ _)
  obtain ⟨v,hSmooth,hTrace,hAgree,hOffΩ,_hOffI⟩ := glue_smooth_actual_trace X.metric μ hμ hΩ
    (Icc 0 T) c W hW hWt hWΩ hCover pv hv (fun t x => A t x) hSlice
  have hCoordAgree (i : Ω) : EqOn (fun p : Point n => v (chartInv i.val p.1) p.2) (pv i) (W i ×ˢ Icc 0 T) := by
    intro p hp
    have hy : chartInv i.val p.1 ∈ scalarChartRegion (c i) (W i) := ⟨p.1,hp.1,rfl⟩
    have he := hAgree i _ hy _ hp.2
    change v (chartInv i.val p.1) p.2 = pv i p
    rw [he]
    have hInv : chartPt i.val (chartInv i.val p.1) = p.1 := (extChartAt (ComplexModel n) i.val).right_inv (hWt i hp.1)
    change pv i (chartPt i.val (chartInv i.val p.1),p.2) = pv i p
    rw [hInv]
  have hSelf (x : Pt X) (hx : x ∈ Ω) : x ∈ scalarChartRegion (c ⟨x,hx⟩) (W ⟨x,hx⟩) :=
    ⟨chartPt x x,hz ⟨x,hx⟩,Yau.LeafProofs.chartInv_chartPt_of_mem x x (mem_chart_source _ _)⟩
  refine ⟨B,C,shift,f,uE,wE,A,v,hForm,hSol,hF,hSmooth,hTrace,?_,?_,hOffΩ,?_⟩
  · intro x t ht
    by_cases hx : x ∈ Ω
    · let i : Ω := ⟨x,hx⟩
      rw [hAgree i x (hSelf x hx) t ht]
      have hb : 0 ≤ pv i (chartPt x x,t) ∧
          pv i (chartPt x x,t) ≤ ρ (chartInv x (chartPt x x)) t ∧
          pv i (chartPt x x,t) ≤ M*t := hBound i (chartPt x x,t) ⟨hz i,ht⟩
      rwa [Yau.LeafProofs.chartInv_chartPt_of_mem x x (mem_chart_source _ _)] at hb
    · rw [hOffΩ x hx t]
      exact ⟨le_rfl,rho_nonneg o h U P ρ hloc x t ht.1,mul_nonneg hM ht.1⟩
  · intro x
    by_cases hx : x ∈ Ω
    · rw [hAgree ⟨x,hx⟩ x (hSelf x hx) 0 ⟨le_rfl,hT.le⟩]
      exact h0 ⟨x,hx⟩ (chartPt x x)
    · exact hOffΩ x hx 0
  · intro x hx
    exact flow_heatOp_of_chart_patch X h v (fun x t => q x * source X h x t) x
      (hW ⟨x,hx⟩) (hz ⟨x,hx⟩) (Icc 0 T) (hv ⟨x,hx⟩) (hCoordAgree ⟨x,hx⟩) (hPDE ⟨x,hx⟩)

end Yau.F04Proof
