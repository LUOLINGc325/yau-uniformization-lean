import Yau.Proofs.F04BoundedForcedLimit
import Yau.Proofs.F04LocalChartSmoothness
import Yau.Proofs.F04GlobalChartHeatOperator
import Yau.Proofs.F04PhysicalChartOperator
import Yau.Proofs.F04FlowSourceSmooth
import Yau.Proofs.F04InteriorChartBuffers
import Yau.Proofs.F04ChartEllipticity

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.F04Proof
open Yau.Blueprint Yau.Parabolic Yau.ParabolicCandidates Yau.LeafProofs.L16Aux

/-- If actual cutoff sources are eventually EXACTLY the full source on
 every compact, the rho-dominated pointwise limit of their actual global
 classical solutions solves the ACTUAL full-source equation smoothly at
 positive time. Compact rho bounds supply the uniform bound before N2;
 no source-uniform global Mt bound is assumed. -/
theorem flow_cutoff_potential_limit_positive_regularization
    {n : ℕ} (hn : 0 < n) (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) {S : ℝ} (hS : 0 < S)
    (qs : ℕ → Pt X → ℝ)
    (hCut : ∀ K : Set (Pt X), IsCompact K → ∃ J : ℕ, ∀ j ≥ J, ∀ x ∈ K, qs j x = 1)
    (v : ℕ → STF X) (z : STF X)
    (hv : ∀ j, SmoothSpaceTime (v j) (Ioo 0 S))
    (hPDE : ∀ j x t, t ∈ Ioo 0 S → heatOp h (Icc 0 S) (v j) x t = qs j x * source X h x t)
    (hBound : ∀ j x t, t ∈ Ioo 0 S → 0 ≤ v j x t ∧ v j x t ≤ ρ x t)
    (hTend : ∀ x t, t ∈ Ioo 0 S → Tendsto (fun j => v j x t) atTop (𝓝 (z x t))) :
    SmoothSpaceTime z (Ioo 0 S) ∧
      ∀ x t, t ∈ Ioo 0 S → heatOp h (Icc 0 S) z x t = source X h x t := by
  have hh : MetricFamilySmooth h (Icc 0 S) := fun c i j => (hloc.1.2.1 c i j).mono
    (Set.prod_mono (Subset.refl _) (fun _ ht => ht.1))
  have hF := flow_source_smooth_closed X o h U P ρ hloc hS
  have hρ : SmoothSpaceTime ρ (Icc 0 S) := fun c => (hloc.2.2.2.1 c).mono
    (Set.prod_mono (Subset.refl _) (fun _ ht => ht.1))
  have hLocal (c : Pt X) : ∃ V : Set (Space n), IsOpen V ∧ chartPt c c ∈ V ∧ V ⊆ chartTarget c ∧
      ContDiffOn ℝ ∞ (fun p : Point n => z (chartInv c p.1) p.2) (V ×ˢ Ioo 0 S) ∧
      ∀ p ∈ V ×ˢ Ioo 0 S,
        linearOp (V ×ˢ Icc 0 S) (flowChartPrincipal h c) (fun _ _ => 0)
          (fun r : Point n => z (chartInv c r.1) r.2) p = source X h (chartInv c p.1) p.2 := by
    obtain ⟨O,V,W,hO,hOC,hOt,_hMap,_hV,_hVC,hVO,_hW,_hWC,hWV,hCenter⟩ :=
      exists_interior_chart_buffers (M := X.manifold) isOpen_univ c (mem_univ c)
    have hCenterO : chartPt c c ∈ O := hVO (subset_closure (hWV (subset_closure hCenter)))
    have hKC : IsCompact (chartInv c '' closure O) := hOC.image_of_continuousOn
      ((continuousOn_extChartAt_symm (I := ComplexModel n) c).mono hOt)
    obtain ⟨J,hJ⟩ := hCut (chartInv c '' closure O) hKC
    let ui : ℕ → Point n → ℝ := fun j p => v (j+J) (chartInv c p.1) p.2
    have hUi (j : ℕ) : ContDiffOn ℝ ∞ (ui j) (O ×ˢ Ioo 0 S) :=
      (hv (j+J) c).mono (Set.prod_mono (subset_closure.trans hOt) (Subset.refl _))
    have hUiPDE (j : ℕ) (p : Point n) (hp : p ∈ O ×ˢ Ioo 0 S) :
        linearOp (O ×ˢ Icc 0 S) (flowChartPrincipal h c) (fun _ _ => 0) (ui j) p =
          source X h (chartInv c p.1) p.2 := by
      have hs : SmoothFn (fun x => v (j+J) x p.2) := fun a => (hv (j+J) a).comp
        (contDiffOn_id.prodMk contDiffOn_const) (fun x hx => ⟨hx,hp.2⟩)
      rw [← flow_heatOp_fixed_chart X h (v (j+J)) c hp.1 (hOt (subset_closure hp.1)) (Icc 0 S) p.2 hs,
        hPDE (j+J) _ _ hp.2,hJ (j+J) (by omega) _ (mem_image_of_mem _ (subset_closure hp.1)),one_mul]
    obtain ⟨B,hB,hRb⟩ := compact_scalar_profile_bound hS.le ρ (smoothSpaceTime_continuousOn hρ)
      (chartInv c '' closure O) hKC
    have hUiBound (j : ℕ) (p : Point n) (hp : p ∈ O ×ˢ Ioo 0 S) : |ui j p| ≤ B := by
      have hb := hBound (j+J) (chartInv c p.1) p.2 hp.2
      have hr := hRb (chartInv c p.1) (mem_image_of_mem _ (subset_closure hp.1)) p.2
      rw [timeClamp_eq_of_mem S hS.le (Ioo_subset_Icc_self hp.2),Real.norm_eq_abs] at hr
      rw [abs_of_nonneg hb.1]
      exact hb.2.trans ((le_abs_self _).trans hr)
    have hUiPoint (p : Point n) (hp : p ∈ O ×ˢ Ioo 0 S) :
        Tendsto (fun j => ui j p) atTop (𝓝 (z (chartInv c p.1) p.2)) :=
      (hTend _ _ hp.2).comp (tendsto_add_atTop_nat J)
    have hAB : SmoothCoefficients (O ×ˢ Icc 0 S) (flowChartPrincipal h c) (fun _ _ => 0) :=
      ⟨(flowChartPrincipal_smooth h hh c).1.mono (Set.prod_mono (subset_closure.trans hOt) (Subset.refl _)),
        fun _ => contDiffOn_const⟩
    have hf := (hF c).mono (Set.prod_mono (subset_closure.trans hOt) (Subset.refl (Icc (0 : ℝ) S)))
    obtain ⟨lam,upper,hEll⟩ := flowChartPrincipal_elliptic h hh c (hOC.prod isCompact_Icc)
      (Set.prod_mono hOt (Subset.refl _))
    obtain ⟨Z,hZ,_hZC,hCenterZ,hZO,hReg,hEq⟩ := bounded_classical_forced_limit_local hn hO hOC
      {chartPt c c} isCompact_singleton (singleton_subset_iff.mpr hCenterO) hS hAB hf
      (elliptic_mono hEll (Set.prod_mono subset_closure (Subset.refl (Icc (0 : ℝ) S)))) ui
      (fun p : Point n => z (chartInv c p.1) p.2) hB hUi hUiPDE hUiBound hUiPoint
    exact ⟨Z,hZ,hCenterZ (mem_singleton _),subset_closure.trans (hZO.trans (subset_closure.trans hOt)),hReg,hEq⟩
  have hz : SmoothSpaceTime z (Ioo 0 S) := by
    apply smoothSpaceTime_of_local_center_charts
    intro c
    obtain ⟨V,hV,hCenter,hVt,hReg,_hEq⟩ := hLocal c
    exact ⟨V,hV,hCenter,hVt,hReg⟩
  refine ⟨hz,?_⟩
  intro x t ht
  obtain ⟨V,hV,hCenter,_hVt,hReg,hEq⟩ := hLocal x
  have hs : ContDiffOn ℝ ∞ (inChart x (fun y => z y t)) V :=
    hReg.comp (contDiffOn_id.prodMk contDiffOn_const) (fun a ha => ⟨ha,ht⟩)
  have hC2 : ContDiffAt ℝ 2 (inChart x (fun y => z y t)) (chartPt x x) :=
    (hs.contDiffAt (hV.mem_nhds hCenter)).of_le (by simp)
  rw [flow_heatOp_chart_center X h z x hCenter (Icc 0 S) t hC2]
  have he := hEq (chartPt x x,t) ⟨hCenter,ht⟩
  rwa [Yau.LeafProofs.chartInv_chartPt_of_mem x x (mem_chart_source _ _)] at he

end Yau.F04Proof
