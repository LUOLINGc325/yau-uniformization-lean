import Yau.Proofs.F04ForcedInitialRegularity
import Yau.Proofs.F04ClosedSlabRegularity
import Yau.Proofs.F04LocalChartSmoothness
import Yau.Proofs.F04GlobalChartHeatOperator
import Yau.Proofs.F04FlowChartBounds
import Yau.Proofs.F04FlowSourceSmooth
import Yau.Proofs.F04PhysicalClosedEquation
import Yau.Proofs.F04InteriorChartBuffers

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.F04Proof
open Yau.Blueprint Yau.Parabolic Yau.ParabolicCandidates Yau.LeafProofs.L16Aux

/-- An ACTUAL global forced classical function below the supplied rho
 acquires genuine one-sided smoothness at its zero initial face. Compact
 growth is derived from rho, particular solutions are constructed, and
 only the homogeneous remainders cross zero. Terminal times lie inside
 the original larger horizon. -/
theorem flow_dominated_initial_regularization
    {n : ℕ} (hn : 0 < n) (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) {S T : ℝ} (hS : 0 < S) (hT : 0 < T) (hTS : T < S)
    (q : Pt X → ℝ) (hq : SmoothFn q) (v : STF X)
    (hv : SmoothSpaceTime v (Ioo 0 S)) (hv0 : ∀ x, v x 0 = 0)
    (hBound : ∀ x t, t ∈ Ioo 0 S → 0 ≤ v x t ∧ v x t ≤ ρ x t)
    (hPDE : ∀ x t, t ∈ Ioo 0 S → heatOp h (Icc 0 S) v x t = q x * source X h x t) :
    SmoothSpaceTime v (Icc 0 T) ∧
      ∀ x t, t ∈ Icc 0 T → heatOp h (Icc 0 T) v x t = q x * source X h x t := by
  have hh : MetricFamilySmooth h (Icc 0 S) := fun c i j => (hloc.1.2.1 c i j).mono
    (Set.prod_mono (Subset.refl _) (fun _ ht => ht.1))
  have hF := flow_cutoff_source_smooth_closed X o h U P ρ hloc hS q hq
  have hClosed : SmoothSpaceTime v (Icc 0 T) := by
    apply smoothSpaceTime_of_local_center_charts
    intro c
    obtain ⟨O,V,W,hO,hOC,hOt,_hMap,_hV,_hVC,hVO,_hW,_hWC,hWV,hCenter⟩ :=
      exists_interior_chart_buffers (M := X.manifold) isOpen_univ c (mem_univ c)
    have hCenterO : chartPt c c ∈ O := hVO (subset_closure (hWV (subset_closure hCenter)))
    have hAB : SmoothCoefficients (O ×ˢ Icc 0 S) (flowChartPrincipal h c) (fun _ _ => 0) :=
      ⟨(flowChartPrincipal_smooth h hh c).1.mono (Set.prod_mono (subset_closure.trans hOt) (Subset.refl _)),
        fun _ => contDiffOn_const⟩
    obtain ⟨lam,upper,hEll⟩ := flowChartPrincipal_elliptic h hh c (hOC.prod isCompact_Icc)
      (Set.prod_mono hOt (Subset.refl _))
    have hEllO := elliptic_mono hEll (Set.prod_mono subset_closure (Subset.refl (Icc (0 : ℝ) S)))
    let uc : Point n → ℝ := fun p => v (chartInv c p.1) p.2
    have hu : ContDiffOn ℝ ∞ uc (O ×ˢ Ioo 0 S) :=
      (hv c).mono (Set.prod_mono (subset_closure.trans hOt) (Subset.refl _))
    have hf : ContDiffOn ℝ ∞ (fun p : Point n => q (chartInv c p.1) * source X h (chartInv c p.1) p.2)
        (O ×ˢ Icc 0 S) :=
      (hF c).mono (Set.prod_mono (subset_closure.trans hOt) (Subset.refl _))
    have hEq : ∀ p ∈ O ×ˢ Ioo 0 S,
        linearOp (O ×ˢ Icc 0 S) (flowChartPrincipal h c) (fun _ _ => 0) uc p =
          q (chartInv c p.1) * source X h (chartInv c p.1) p.2 := by
      intro p hp
      have hs : SmoothFn (fun x => v x p.2) := fun a => (hv a).comp
        (contDiffOn_id.prodMk contDiffOn_const) (fun z hz => ⟨hz,hp.2⟩)
      rw [← flow_heatOp_fixed_chart X h v c hp.1 (hOt (subset_closure hp.1)) (Icc 0 S) p.2 hs]
      exact hPDE _ _ hp.2
    have hGrowth := flow_chart_rho_dominated_compact_growth X o h U P ρ hloc hS c
      (O := O) (subset_closure.trans hOt) (fun p hp => hBound _ _ hp.2)
    have hInitial : ∀ Z : Set (Space n), IsOpen Z → IsCompact (closure Z) → closure Z ⊆ O →
        ∃ s : ℝ, 0 < s ∧ s < S ∧ ContDiffOn ℝ ∞ (zeroPast uc) (Z ×ˢ Icc 0 s) := by
      intro Z hZ hZC hZO
      exact forced_linearGrowth_initial_regularization hn hO hS hAB hf hEllO hu hEq hGrowth Z hZ hZC hZO
    have hz := contDiffOn_closedSlab_of_local_initial hO hTS hu hInitial
    refine ⟨O,hO,hCenterO,subset_closure.trans hOt,?_⟩
    apply hz.congr
    intro p hp
    by_cases ht : 0 < p.2
    · rw [zeroPast_of_pos uc ht]
    · have hp0 : p.2 = 0 := le_antisymm (le_of_not_gt ht) hp.2.1
      rw [zeroPast_of_nonpos uc (le_of_not_gt ht)]
      change v (chartInv c p.1) p.2 = 0
      rw [hp0,hv0]
  refine ⟨hClosed,?_⟩
  have hhT : MetricFamilySmooth h (Icc 0 T) := fun c i j => (hh c i j).mono
    (Set.prod_mono (Subset.refl _) (Icc_subset_Icc le_rfl hTS.le))
  apply physical_forced_equation_closed_of_positive X h hT hhT hClosed
    (flow_cutoff_source_smooth_closed X o h U P ρ hloc hT q hq)
  intro x t ht
  have he := hPDE x t ⟨ht.1,ht.2.trans hTS⟩
  unfold heatOp at he ⊢
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
  rwa [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 (ht.2.trans hTS))] at he

end Yau.F04Proof
