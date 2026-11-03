import Yau.Proofs.D04AtlasGlueDichotomy
import Yau.Proofs.D04AtlasGlueAllCharts
import Yau.Proofs.D04AtlasAssembly

open MeasureTheory Filter Set
open scoped Topology Manifold ENNReal

noncomputable section

namespace Yau.Proofs.D04AtlasGlueAux

open Yau Yau.Blueprint

/-- The original coordinate bridge implies the complete original manifold
bridge for the volume of a smooth Hermitian field. All original domains,
chart tests, EReal errors, and both lower-anchor clauses are retained. -/
theorem manifold_bridge_of_coordinate_bridge {n : ℕ}
    (hcoord : Yau.Blueprint.PshCompactnessBridge n)
    (M : ComplexManifold n) (g : HermitianField M)
    (hg : MetricSmooth g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g μ) :
    Yau.Blueprint.ManifoldPshCompactnessBridge M μ := by
  classical
  intro Ωs us hΩ hcover hpsh hupper
  obtain ⟨B, hB⟩ := exists_countable_chartBalls M
  obtain ⟨φ, hφ, hbranches⟩ := exists_simultaneous_chart_branches hcoord B
    Ωs us hΩ hcover hpsh hupper
  refine ⟨φ, hφ, ?_, ?_, ?_⟩
  · rcases chart_branches_dichotomy g hg μ hμ B hB Ωs us hΩ hcover hpsh hφ hbranches
      with hcollapse | hlimits
    · exact Or.inl hcollapse
    right
    let L : ∀ i, ChartLimit μ (B i).center (B i).domain us φ :=
      fun i => Classical.choice (hlimits i)
    have hagree (i j : ℕ) : EqOn (L i).value (L j).value ((B i).outer ∩ (B j).outer) :=
      chartLimits_agree g hg μ hμ Ωs us hΩ hcover hpsh hφ
        (B i).center (B j).center Metric.isOpen_ball (B i).outer_subset_target
        Metric.isOpen_ball (B j).outer_subset_target (L i) (L j)
    obtain ⟨u, husc, hu, hfinite, heq, hlocal, hhartogs⟩ :=
      D04Aux.assemble_manifold_psh_limits μ
        (fun i => (B i).inner) (fun i => (B i).core) (fun i => (B i).outer)
        (fun i => (B i).isOpen_inner) (fun i => (B i).isCompact_core)
        (fun i => (B i).inner_subset_core) (fun i => (B i).core_subset_outer)
        (fun i => (B i).isOpen_outer) hB
        (fun i => (L i).value) (fun i => (L i).usc) (fun i => (L i).lt_top)
        hagree (fun i => ((L i).finite (B i).core (B i).isCompact_core
          (B i).core_subset_outer).mono (fun _ hx => hx.1)) us φ
        (fun i K hK hKW => ⟨(L i).integrable K hK hKW, (L i).convergence K hK hKW⟩)
        (fun i => (L i).hartogs)
    have hselected : ∀ x : M.Carrier, ∃ (a : M.Carrier) (D : Set (ComplexVector n)),
        IsOpen D ∧ D ⊆ chartTarget a ∧ x ∈ chartInv a '' D ∧
          IsPshOn (fun z => u (chartInv a z)) D := by
      intro x
      have hx : x ∈ ⋃ i, (B i).inner := by rw [hB]; exact mem_univ x
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      refine ⟨(B i).center, (B i).domain, Metric.isOpen_ball, (B i).outer_subset_target,
        (B i).core_subset_outer ((B i).inner_subset_core hxi), ?_⟩
      apply isPshOn_congr (L i).psh
      intro z hz
      exact heq i (mem_image_of_mem _ hz)
    have hupsh := isPsh_of_selected_atlas_limit hcoord g hg μ hμ Ωs us hΩ hcover hpsh hupper
      hφ hu husc hfinite (fun K hK => (hlocal K hK).2) hselected
    obtain ⟨K, hK, _, hKpos⟩ := exists_compact_positive_subset g hg μ hμ
      isOpen_univ (Set.univ_nonempty : (univ : Set M.Carrier).Nonempty)
    obtain ⟨x, _, hx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hKpos.ne'
      (ae_restrict_of_ae hfinite)
    exact ⟨u, hupsh, ⟨x, hx⟩, hfinite, hlocal, hhartogs⟩
  · intro K z A hK hz
    exact D04Aux.not_collapse_of_point_anchor hK
      (fun j => ⟨(hz j).1, (hz j).2.2⟩)
  · intro K Es A c hK hc hEs
    exact D04Aux.not_collapse_of_positive_measure_anchor μ hK hc
      (fun j => ⟨(hEs j).2.1.trans inter_subset_left, (hEs j).2.2.1, (hEs j).2.2.2⟩)

end Yau.Proofs.D04AtlasGlueAux
