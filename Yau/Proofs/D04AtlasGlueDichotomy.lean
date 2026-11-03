import Yau.Proofs.D04AtlasGlueTopology
import Yau.Proofs.D04AtlasGlueSequence

open MeasureTheory Filter Set
open scoped Topology Manifold ENNReal

noncomputable section

namespace Yau.Proofs.D04AtlasGlueAux

open Yau Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}

def ChartBall.domain (B : ChartBall M) : Set (ComplexVector n) :=
  Metric.ball (chartPt B.center B.center) (2 * B.radius)

theorem global_collapse_of_chart_collapses
    (B : ℕ → ChartBall M) (hB : (⋃ i, (B i).inner) = univ)
    {us : ℕ → M.Carrier → EReal} {φ : ℕ → ℕ}
    (hcollapse : ∀ i, CollapsesOn (B i).outer us φ) : ManifoldPshCollapse us φ := by
  intro K hK A
  obtain ⟨I, hI⟩ := finite_chartBall_cover B hB hK
  have hall : ∀ᶠ j in atTop, ∀ i ∈ I, ∀ x ∈ K ∩ (B i).core,
      us (φ j) x ≤ ((-A : ℝ) : EReal) := by
    apply (eventually_all_finset I).mpr
    intro i hi
    obtain ⟨N, hN⟩ := hcollapse i (K ∩ (B i).core)
      (hK.inter_right (B i).isCompact_core.isClosed)
      (inter_subset_right.trans (B i).core_subset_outer) A
    exact eventually_atTop.mpr ⟨N, hN⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hall
  refine ⟨N, ?_⟩
  intro j hj x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hI hx)
  obtain ⟨hiI, hxi⟩ := mem_iUnion.mp hi
  exact hN j hj i hiI x ⟨hx, (B i).inner_subset_core hxi⟩

/-- Connectedness excludes a mixture of collapse and finite local-limit
branches. The retained chart balls cover the whole manifold. -/
theorem chart_branches_dichotomy
    (g : HermitianField M) (hg : MetricSmooth g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g μ)
    (B : ℕ → ChartBall M) (hB : (⋃ i, (B i).inner) = univ)
    (Ωs : ℕ → Set M.Carrier) (us : ℕ → M.Carrier → EReal)
    (hΩ : ∀ j, IsOpen (Ωs j) ∧ Ωs j ⊆ Ωs (j + 1))
    (hcover : (⋃ j, Ωs j) = univ)
    (hpsh : ∀ j, PshOnManifold (us j) (Ωs j))
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hbranches : ∀ i,
      PshCollapses (B i).domain (fun j z => us j (chartInv (B i).center z)) φ ∨
      PshL1Limit (B i).domain (fun j z => us j (chartInv (B i).center z)) φ) :
    ManifoldPshCollapse us φ ∨ ∀ i, Nonempty (ChartLimit μ (B i).center (B i).domain us φ) := by
  classical
  have hbranchesM (i : ℕ) : CollapsesOn (B i).outer us φ ∨
      Nonempty (ChartLimit μ (B i).center (B i).domain us φ) := by
    rcases hbranches i with hc | hl
    · exact Or.inl (collapsesOn_of_coordinate (B i).center (B i).outer_subset_target hc)
    · exact Or.inr (chartLimit_of_coordinate_limit g hg μ hμ (B i).center
        Metric.isOpen_ball (B i).outer_subset_target Ωs us hΩ hcover hpsh hφ hl)
  let P : ℕ → Prop := fun i => CollapsesOn (B i).outer us φ
  by_cases hall : ∀ i, P i
  · exact Or.inl (global_collapse_of_chart_collapses B hB hall)
  right
  push_neg at hall
  obtain ⟨i₀, hi₀⟩ := hall
  let G := ⋃ i, ⋃ (_ : ¬ P i), (B i).outer
  let H := ⋃ i, ⋃ (_ : P i), (B i).outer
  have hG : IsOpen G := isOpen_iUnion (fun i => isOpen_iUnion (fun _ => (B i).isOpen_outer))
  have hH : IsOpen H := isOpen_iUnion (fun i => isOpen_iUnion (fun _ => (B i).isOpen_outer))
  have hdisj : Disjoint G H := by
    apply Set.disjoint_left.mpr
    intro x hxG hxH
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxG
    obtain ⟨hiP, hxi⟩ := mem_iUnion.mp hi
    obtain ⟨j, hj⟩ := mem_iUnion.mp hxH
    obtain ⟨hjP, hxj⟩ := mem_iUnion.mp hj
    obtain ⟨L⟩ := (hbranchesM i).resolve_left hiP
    exact Set.disjoint_left.mp
      (collapse_limit_overlap_empty g hg μ hμ Ωs us hΩ hcover hpsh hφ
        (B j).isOpen_outer hjP (B i).center Metric.isOpen_ball (B i).outer_subset_target L)
      hxj hxi
  have hcoverGH : univ ⊆ G ∪ H := by
    intro x _
    have hx : x ∈ ⋃ i, (B i).inner := by rw [hB]; exact mem_univ x
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    have hxW := (B i).core_subset_outer ((B i).inner_subset_core hxi)
    by_cases hi : P i
    · exact Or.inr (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hxW⟩⟩)
    · exact Or.inl (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hxW⟩⟩)
  have hGne : (univ ∩ G).Nonempty := by
    refine ⟨(B i₀).center, mem_univ _, mem_iUnion.mpr ⟨i₀, mem_iUnion.mpr ⟨hi₀, ?_⟩⟩⟩
    exact (B i₀).core_subset_outer ((B i₀).inner_subset_core (B i₀).center_mem_inner)
  have hGuniv : univ ⊆ G :=
    isPreconnected_univ.subset_left_of_subset_union hG hH hdisj hcoverGH hGne
  intro i
  apply (hbranchesM i).resolve_left
  intro hi
  have hxH : (B i).center ∈ H :=
    mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi,
      (B i).core_subset_outer ((B i).inner_subset_core (B i).center_mem_inner)⟩⟩
  exact Set.disjoint_left.mp hdisj (hGuniv (mem_univ _)) hxH

end Yau.Proofs.D04AtlasGlueAux
