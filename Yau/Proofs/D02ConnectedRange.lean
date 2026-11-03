import Yau.Proofs.D02NormalFamily
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.Connected.Clopen

/-! Equicontinuity propagates a genuine bounded point range through a
connected domain. Compact sets then have common all-index bounded ranges. -/

open scoped Topology
open Filter Metric Set

noncomputable section
namespace Yau.NodeProofs.D02Aux

theorem equicontinuous_open_unit_neighborhood {D Y ι : Type*}
    [TopologicalSpace D] [PseudoMetricSpace Y] {fs : ι → D → Y}
    (heq : Equicontinuous fs) (x : D) :
    ∃ V : Set D, IsOpen V ∧ x ∈ V ∧ ∀ y ∈ V, ∀ j, dist (fs j x) (fs j y) ≤ 1 := by
  have h := (Metric.equicontinuousAt_iff_right.mp (heq x)) 1 one_pos
  obtain ⟨V, hV, ho, hx⟩ := mem_nhds_iff.mp h
  exact ⟨V, ho, hx, fun y hy j => (hV hy j).le⟩

theorem bounded_point_ranges_of_connected {D Y ι : Type*}
    [TopologicalSpace D] [PreconnectedSpace D] [PseudoMetricSpace Y]
    (fs : ι → D → Y) (heq : Equicontinuous fs) (o : Y)
    (hanchor : ∃ x : D, ∃ B : ℝ, ∀ j, dist (fs j x) o ≤ B) :
    ∀ x : D, ∃ B : ℝ, ∀ j, dist (fs j x) o ≤ B := by
  let S : Set D := {x | ∃ B : ℝ, ∀ j, dist (fs j x) o ≤ B}
  have hopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    rintro x ⟨B, hB⟩
    obtain ⟨V, ho, hx, hV⟩ := equicontinuous_open_unit_neighborhood heq x
    apply mem_of_superset (ho.mem_nhds hx)
    intro y hy
    refine ⟨1 + B, fun j => ?_⟩
    calc
      _ ≤ dist (fs j y) (fs j x) + dist (fs j x) o := dist_triangle _ _ _
      _ ≤ 1 + B := add_le_add (by simpa only [dist_comm] using hV y hy j) (hB j)
  have hcompl : IsOpen Sᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨V, ho, hxV, hV⟩ := equicontinuous_open_unit_neighborhood heq x
    apply mem_of_superset (ho.mem_nhds hxV)
    rintro y hy ⟨B, hB⟩
    apply hx
    refine ⟨1 + B, fun j => ?_⟩
    exact (dist_triangle (fs j x) (fs j y) o).trans (add_le_add (hV y hy j) (hB j))
  have hS : S = univ := (show IsClopen S from ⟨isOpen_compl_iff.mp hcompl, hopen⟩).eq_univ hanchor
  intro x
  exact (show x ∈ S from hS ▸ mem_univ x)

theorem bounded_compact_ranges_of_equicontinuous {D Y ι : Type*}
    [TopologicalSpace D] [PseudoMetricSpace Y]
    (fs : ι → D → Y) (heq : Equicontinuous fs) (o : Y)
    (hpoint : ∀ x : D, ∃ B : ℝ, ∀ j, dist (fs j x) o ≤ B)
    {K : Set D} (hK : IsCompact K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j x, x ∈ K → dist (fs j x) o ≤ B := by
  classical
  choose V hVo hxV hV using equicontinuous_open_unit_neighborhood heq
  choose B hB using hpoint
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover V hVo (fun x _ => mem_iUnion.mpr ⟨x, hxV x⟩)
  let C : ℝ := ∑ x ∈ T, max 0 (1 + B x)
  have hC : 0 ≤ C := Finset.sum_nonneg (fun x _ => le_max_left 0 (1 + B x))
  refine ⟨C, hC, fun j x hx => ?_⟩
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hT hx)
  have hc : max 0 (1 + B y) ≤ C := Finset.single_le_sum
    (fun z _ => le_max_left 0 (1 + B z)) hy
  calc
    _ ≤ dist (fs j x) (fs j y) + dist (fs j y) o := dist_triangle _ _ _
    _ ≤ 1 + B y := add_le_add (by simpa only [dist_comm] using hV y x hxy j) (hB y j)
    _ ≤ C := (le_max_right 0 (1 + B y)).trans hc

end Yau.NodeProofs.D02Aux
