import Yau.LeafProofs.L16BoundaryPhysicalData

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic

/-- A genuine smooth boundary-chart buffer for a physical cutoff patch. -/
def boundaryChartBuffer {n : ℕ} (O : Set (Space n)) (x : Space n) (r : ℝ) : Prop :=
  ∃ (e : Space n) (c : OpenPartialHomeomorph (Space n) (Space n)) (q : ℝ),
    ‖e‖ = 1 ∧ 0 < q ∧ Metric.closedBall x (4*r) ⊆ c.source ∧
    MapsTo c (Metric.closedBall x (4*r)) (Metric.ball (0 : Space n) (q/2)) ∧
    Metric.closedBall (0 : Space n) (4*q) ⊆ c.target ∧
    ContDiffOn ℝ 3 c c.source ∧ ContDiffOn ℝ 3 c.symm c.target ∧
    ∀ y ∈ c.source, (y ∈ O ↔ 0 < inner ℝ e (c y)) ∧
      (y ∈ closure O ↔ 0 ≤ inner ℝ e (c y)) ∧ (y ∈ frontier O ↔ inner ℝ e (c y) = 0)

theorem boundaryChartBuffer_mono_ball {n : ℕ} {O : Set (Space n)} {x y : Space n} {r R : ℝ}
    (h : boundaryChartBuffer O x R)
    (hBall : Metric.closedBall y (4*r) ⊆ Metric.closedBall x (4*R)) :
    boundaryChartBuffer O y r := by
  obtain ⟨e,c,q,he,hq,hSource,hImage,hTarget,hc,hci,hFaces⟩ := h
  exact ⟨e,c,q,he,hq,hBall.trans hSource,fun z hz => hImage (hBall hz),hTarget,hc,hci,hFaces⟩

/-- Compactness fixes one physical patch scale whose fourfold buffers
    fit inside one of finitely many originally supplied genuine buffers. -/
theorem compact_uniform_buffered_ball_assignment {n : ℕ} {K : Set (Space n)} (hK : IsCompact K)
    (R : K → ℝ) (hR : ∀ i, 0 < R i) :
    ∃ (r : ℝ) (J : Finset K), 0 < r ∧ r ≤ 1 ∧ ∀ x ∈ K,
      ∃ i ∈ J, Metric.closedBall x (4*r) ⊆ Metric.closedBall (i : Space n) (4*R i) := by
  classical
  obtain ⟨J,hCover⟩ := hK.elim_finite_subcover (fun i : K => Metric.ball (i : Space n) (R i))
    (fun _ => Metric.isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x,hx⟩,Metric.mem_ball_self (hR ⟨x,hx⟩)⟩)
  let I : ℝ := ∑ i ∈ J, (R i)⁻¹
  let d : ℝ := 1/(1+I)
  let r : ℝ := d/4
  have hI : 0 ≤ I := Finset.sum_nonneg (fun i hi => inv_nonneg.mpr (hR i).le)
  have hd : 0 < d := by dsimp only [d]; positivity
  have hd1 : d ≤ 1 := by
    dsimp only [d]
    exact (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) (by linarith)).trans_eq (by norm_num)
  have hdi (i : K) (hi : i ∈ J) : d ≤ R i := by
    have hSingle : (R i)⁻¹ ≤ I := Finset.single_le_sum (fun j hj => inv_nonneg.mpr (hR j).le) hi
    calc
      d ≤ 1/((R i)⁻¹) := one_div_le_one_div_of_le (inv_pos.mpr (hR i)) (by linarith)
      _ = R i := by rw [one_div,inv_inv]
  refine ⟨r,J,by dsimp only [r]; positivity,by dsimp only [r]; linarith,?_⟩
  intro x hx
  obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (hCover hx)
  refine ⟨i,hi,?_⟩
  intro y hy
  change dist y x ≤ 4*r at hy
  change dist x (i : Space n) < R i at hxi
  change dist y (i : Space n) ≤ 4*R i
  have hScale : 4*r ≤ R i := by dsimp only [r]; linarith [hdi i hi]
  linarith [dist_triangle y x (i : Space n),hR i]

/-- The original smooth bounded domain gives a fixed finite separated
    physical partition. Every fourfold patch is either genuinely interior
    or has an actual buffered flattening chart. All choices precede PDE data. -/
theorem smoothDomain_small_patch_atlas {n : ℕ} {O : Set (Space n)} (hO : SmoothDomain O) :
    ∃ (r : ℝ) (hr : 0 < r) (s : Finset (Space n)), r ≤ 1 ∧
      (∀ c ∈ s, c ∈ closure O) ∧
      (∀ c ∈ s, ∀ d ∈ s, c ≠ d → r ≤ ‖c-d‖) ∧
      (∀ x ∈ closure O, 1 ≤ patchSum s r hr x) ∧
      ∀ c ∈ s, Metric.closedBall c (4*r) ⊆ O ∨ boundaryChartBuffer O c r := by
  classical
  have hLocal (i : closure O) : ∃ R : ℝ, 0 < R ∧
      (Metric.closedBall (i : Space n) (4*R) ⊆ O ∨ boundaryChartBuffer O i R) := by
    by_cases hi : (i : Space n) ∈ O
    · obtain ⟨ε,hε,hBall⟩ := Metric.isOpen_iff.mp hO.1 i hi
      exact ⟨ε/8,by positivity,Or.inl ((Metric.closedBall_subset_ball (by linarith : 4*(ε/8) < ε)).trans hBall)⟩
    · have hiF : (i : Space n) ∈ frontier O := by
        rw [frontier,hO.1.interior_eq]
        exact ⟨i.2,hi⟩
      obtain ⟨e,c,he,hxc,hcx,hc,hci,hFaces⟩ := smoothDomain_boundary_closed_flat_chart hO hiF
      obtain ⟨r,q,hr,hq,hSource,hTarget⟩ := openPartialHomeomorph_buffered_radii c hxc hcx
      obtain ⟨R,hR,hBuffer,hImage⟩ := openPartialHomeomorph_source_small_image c hxc hcx (by positivity : 0 < q/2)
      exact ⟨R,hR,Or.inr ⟨e,c,q,he,hq,hBuffer,hImage,hTarget,hc,hci,hFaces⟩⟩
  choose R hR hLocalBuffer using hLocal
  obtain ⟨r,J,hr,hr1,hAssign⟩ := compact_uniform_buffered_ball_assignment hO.2.2.1 R hR
  obtain ⟨s,hs,hSep,hCover,hPartition,hBounds⟩ := compact_separated_patch_partition hO.2.2.1 hr
  refine ⟨r,hr,s,hr1,hs,hSep,hCover,?_⟩
  intro c hc
  obtain ⟨i,hi,hBall⟩ := hAssign c (hs c hc)
  rcases hLocalBuffer i with hInterior | hBoundary
  · exact Or.inl (hBall.trans hInterior)
  · exact Or.inr (boundaryChartBuffer_mono_ball hBoundary hBall)

end Yau.LeafProofs.L16Aux
