import Yau.LeafProofs.L16ExpBoundaryHolderPowers
import Yau.LeafProofs.L16ExpBoundary

open Filter Set
open scoped Topology ContDiff

noncomputable section

namespace Yau.LeafProofs.L16ExpBoundaryHolderAux

open Yau.Parabolic L16Aux

def boundaryDistance {n : ℕ} (O : Set (Space n)) (x : Space n) : ℝ :=
  Metric.infDist x (frontier O)

theorem boundaryDistance_nonneg {n : ℕ} (O : Set (Space n)) (x : Space n) :
    0 ≤ boundaryDistance O x := Metric.infDist_nonneg

theorem boundaryDistance_le_add {n : ℕ} (O : Set (Space n)) (x y : Space n) :
    boundaryDistance O x ≤ boundaryDistance O y+‖x-y‖ := by
  simpa only [boundaryDistance,dist_eq_norm] using
    (Metric.infDist_le_infDist_add_dist (x := x) (y := y) (s := frontier O))

/-- A positive boundary-distance buffer contains a genuine interior ball. -/
theorem ball_subset_of_boundaryDistance {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    (hFrontier : (frontier O).Nonempty) {x : Space n} (hx : x ∈ closure O)
    {R : ℝ} (hR : 0 < R) (hRd : R ≤ boundaryDistance O x) :
    x ∈ O ∧ Metric.ball x R ⊆ O := by
  have hd : 0 < boundaryDistance O x := hR.trans_le hRd
  have hxO : x ∈ O := by
    by_contra hn
    have hxF : x ∈ frontier O := ⟨hx,by simpa only [hO.interior_eq] using hn⟩
    have hle := Metric.infDist_le_dist_of_mem (x := x) hxF
    simp only [dist_self] at hle
    exact not_le_of_gt hd hle
  have hne : O ≠ univ := by
    intro heq
    simpa only [heq,frontier_univ,Set.not_nonempty_empty] using hFrontier
  obtain ⟨y,hy,heq⟩ := exists_mem_frontier_infDist_compl_eq_dist hxO hne
  have hCompare : boundaryDistance O x ≤ Metric.infDist x Oᶜ := by
    rw [heq]
    exact Metric.infDist_le_dist_of_mem hy
  exact ⟨hxO,(Metric.ball_subset_ball (hRd.trans hCompare)).trans Metric.ball_infDist_compl_subset⟩

theorem center_mem_oscCylinder {n : ℕ} (p : Point n) {R : ℝ} (hR : 0 < R) :
    p ∈ dgOscCylinder p R := by
  exact ⟨Metric.mem_ball_self hR,by nlinarith,le_rfl⟩

theorem ordered_pair_mem_oscCylinder {n : ℕ} {p q : Point n}
    (hδ : 0 < parabolicDistance p q) (ht : q.2 ≤ p.2) :
    p ∈ dgOscCylinder p (2*parabolicDistance p q) ∧
      q ∈ dgOscCylinder p (2*parabolicDistance p q) := by
  refine ⟨center_mem_oscCylinder p (by positivity),?_,?_,ht⟩
  · change dist q.1 p.1 < 2*parabolicDistance p q
    rw [dist_eq_norm,norm_sub_rev]
    linarith [parabolicDistance_spatial_le p q]
  · have hh := parabolicDistance_time_gap_le_sq p q
    rw [abs_of_nonneg (sub_nonneg.mpr ht)] at hh
    nlinarith

/-- The radius selected below both boundary and initial buffers fits entirely
inside the actual equation region, while retaining its terminal face. -/
theorem buffered_oscCylinder_subsets {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    (hFrontier : (frontier O).Nonempty) {T : ℝ} {p : Point n}
    (hp : p ∈ cylinder (closure O) 0 T) {h : ℝ} (hh : 0 < h)
    (hbd : h ≤ boundaryDistance O p.1) (hbt : h ≤ Real.sqrt p.2) :
    dgOscCylinderOpen p (h/2) ⊆ O ×ˢ Ioo 0 T ∧
      dgOscCylinder p (h/2) ⊆ cylinder (closure O) 0 T := by
  have hR : 0 < h/2 := by positivity
  have hRd : h/2 ≤ boundaryDistance O p.1 := by linarith
  have hball := (ball_subset_of_boundaryDistance hO hFrontier hp.1 hR hRd).2
  have hsqrt := Real.sq_sqrt hp.2.1
  have hsq : h^2 ≤ p.2 := by nlinarith [Real.sqrt_nonneg p.2]
  have hbottom : 0 < p.2-(h/2)^2 := by nlinarith
  constructor
  · intro z hz
    exact ⟨hball hz.1,hbottom.trans hz.2.1,hz.2.2.trans_le hp.2.2⟩
  · intro z hz
    exact ⟨subset_closure (hball hz.1),(hbottom.trans hz.2.1).le,hz.2.2.trans hp.2.2⟩

theorem oscCylinder_spatial_time_bounds {n : ℕ} {p z : Point n} {R : ℝ}
    (hz : z ∈ dgOscCylinder p R) : ‖z.1-p.1‖ < R ∧ |z.2-p.2| ≤ R^2 := by
  refine ⟨by simpa only [Metric.mem_ball,dist_eq_norm] using hz.1,?_⟩
  rw [abs_of_nonpos (sub_nonpos.mpr hz.2.2)]
  linarith [hz.2.1]

end Yau.LeafProofs.L16ExpBoundaryHolderAux
