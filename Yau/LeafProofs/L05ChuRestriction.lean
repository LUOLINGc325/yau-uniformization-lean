import Yau.LeafProofs.L05ChuHessianTransport
import Yau.LeafProofs.L05ChuParabolicGeometry

noncomputable section

open Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

theorem chu_backward_subset {n : ℕ} {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) :
    (backward r : Set (Point n)) ⊆ backward R := by
  intro p hp
  refine ⟨Metric.ball_subset_ball hrR hp.1,?_,hp.2.2⟩
  have hs : r^2 ≤ R^2 := by nlinarith only [hr,hrR]
  exact (neg_le_neg hs).trans_lt hp.2.1

theorem chu_timeD_backward_restrict {n : ℕ} {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R)
    (u : Point n → ℝ) {p : Point n} (hp : p ∈ backward r) :
    timeD (backward r) u p=timeD (backward R) u p := by
  unfold timeD
  apply derivWithin_congr_set
  have hsp := Metric.ball_subset_ball hrR hp.1
  have hs : r^2 ≤ R^2 := by nlinarith only [hr,hrR]
  filter_upwards [isOpen_Ioi.mem_nhds hp.2.1] with t ht
  apply propext
  change (p.1 ∈ Metric.ball 0 r ∧ -(r^2) < t ∧ t ≤ 0) ↔
    (p.1 ∈ Metric.ball 0 R ∧ -(R^2) < t ∧ t ≤ 0)
  constructor
  · intro h
    exact ⟨hsp,(neg_le_neg hs).trans_lt h.2.1,h.2.2⟩
  · intro h
    exact ⟨hp.1,ht,h.2.2⟩

theorem chu_c2_backward_restrict {n : ℕ} {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R)
    {u : Point n → ℝ} (hu : C2 (backward R) u) : C2 (backward r) u := by
  have hsub := chu_backward_subset hr hrR (n := n)
  refine ⟨hu.1.mono hsub,hu.2.1.mono hsub,hu.2.2.1.mono hsub,?_,?_,?_⟩
  · exact (hu.2.2.2.1.mono hsub).congr (fun p hp => chu_timeD_backward_restrict hr hrR u hp)
  · intro p hp
    exact hu.2.2.2.2.1 p (hsub hp)
  · intro p hp
    exact (hu.2.2.2.2.2 p (hsub hp)).mono (fun t ht => hsub ht)

theorem chu_timeD_cylinder_restrict_backward {n : ℕ} {O : Set (Space n)} {l r R : ℝ}
    (hlr : l < r) (hQ : cylinder O l r ⊆ backward R) {u : Point n → ℝ}
    (hu : C2 (backward R) u) {p : Point n} (hp : p ∈ cylinder O l r) :
    timeD (cylinder O l r) u p=timeD (backward R) u p := by
  have hf : {t | (p.1,t) ∈ cylinder O l r}=Set.Icc l r := by ext t; simp [cylinder,hp.1]
  have hsub : Set.Icc l r ⊆ {t : ℝ | (p.1,t) ∈ backward R} := by
    intro t ht
    exact hQ ⟨hp.1,ht⟩
  unfold timeD
  rw [hf]
  apply derivWithin_subset hsub (uniqueDiffOn_Icc hlr p.2 hp.2)
  exact hu.2.2.2.2.2 p (hQ hp)

theorem chu_c2_cylinder_restrict_backward {n : ℕ} {O : Set (Space n)} {l r R : ℝ}
    (hlr : l < r) (hQ : cylinder O l r ⊆ backward R) {u : Point n → ℝ}
    (hu : C2 (backward R) u) : C2 (cylinder O l r) u := by
  refine ⟨hu.1.mono hQ,hu.2.1.mono hQ,hu.2.2.1.mono hQ,?_,?_,?_⟩
  · exact (hu.2.2.2.1.mono hQ).congr (fun p hp => chu_timeD_cylinder_restrict_backward hlr hQ hu hp)
  · exact fun p hp => hu.2.2.2.2.1 p (hQ hp)
  · exact fun p hp => (hu.2.2.2.2.2 p (hQ hp)).mono (fun t ht => hQ ht)

end Yau.LeafProofs.L05Aux
