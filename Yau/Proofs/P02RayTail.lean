import Yau.Proofs.P02BusemannConvergence

noncomputable section
open Filter
open scoped Topology NNReal

namespace Yau.NodeProofs.P02Aux
open Yau Yau.Blueprint

theorem ray_nat_distance {n : ℕ} (X : KahlerManifold n) (o : Pt X)
    (ray : ℝ≥0 → Pt X) (h0 : ray 0=o)
    (hdist : ∀ s t, distFrom X.metric.form (ray s) (ray t) = |(t : ℝ)-(s : ℝ)|)
    (j : ℕ) : inducedDistance X.metric.form o (ray j) = j := by
  have H := hdist 0 j
  rw [h0] at H
  simpa only [distFrom,lengthDist,NNReal.coe_zero,NNReal.coe_natCast,sub_zero,
    abs_of_nonneg (show (0 : ℝ) ≤ (j : ℝ) from Nat.cast_nonneg j)] using H

theorem exists_common_ray_tail {n : ℕ} (X : KahlerManifold n) (o : Pt X)
    (ray : ℝ≥0 → Pt X) (h0 : ray 0=o)
    (hdist : ∀ s t, distFrom X.metric.form (ray s) (ray t) = |(t : ℝ)-(s : ℝ)|)
    (K : Set (Pt X)) (R L : ℝ)
    (hR : ∀ x ∈ K, inducedDistance X.metric.form o x ≤ R) :
    ∃ N : ℕ, ∀ j ≥ N, ∀ x ∈ K, L ≤ inducedDistance X.metric.form (ray j) x := by
  obtain ⟨N,hN⟩ := exists_nat_ge (R+L)
  refine ⟨N,?_⟩
  intro j hj x hx
  have Htri := X.metric.induced_distance_triangle o x (ray j)
  rw [ray_nat_distance X o ray h0 hdist j,
    X.metric.induced_distance_symm x (ray j)] at Htri
  have Hcast : (N : ℝ) ≤ j := by exact_mod_cast hj
  linarith [hR x hx]

end Yau.NodeProofs.P02Aux
