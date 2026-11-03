import Yau.Proofs.F01AffineParabolicSchauder

/-! A closed-cylinder estimate supplies the actual open-lower backward
cylinder estimate. Their within-time derivatives agree at every point
of the backward cylinder, including its upper time face. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem timeD_closed_open_lower {S : Set (Space n)} {l r : ℝ} (u : Point n → ℝ)
    {p : Point n} (hp : p ∈ S ×ˢ Ioc l r) :
    timeD (cylinder S l r) u p = timeD (S ×ˢ Ioc l r) u p := by
  simp only [timeD, cylinder, mem_prod, hp.1, true_and, Set.mem_ofPred_eq]
  apply derivWithin_congr_set
  filter_upwards [Ioi_mem_nhds hp.2.1] with t ht
  apply propext
  exact ⟨fun h => ⟨ht, h.2⟩, fun h => ⟨ht.le, h.2⟩⟩

theorem c2_closed_open_lower {S : Set (Space n)} {l r : ℝ} {u : Point n → ℝ}
    (hu : C2 (cylinder S l r) u) : C2 (S ×ˢ Ioc l r) u := by
  have hSub : S ×ˢ Ioc l r ⊆ cylinder S l r := fun p hp => ⟨hp.1, hp.2.1.le, hp.2.2⟩
  refine ⟨hu.1.mono hSub, hu.2.1.mono hSub, hu.2.2.1.mono hSub, ?_, ?_, ?_⟩
  · apply (hu.2.2.2.1.mono hSub).congr
    intro p hp
    exact (timeD_closed_open_lower u hp).symm
  · intro p hp
    exact hu.2.2.2.2.1 p (hSub hp)
  · intro p hp
    have hd := hu.2.2.2.2.2 p (hSub hp)
    simp only [cylinder, mem_prod, hp.1, true_and, Set.mem_ofPred_eq] at hd ⊢
    exact hd.mono Ioc_subset_Icc_self

theorem schauderBound_closed_open_lower {S : Set (Space n)} {l r β C : ℝ} {u : Point n → ℝ}
    (hu : SchauderBound β (cylinder S l r) u C) : SchauderBound β (S ×ˢ Ioc l r) u C := by
  have hSub : S ×ˢ Ioc l r ⊆ cylinder S l r := fun p hp => ⟨hp.1, hp.2.1.le, hp.2.2⟩
  have hDD : HolderBound β (S ×ˢ Ioc l r) (spatialDD u) C :=
    ⟨hu.2.2.2.1.1, fun p hp => hu.2.2.2.1.2.1 p (hSub hp),
      fun p hp q hq => hu.2.2.2.1.2.2 p (hSub hp) q (hSub hq)⟩
  have hTime : HolderBound β (S ×ˢ Ioc l r) (timeD (cylinder S l r) u) C :=
    ⟨hu.2.2.2.2.1, fun p hp => hu.2.2.2.2.2.1 p (hSub hp),
      fun p hp q hq => hu.2.2.2.2.2.2 p (hSub hp) q (hSub hq)⟩
  refine ⟨c2_closed_open_lower hu.1, hu.2.1, fun p hp => hu.2.2.1 p (hSub hp), hDD, ?_⟩
  apply holderBound_congr_on_native hTime
  intro p hp
  exact timeD_closed_open_lower u hp

theorem schauderBound_backward_of_closed {R β C : ℝ} {u : Point n → ℝ}
    (hu : SchauderBound β (cylinder (Metric.ball 0 R) (-(R ^ 2)) 0) u C) :
    SchauderBound β (backward R) u C := schauderBound_closed_open_lower hu

theorem linearOp_closed_open_lower {S : Set (Space n)} {l r : ℝ}
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ) (u : Point n → ℝ)
    {p : Point n} (hp : p ∈ S ×ˢ Ioc l r) :
    linearOp (cylinder S l r) a b u p = linearOp (S ×ˢ Ioc l r) a b u p := by
  unfold linearOp
  rw [timeD_closed_open_lower u hp]

end Yau.NodeProofs.F01Aux
