import Yau.Proofs.F05PhysicalFactories

/-! The native factories on full space and the genuine flat physical halfspace. -/

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false

namespace Yau.Proofs.F05Aux

open Yau.Parabolic Yau.LeafProofs.L16Aux

def F05FlatOpen {n : ℕ} (ν : Option (RIdx n)) : Set (Space n) :=
  match ν with
  | none => univ
  | some j => {z | realCoord z j < 0}

theorem F05_flat_physical_factory {n : ℕ} (ν : Option (RIdx n))
    {α lam upper M P : ℝ} (hα : 0 < α) (hα1 : α < 1) (hM : 0 ≤ M) (hP : 0 ≤ P)
    (ψ : Space n → ℝ)
    (hψ : HolderBound α (cylinder univ 0 1) (fun p => ψ p.1) P)
    (hψsupp : tsupport ψ ⊆ Metric.closedBall 0 (1/4)) :
    ∃ δ C E : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧ 0 < E ∧
      F05AllInitialPhysicalFactory (F05FlatOpen ν) α lam upper M ψ δ C E := by
  have hr : (0 : ℝ) < 1/2 := by norm_num
  have hr1 : (1/2 : ℝ) ≤ 1 := by norm_num
  have hPlateau : ∀ x, outerPatchBump (1/2) hr (0 : Space n) x * ψ x = ψ x := by
    intro x
    by_cases hx : ψ x = 0
    · rw [hx, mul_zero]
    have hxS := hψsupp (subset_tsupport ψ (Function.mem_support.mpr hx))
    have hb : outerPatchBump (1/2) hr (0 : Space n) x = 1 := by
      apply (outerPatchBump (1/2) hr (0 : Space n)).one_of_mem_closedBall
      exact (Metric.closedBall_subset_closedBall (by norm_num : (1/4 : ℝ) ≤ 3*(1/2)/2)) hxS
    rw [hb, one_mul]
  cases ν with
  | none =>
    exact F05_interior_physical_factory hα hα1 hM hP 0 hr hr1 (subset_univ _) ψ hψ hPlateau
  | some j =>
    let e := -(realVec j)
    let c := OpenPartialHomeomorph.refl (Space n)
    have he : ‖e‖ = 1 := by simp only [e, norm_neg, realVec_norm]
    have hinner (z : Space n) : inner ℝ e z = -realCoord z j := by
      rw [show e = -(realVec j) from rfl, inner_neg_left, real_inner_comm, real_inner_realVec]
    have hO : F05FlatOpen (some j) = {z : Space n | 0 < inner ℝ e z} := by
      ext z
      simp only [F05FlatOpen, mem_ofPred_eq, hinner, neg_pos]
    apply F05_boundary_physical_factory hα hα1 hM hP 0 hr hr1 e he c (q := 8)
      (by norm_num) (subset_univ _) ?_ (subset_univ _) contDiffOn_id contDiffOn_id
      ?_ ψ hψ hPlateau
    · intro z hz
      change z ∈ Metric.ball (0 : Space n) (8/2)
      have hn : ‖z‖ ≤ 4*(1/2 : ℝ) := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
      rw [Metric.mem_ball, dist_zero_right]
      linarith
    · intro z hz
      change (z ∈ closure (F05FlatOpen (some j)) ↔ 0 ≤ inner ℝ e z) ∧
        (z ∈ frontier (F05FlatOpen (some j)) ↔ inner ℝ e z = 0)
      rw [hO, unitNormal_halfSpace_closure he, unitNormal_halfSpace_frontier he]
      exact ⟨Iff.rfl, Iff.rfl⟩

/-- First compatibility of the computed patch equation gives the actual zero
initial time jet; it is not part of the source-free Dirichlet data alone. -/
theorem F05_patch_initial_time_zero {n : ℕ} (O : Set (Space n)) (T : ℝ) (hT : 0 ≤ T)
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ)
    (w f H : Point n → ℝ) (ψ : Space n → ℝ)
    (hw : ∀ x, w (x,0) = 0) (hf : ∀ x ∈ closure O, f (x,0) = 0)
    (hH : ∀ x, H (x,0) = 0)
    (hEq : ∀ p ∈ cylinder (closure O) 0 T,
      linearOp (cylinder (closure O) 0 T) a b w p = ψ p.1*f p-H p)
    (x : Space n) (hx : x ∈ closure O) :
    derivWithin (fun t => w (x,t)) (Icc 0 T) 0 = 0 := by
  have heq := hEq (x,0) ⟨hx,le_rfl,hT⟩
  simp only [linearOp, spatialD_initial_zero hw, spatialDD_initial_zero hw,
    ContinuousLinearMap.zero_apply, mul_zero, Finset.sum_const_zero, sub_zero, hf x hx,
    hH x] at heq
  have hFiber : {t : ℝ | (x,t) ∈ Parabolic.cylinder (closure O) 0 T} = Icc 0 T := by
    ext t
    simp only [Parabolic.cylinder, mem_prod, hx, true_and, mem_setOf_eq]
  unfold timeD at heq
  rw [hFiber] at heq
  exact heq

end Yau.Proofs.F05Aux
