import Yau.Proofs.F05BootstrapDefinitions

/-! Every positive-radius physical cap has unique real derivatives, including
the true plane and the artificial rim. -/

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_region_convex (ν : Option (RIdx n)) (r : ℝ) : Convex ℝ (region ν r) := by
  cases ν with
  | none =>
    have hEq : region (none : Option (RIdx n)) r = Metric.closedBall (0 : Space n) r := by
      ext z
      simp [region,Metric.mem_closedBall,dist_zero_right]
    rw [hEq]
    exact convex_closedBall 0 r
  | some j =>
    have hEq : region (some j) r = Metric.closedBall (0 : Space n) r ∩
        {z | realCoordLinear j z ≤ 0} := by
      ext z
      simp [region,Metric.mem_closedBall,dist_zero_right,realCoordLinear_apply]
    rw [hEq]
    exact (convex_closedBall 0 r).inter
      (convex_halfSpace_le (realCoordLinear j).toLinearMap.isLinear 0)

theorem F05_region_interior_nonempty (ν : Option (RIdx n)) {r : ℝ} (hr : 0 < r) :
    (interior (region ν r)).Nonempty := by
  cases ν with
  | none =>
    refine ⟨0,mem_interior_iff_mem_nhds.mpr ?_⟩
    apply mem_of_superset (Metric.ball_mem_nhds (0 : Space n) hr)
    intro z hz
    exact ⟨(show ‖z‖ < r by simpa only [Metric.mem_ball,dist_zero_right] using hz).le,trivial⟩
  | some j =>
    let a : Space n := -(r/2) • realVec j
    let V : Set (Space n) := {z | ‖z‖ < r ∧ realCoordLinear j z < 0}
    have hV : IsOpen V := (isOpen_lt continuous_norm continuous_const).inter
      (isOpen_lt (realCoordLinear j).continuous continuous_const)
    have ha : a ∈ V := by
      constructor
      · simp only [a,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_pos (by positivity : 0 < r/2),
          realVec_norm,mul_one]
        linarith
      · rw [show a = -(r/2) • realVec j from rfl,map_smul]
        change -(r/2)*inner ℝ (realVec j) (realVec j) < 0
        rw [realVec_inner]
        simp only [ite_true,mul_one]
        linarith
    have hSub : V ⊆ region (some j) r := by
      intro z hz
      exact ⟨hz.1.le,by simpa only [realCoordLinear_apply] using hz.2.le⟩
    exact ⟨a,mem_interior_iff_mem_nhds.mpr (mem_of_superset (hV.mem_nhds ha) hSub)⟩

theorem F05_region_uniqueDiffOn (ν : Option (RIdx n)) {r : ℝ} (hr : 0 < r) :
    UniqueDiffOn ℝ (region ν r) :=
  uniqueDiffOn_convex (F05_region_convex ν r) (F05_region_interior_nonempty ν hr)

theorem F05_region_closure_interior (ν : Option (RIdx n)) {r : ℝ} (hr : 0 < r) :
    closure (interior (region ν r)) = region ν r := by
  rw [(F05_region_convex ν r).closure_interior_eq_closure_of_nonempty_interior
    (F05_region_interior_nonempty ν hr),(F05_region_isClosed ν r).closure_eq]

theorem F05_bootstrap_cylinder_uniqueDiffOn (ν : Option (RIdx n)) {r s T : ℝ}
    (hr : 0 < r) (hsT : s < T) : UniqueDiffOn ℝ (region ν r ×ˢ Icc s T) :=
  (F05_region_uniqueDiffOn ν hr).prod (uniqueDiffOn_Icc hsT)

end Yau.Proofs.F05Aux
