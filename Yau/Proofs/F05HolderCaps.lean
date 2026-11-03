import Yau.Proofs.F05HolderGauge
import Yau.LeafProofs.L16ExpBoundaryLocalDomain

/-! The comparison caps require openness and compact closure, including at
the physical/spherical corner. No smooth-domain assertion is needed. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
open Yau.LeafProofs.L16ExpBoundaryAux
variable {n : ℕ}

theorem F05_region_mono {k : Option (RIdx n)} {r R : ℝ} (hr : r ≤ R) :
    region k r ⊆ region k R := fun _ hx => ⟨hx.1.trans hr,hx.2⟩

theorem F05_region_isClosed (k : Option (RIdx n)) (r : ℝ) :
    IsClosed (region k r) := by
  have hEq : region k r = Metric.closedBall 0 r ∩ closure (F05FlatOpen k) := by
    ext x
    cases k <;> simp [region,Metric.mem_closedBall,dist_zero_right,F05FlatOpen_closure]
  rw [hEq]
  exact Metric.isClosed_closedBall.inter isClosed_closure

theorem F05_region_isCompact (k : Option (RIdx n)) (r : ℝ) :
    IsCompact (region k r) :=
  (isCompact_closedBall (0 : Space n) r).of_isClosed_subset (F05_region_isClosed k r)
    (fun x hx => by simpa only [Metric.mem_closedBall,dist_zero_right] using hx.1)

theorem F05_cap_closure_isCompact (k : Option (RIdx n)) (y : Space n) (r : ℝ) :
    IsCompact (closure (F05FlatOpen k ∩ Metric.ball y r)) :=
  (isCompact_closedBall y r).of_isClosed_subset isClosed_closure
    (fun _ hx => (closure_inter_ball_subset (F05FlatOpen k) y r hx).2)

theorem F05_cap_closure_subset_region (k : Option (RIdx n))
    {y : Space n} {R r : ℝ} (hy : ‖y‖ ≤ R) :
    closure (F05FlatOpen k ∩ Metric.ball y r) ⊆ region k (R+r) := by
  intro x hx
  have hcl := closure_inter_ball_subset (F05FlatOpen k) y r hx
  have hxy : ‖x-y‖ ≤ r := by
    simpa only [Metric.mem_closedBall,dist_eq_norm] using hcl.2
  have hn := norm_add_le (x-y) y
  rw [sub_add_cancel] at hn
  refine ⟨by linarith,?_⟩
  cases k <;> simpa only [F05FlatOpen_closure,mem_ofPred_eq] using hcl.1

theorem F05_cap_closure_subset_two (k : Option (RIdx n))
    {y : Space n} (hy : ‖y‖ ≤ (7/4 : ℝ)) :
    closure (F05FlatOpen k ∩ Metric.ball y (1/8)) ⊆ region k 2 :=
  (F05_cap_closure_subset_region k hy).trans (F05_region_mono (by norm_num))

theorem F05_cap_center_mem_closure {k : Option (RIdx n)} {y : Space n} {r : ℝ}
    (hy : y ∈ closure (F05FlatOpen k)) (hr : 0 < r) :
    y ∈ closure (F05FlatOpen k ∩ Metric.ball y r) :=
  Metric.isOpen_ball.closure_inter ⟨hy,Metric.mem_ball_self hr⟩

theorem F05CapOpen_closure_subset (k : Option (RIdx n)) (r : ℝ) :
    closure (F05CapOpen k r) ⊆ region k r := by
  have h := F05_cap_closure_subset_region k (y := (0 : Space n)) (r := r) (le_refl ‖(0 : Space n)‖)
  simpa only [F05CapOpen,norm_zero,zero_add] using h

theorem F05_cap_frontier_cases {k : Option (RIdx n)} {y x : Space n} {r : ℝ}
    (hx : x ∈ frontier (F05FlatOpen k ∩ Metric.ball y r)) :
    x ∈ frontier (F05FlatOpen k) ∨
      (x ∈ closure (F05FlatOpen k) ∧ ‖x-y‖ = r) :=
  frontier_inter_ball_cases (F05FlatOpen_isOpen k) hx

end Yau.Proofs.F05Aux
