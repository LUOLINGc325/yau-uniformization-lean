import Yau.Proofs.F05HolderCaps
import Yau.Proofs.F05HolderMovingBarrier
import Yau.LeafProofs.L16ExpBoundaryCombinedBarrier

/-! Uniform initial modulus on a buffered physical chart. The sphere is
controlled by the supplied amplitude, and no trace is imposed on it. -/

open Set
noncomputable section
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
open Yau.LeafProofs.L16ExpBoundaryAux
variable {n : ℕ}

theorem F05_linearOp_cylinder_space_eq {X Y : Set (Space n)} {T : ℝ}
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ) (u : Point n → ℝ)
    {p : Point n} (hx : p.1 ∈ X) (hy : p.1 ∈ Y) (ht : p.2 ∈ Icc 0 T) :
    linearOp (cylinder X 0 T) a b u p = linearOp (cylinder Y 0 T) a b u p :=
  (linearOp_cylinder_restrict_space a b u ⟨hx,ht⟩).trans
    (linearOp_cylinder_restrict_space a b u ⟨hy,ht⟩).symm

theorem F05_buffered_initial_error (k : Option (RIdx n))
    {A₀ b₀ H W₀ lam upper : ℝ} (hA₀ : 0 ≤ A₀) (hb₀ : 0 ≤ b₀)
    (hH : 0 < H) (hW₀ : 0 < W₀) :
    ∃ Ht : ℝ, 0 < Ht ∧ ∀ (T : ℝ), 0 < T →
      ∀ (a : Point n → Mat n) (b : Point n → RIdx n → ℝ) (u : Point n → ℝ),
      ContinuousOn u (cylinder (region k 2) 0 T) →
      (∀ z ∈ F05CapOpen k 2 ×ˢ Ioo 0 T,
        ContDiffAt ℝ 2 (fun x => u (x,z.2)) z.1) →
      (∀ z ∈ F05CapOpen k 2 ×ˢ Ioo 0 T,
        DifferentiableAt ℝ (fun t => u (z.1,t)) z.2) →
      Elliptic (F05CapOpen k 2 ×ˢ Ioo 0 T) a lam upper →
      (∀ z ∈ F05CapOpen k 2 ×ˢ Ioo 0 T, ∀ i j, |a z i j| ≤ A₀) →
      (∀ z ∈ F05CapOpen k 2 ×ˢ Ioo 0 T, ∀ i, |b z i| ≤ b₀) →
      (∀ x ∈ region k 2, u (x,0) = 0) →
      (∀ x ∈ frontier (F05FlatOpen k) ∩ Metric.ball 0 2,
        ∀ t ∈ Icc 0 T, u (x,t) = 0) →
      (∀ z ∈ cylinder (region k 2) 0 T, |u z| ≤ W₀) →
      (∀ z ∈ F05CapOpen k 2 ×ˢ Ioo 0 T,
        |linearOp (cylinder (region k 2) 0 T) a b u z| ≤ H) →
      ∀ y ∈ region k (7/4), ∀ t ∈ Icc 0 T, |u (y,t)| ≤ Ht*t := by
  classical
  let r : ℝ := 1/8
  have hr : 0 < r := by norm_num [r]
  let c := W₀/r^2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  let C : ℝ := (∑ _i : RIdx n, ∑ _j : RIdx n, A₀*2)+
    ∑ _i : RIdx n, b₀*(2*r)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let Ht := H+c*C+1
  have hHt : 0 < Ht := by dsimp [Ht]; positivity
  refine ⟨Ht,hHt,?_⟩
  intro T hT a b u hu hs ht he hA hb hi hl hsup hop y hy t htm
  let D := F05FlatOpen k ∩ Metric.ball y r
  let W : Space n → ℝ := fun x => c*sphereBarrier y x
  have hD : IsOpen D := (F05FlatOpen_isOpen k).inter Metric.isOpen_ball
  have hcl : closure D ⊆ region k 2 := F05_cap_closure_subset_two k hy.1
  have hDsmall : D ⊆ F05CapOpen k 2 := by
    intro x hx
    have hxy : ‖x-y‖ < r := by simpa only [Metric.mem_ball,dist_eq_norm] using hx.2
    have hn := norm_add_le (x-y) y
    rw [sub_add_cancel] at hn
    refine ⟨hx.1,?_⟩
    rw [Metric.mem_ball,dist_zero_right]
    dsimp only [r] at hxy
    linarith [hy.1]
  have hSub : D ×ˢ Ioo 0 T ⊆ F05CapOpen k 2 ×ˢ Ioo 0 T :=
    fun _ hz => ⟨hDsmall hz.1,hz.2⟩
  have hWnonneg (x : Space n) : 0 ≤ W x := mul_nonneg hc (sq_nonneg _)
  have hWc : ContinuousOn W (closure D) :=
    (continuous_const.mul (sphereBarrier_contDiff y).continuous).continuousOn
  have hWs (x : Space n) (_ : x ∈ D) : ContDiffAt ℝ 2 W x :=
    contDiffAt_const.mul ((sphereBarrier_contDiff y).contDiffAt.of_le (by simp))
  have hbound := F05_moving_barrier_abs (O := D) (b := b) (H := H) (Ht := Ht)
    hD (F05_cap_closure_isCompact k y r) hT
    (hu.mono (fun _ hz => ⟨hcl hz.1,hz.2⟩))
    (fun z hz => hs z (hSub hz)) (fun z hz => ht z (hSub hz))
    ⟨he.1,he.2.1,fun z hz => he.2.2 z (hSub hz)⟩ hWc hWs
    (by intro x hx; rw [hi x (hcl hx),abs_zero]; exact hWnonneg x)
    (by
      intro x hx s hsm
      have hn : 0 ≤ Ht*s := mul_nonneg hHt.le hsm.1
      rcases F05_cap_frontier_cases hx with hface | hsphere
      · have hnorm : ‖x‖ < 2 := by
          have hxnorm := (F05_cap_closure_subset_region k hy.1) hx.1
          dsimp only [r] at hxnorm
          linarith [hxnorm.1]
        rw [hl x ⟨hface,by simpa only [Metric.mem_ball,dist_zero_right] using hnorm⟩ s hsm,
          abs_zero]
        exact add_nonneg (hWnonneg x) hn
      · have hSphere : W x = W₀ := by
          dsimp only [W,c,sphereBarrier]
          rw [hsphere.2]
          exact div_mul_cancel₀ W₀ (ne_of_gt (sq_pos_of_pos hr))
        rw [hSphere]
        exact (hsup (x,s) ⟨hcl hx.1,hsm⟩).trans (le_add_of_nonneg_right hn))
    (by
      intro z hz
      rw [F05_linearOp_cylinder_space_eq a b u (subset_closure hz.1)
        (hcl (subset_closure hz.1)) ⟨hz.2.1.le,hz.2.2.le⟩]
      exact hop z (hSub hz))
    (by
      intro z hz
      have hxy : ‖z.1-y‖ ≤ r :=
        (show ‖z.1-y‖ < r by simpa only [Metric.mem_ball,dist_eq_norm] using hz.1.2).le
      have hSphere : |stationaryOp (a z) (b z) (sphereBarrier y) z.1| ≤ C :=
        sphereBarrier_operator_abs_bound hA₀ hb₀ (hA z (hSub hz)) (hb z (hSub hz)) hxy
      rw [show W = (fun x => c*sphereBarrier y x) from rfl,
        stationaryOp_const_mul ((sphereBarrier_contDiff y).contDiffAt.of_le (by simp))]
      have hMul := mul_le_mul_of_nonneg_left (abs_le.mp hSphere).1 hc
      dsimp only [Ht]
      linarith)
  have hycl : y ∈ closure (F05FlatOpen k) := by
    rw [F05FlatOpen_closure]
    exact hy.2
  have hymem : y ∈ closure D := F05_cap_center_mem_closure hycl hr
  have hout := hbound (y,t) ⟨hymem,htm⟩
  simpa only [W,sphereBarrier,sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0),
    mul_zero,zero_add] using hout

end Yau.Proofs.F05Aux
