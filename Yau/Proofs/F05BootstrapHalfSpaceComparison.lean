import Yau.Proofs.F05BootstrapNative

/-! Bounded comparison on the actual half-space follows by compact half-ball
comparison with a quadratic barrier. No equation is reflected across the
physical plane, and no artificial spherical trace is imposed on the input. -/

open Set
noncomputable section
set_option maxHeartbeats 1600000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux Yau.LeafProofs.L16ExpBoundaryAux
variable {n : ℕ}

theorem F05_bounded_halfSpace_subsolution_bound {e : Space n} (he : ‖e‖ = 1)
    {T lam upper M B F : ℝ} {a : Point n → Mat n} {b : Point n → RIdx n → ℝ}
    {u : Point n → ℝ} (hT : 0 < T)
    (hu : C2 (cylinder {x | 0 ≤ inner ℝ e x} 0 T) u)
    (hEll : Elliptic (cylinder {x | 0 ≤ inner ℝ e x} 0 T) a lam upper)
    (hM : 0 ≤ M)
    (hb : ∀ p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T, ∀ i, |b p i| ≤ M)
    (hBound : ∀ p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T, u p ≤ B)
    (hInit : ∀ x, 0 ≤ inner ℝ e x → u (x,0) ≤ 0)
    (hFace : ∀ x, inner ℝ e x = 0 → ∀ t ∈ Icc 0 T, u (x,t) ≤ 0)
    (hF : 0 ≤ F)
    (hOp : ∀ p ∈ {x | 0 < inner ℝ e x} ×ˢ Ioc 0 T,
      linearOp (cylinder {x | 0 ≤ inner ℝ e x} 0 T) a b u p ≤ F) :
    ∀ p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T, u p ≤ p.2*F := by
  intro p hp
  by_contra hn
  have hPos : 0 < u p-p.2*F := sub_pos.mpr (lt_of_not_ge hn)
  have hpInside : 0 < inner ℝ e p.1 := by
    have hpNonneg : 0 ≤ inner ℝ e p.1 := hp.1
    by_contra hNot
    have hpZero : inner ℝ e p.1 = 0 := le_antisymm (le_of_not_gt hNot) hpNonneg
    have hFaceP := hFace p.1 hpZero p.2 hp.2
    have htF := mul_nonneg hp.2.1 hF
    linarith
  let K : ℝ := barrierGrowthRate n upper M
  have hK : 0 ≤ K := barrierGrowthRate_nonneg n (hEll.1.le.trans hEll.2.1) hM
  let ρ : ℝ := quadraticBarrier 1 K p
  have hρ : 0 < ρ := by
    dsimp only [ρ,quadraticBarrier,barrierTime,quadraticBarrierSpace]
    positivity
  let δ : ℝ := (u p-p.2*F)/(2*ρ)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδeq : quadraticBarrier δ K p = (u p-p.2*F)/2 := by
    have hScale : quadraticBarrier δ K p = δ*ρ := by
      dsimp only [quadraticBarrier,barrierTime,ρ]
      ring
    rw [hScale]
    dsimp only [δ]
    field_simp
  let B' : ℝ := max B 0
  have hB' : 0 ≤ B' := le_max_right _ _
  let R : ℝ := ‖p.1‖+1+B'/δ
  have hR1 : 1 ≤ R := by
    dsimp only [R]
    linarith [norm_nonneg p.1,div_nonneg hB' hδ.le]
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hpR : ‖p.1‖ < R := by dsimp only [R]; linarith [div_nonneg hB' hδ.le]
  have hBR : B' ≤ δ*R^2 := by
    have hRdiv : B'/δ ≤ R := by dsimp only [R]; linarith [norm_nonneg p.1]
    have hRSq : R ≤ R^2 := by nlinarith
    have h := (div_le_iff₀ hδ).mp (hRdiv.trans hRSq)
    nlinarith
  let H : Set (Space n) := {x | 0 < inner ℝ e x}
  let S : Set (Space n) := {x | 0 ≤ inner ℝ e x}
  let O : Set (Space n) := H ∩ Metric.ball 0 R
  have hH : IsOpen H := isOpen_lt continuous_const (continuous_const.inner continuous_id)
  have hClosure : closure H = S := unitNormal_halfSpace_closure he
  have hSpaceSub : closure O ⊆ S := by
    rw [← hClosure]
    exact closure_mono inter_subset_left
  have hCompact : IsCompact (closure O) :=
    (isCompact_closedBall (0 : Space n) R).of_isClosed_subset isClosed_closure
      (fun _ hx => (closure_inter_ball_subset H 0 R hx).2)
  have hSub : cylinder (closure O) 0 T ⊆ cylinder S 0 T :=
    fun q hq => ⟨hSpaceSub hq.1,hq.2⟩
  have huLoc := c2_cylinder_mono_space hSpaceSub hu
  have hBarLoc := quadraticBarrier_C2 (S := closure O) hT δ K
  have hLift := c2_add_const (c2_sub_timeAffine hT huLoc F) F
  let w : Point n → ℝ := fun q => ((u q-F*(q.2+1))+F)-quadraticBarrier δ K q
  have hw : C2 (cylinder (closure O) 0 T) w := c2_sub hLift hBarLoc
  have hWInit : ∀ x ∈ closure O, w (x,0) ≤ 0 := by
    intro x hx
    have hBar : 0 ≤ quadraticBarrier δ K (x,0) := by
      dsimp only [quadraticBarrier,barrierTime,quadraticBarrierSpace]
      positivity
    dsimp only [w]
    simp only [zero_add,mul_one]
    linarith [hInit x (hSpaceSub hx)]
  have hWLat : ∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, w (x,t) ≤ 0 := by
    intro x hx t ht
    have hCases := frontier_inter_ball_cases hH hx
    rcases hCases with hPlane | hSphere
    · have hxZero : inner ℝ e x = 0 := by
        simpa only [H,unitNormal_halfSpace_frontier he,mem_ofPred_eq] using hPlane
      have hU := hFace x hxZero t ht
      have hBar : 0 ≤ quadraticBarrier δ K (x,t) := by
        dsimp only [quadraticBarrier,barrierTime,quadraticBarrierSpace]
        positivity
      have htF := mul_nonneg ht.1 hF
      dsimp only [w]
      linarith
    · have hxR : ‖x‖ = R := by simpa only [sub_zero] using hSphere.2
      have hxS : x ∈ S := by rw [← hClosure]; exact hSphere.1
      have hExp : 1 ≤ Real.exp (K*t) := Real.one_le_exp_iff.mpr (mul_nonneg hK ht.1)
      have hQuad0 : 0 ≤ quadraticBarrierSpace x := by dsimp only [quadraticBarrierSpace]; positivity
      have hBar : B' ≤ quadraticBarrier δ K (x,t) := by
        calc
          B' ≤ δ*R^2 := hBR
          _ ≤ δ*quadraticBarrierSpace x := mul_le_mul_of_nonneg_left
            (by dsimp only [quadraticBarrierSpace]; rw [hxR]; linarith) hδ.le
          _ = δ*1*quadraticBarrierSpace x := by ring
          _ ≤ δ*Real.exp (K*t)*quadraticBarrierSpace x :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hExp hδ.le) hQuad0
          _ = quadraticBarrier δ K (x,t) := rfl
      have hUB : u (x,t) ≤ B' := (hBound (x,t) ⟨hxS,ht⟩).trans (le_max_left _ _)
      have htF := mul_nonneg ht.1 hF
      dsimp only [w]
      linarith
  have hOpSpace (f : Point n → ℝ) {q : Point n} (hq : q ∈ cylinder (closure O) 0 T) :
      linearOp (cylinder (closure O) 0 T) a b f q = linearOp (cylinder S 0 T) a b f q := by
    unfold linearOp
    rw [timeD_cylinder_change_space f hq.1 (hSpaceSub hq.1)]
  have hWOp : ∀ q ∈ O ×ˢ Ioc 0 T,
      linearOp (cylinder (closure O) 0 T) a b w q ≤ 0 := by
    intro q hq
    have hqLoc : q ∈ cylinder (closure O) 0 T := ⟨subset_closure hq.1,hq.2.1.le,hq.2.2⟩
    dsimp only [w]
    rw [linearOp_sub (a := a) (b := b) hLift hBarLoc hqLoc,linearOp_add_const,
      linearOp_sub_timeAffine hT huLoc F hqLoc,hOpSpace u hqLoc,
      hOpSpace (quadraticBarrier δ K) hqLoc]
    have hBarOp := quadraticBarrier_linearOp_pos hT hEll hM hb hδ (hSub hqLoc)
    have hUOp := hOp q ⟨hq.1.1,hq.2⟩
    change 0 < linearOp (cylinder S 0 T) a b (quadraticBarrier δ K) q at hBarOp
    linarith
  have hMax := maximum_principle (O := O) (hH.inter Metric.isOpen_ball) hCompact hT hw
    (elliptic_mono hEll hSub) hWInit hWLat hWOp
  have hpLoc : p ∈ cylinder (closure O) 0 T := by
    refine ⟨subset_closure ⟨hpInside,?_⟩,hp.2⟩
    simpa only [Metric.mem_ball,dist_zero_right] using hpR
  have h := hMax p hpLoc
  dsimp only [w] at h
  rw [hδeq] at h
  linarith

end Yau.Proofs.F05Aux
