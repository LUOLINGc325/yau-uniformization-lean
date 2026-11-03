import Yau.Proofs.F03DirectionalJets

/-! Actual joint C2 germs supply the native parabolic C2 cylinder class. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau Parabolic
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem joint_spatial_fderiv_contDiffAt {E B : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    {u : E × ℝ → B} {p : E × ℝ} {m : ℕ∞ω}
    (hu : ContDiffAt ℝ (m+1) u p) :
    ContDiffAt ℝ m (fun q : E × ℝ => fderiv ℝ (fun x => u (x,q.2)) q.1) p := by
  have hF : ContDiffAt ℝ (m+1)
      (Function.uncurry (fun q : E × ℝ => fun x : E => u (x,q.2))) (p,p.1) :=
    hu.comp (p,p.1) (contDiffAt_snd.prodMk contDiffAt_fst.snd)
  exact hF.fderiv_succ contDiffAt_fst

theorem joint_time_fderiv_contDiffAt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E × ℝ → ℝ} {p : E × ℝ} {m : ℕ∞ω}
    (hu : ContDiffAt ℝ (m+1) u p) :
    ContDiffAt ℝ m (fun q : E × ℝ => deriv (fun s => u (q.1,s)) q.2) p := by
  have hF : ContDiffAt ℝ (m+1)
      (Function.uncurry (fun q : E × ℝ => fun s : ℝ => u (q.1,s))) (p,p.2) :=
    hu.comp (p,p.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  exact (hF.fderiv_succ contDiffAt_snd).clm_apply contDiffAt_const

/-- Only a genuine C2 neighbourhood is used. The derivative on both closed
time faces is the native one-sided derivative of the same function. -/
theorem parabolic_c2_of_joint_contDiffOn {n : ℕ} {S : Set (Space n)}
    {T : ℝ} (hT : 0 < T) {Q : Set (Point n)} (hQ : IsOpen Q)
    {u : Point n → ℝ} (hu : ContDiffOn ℝ 2 u Q)
    (hsub : cylinder S 0 T ⊆ Q) : C2 (cylinder S 0 T) u := by
  have hAt (p : Point n) (hp : p ∈ cylinder S 0 T) : ContDiffAt ℝ 2 u p :=
    hu.contDiffAt (hQ.mem_nhds (hsub hp))
  have hGrad (p : Point n) (hp : p ∈ cylinder S 0 T) :
      ContDiffAt ℝ 1 (spatialD u) p := joint_spatial_fderiv_contDiffAt (hAt p hp)
  have hHess (p : Point n) (hp : p ∈ cylinder S 0 T) :
      ContDiffAt ℝ 0 (spatialDD u) p := by
    change ContDiffAt ℝ 0
      (fun q : Point n => fderiv ℝ (fun x => spatialD u (x,q.2)) q.1) p
    exact joint_spatial_fderiv_contDiffAt (m := 0) (hGrad p hp)
  have hTime (p : Point n) (hp : p ∈ cylinder S 0 T) :
      ContinuousAt (fun q : Point n => deriv (fun s => u (q.1,s)) q.2) p :=
    (joint_time_fderiv_contDiffAt (m := 1) (hAt p hp)).continuousAt
  have hSlice (p : Point n) (hp : p ∈ cylinder S 0 T) :
      DifferentiableAt ℝ (fun s => u (p.1,s)) p.2 :=
    ((hAt p hp).comp p.2 (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by norm_num)
  have hTimeEq (p : Point n) (hp : p ∈ cylinder S 0 T) :
      timeD (cylinder S 0 T) u p = deriv (fun s => u (p.1,s)) p.2 := by
    have hFiber : {t | (p.1,t) ∈ cylinder S 0 T} = Icc 0 T := by
      ext t
      simp only [cylinder,mem_setOf_eq,mem_prod,hp.1,true_and]
    unfold timeD
    rw [hFiber]
    exact (hSlice p hp).hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hT p.2 hp.2)
  refine ⟨hu.continuousOn.mono hsub,?_,?_,?_,?_,?_⟩
  · exact fun p hp => (hGrad p hp).continuousAt.continuousWithinAt
  · exact fun p hp => (hHess p hp).continuousAt.continuousWithinAt
  · apply ContinuousOn.congr (f := fun q : Point n => deriv (fun s => u (q.1,s)) q.2)
      (fun p hp => (hTime p hp).continuousWithinAt)
    exact hTimeEq
  · intro p hp
    exact (hAt p hp).comp p.1 (contDiffAt_id.prodMk contDiffAt_const)
  · intro p hp
    exact (hSlice p hp).differentiableWithinAt

end Yau.Proofs.F03Aux
