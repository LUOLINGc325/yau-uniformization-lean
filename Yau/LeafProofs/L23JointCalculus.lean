import Yau.LeafProofs.L23TensorAlgebra

/-! Ordinary space and time derivatives of a joint chart function. -/

noncomputable section
open Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem joint_spatial_direction (F : ComplexVector n × ℝ → ℝ)
    (z : ComplexVector n) (t : ℝ) (hF : DifferentiableAt ℝ F (z,t)) (i : RIdx n) :
    rDeriv (fun w => F (w,t)) z i=fderiv ℝ F (z,t) (realVec i,0) := by
  have hmap : HasFDerivAt (fun w : ComplexVector n => (w,t))
      ((ContinuousLinearMap.id ℝ (ComplexVector n)).prod 0) z :=
    (hasFDerivAt_id z).prodMk (hasFDerivAt_const t z)
  have hc := (hF.hasFDerivAt.comp z hmap).fderiv
  have he := congrArg (fun L : ComplexVector n →L[ℝ] ℝ => L (realVec i)) hc
  simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply,zero_apply,rDeriv] using he

theorem joint_time_direction (F : ComplexVector n × ℝ → ℝ)
    (z : ComplexVector n) (t : ℝ) (hF : DifferentiableAt ℝ F (z,t)) :
    deriv (fun s => F (z,s)) t=fderiv ℝ F (z,t) (0,1) := by
  have hmap : HasDerivAt (fun s : ℝ => (z,s)) (0,1) t :=
    (hasDerivAt_const t z).prodMk (hasDerivAt_id t)
  simpa only [Function.comp_def] using (hF.hasFDerivAt.comp_hasDerivAt t hmap).deriv

theorem joint_spatial_derivative_contDiffOn (F : ComplexVector n × ℝ → ℝ)
    (U : Set (ComplexVector n × ℝ)) (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (i : RIdx n) : ContDiffOn ℝ ∞ (fun p => rDeriv (fun w => F (w,p.2)) p.1 i) U := by
  have hs : ContDiffOn ℝ ∞ (fun p => fderiv ℝ F p (realVec i,0)) U :=
    (hF.fderiv_of_isOpen hU (by simp)).clm_apply
    (contDiffOn_const (c := (realVec i,0)))
  apply hs.congr
  intro p hp
  exact joint_spatial_direction F p.1 p.2
    ((hF.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)) i

theorem joint_time_derivative_contDiffOn (F : ComplexVector n × ℝ → ℝ)
    (U : Set (ComplexVector n × ℝ)) (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) :
    ContDiffOn ℝ ∞ (fun p => deriv (fun s => F (p.1,s)) p.2) U := by
  have hs : ContDiffOn ℝ ∞ (fun p => fderiv ℝ F p (0,1)) U :=
    (hF.fderiv_of_isOpen hU (by simp)).clm_apply
    (contDiffOn_const (c := (0,1)))
  apply hs.congr
  intro p hp
  exact joint_time_direction F p.1 p.2
    ((hF.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp))

theorem joint_spatial_time_hasDerivAt (F : ComplexVector n × ℝ → ℝ)
    (z : ComplexVector n) (t : ℝ) (hF : ContDiffAt ℝ 2 F (z,t)) (i : RIdx n) :
    HasDerivAt (fun s => rDeriv (fun w => F (w,s)) z i)
      (rDeriv (fun w => deriv (fun s => F (w,s)) t) z i) t := by
  have hDF : DifferentiableAt ℝ (fderiv ℝ F) (z,t) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hmapT : HasDerivAt (fun s : ℝ => (z,s)) (0,1) t :=
    (hasDerivAt_const t z).prodMk (hasDerivAt_id t)
  have hT : HasDerivAt (fun s => fderiv ℝ F (z,s) (realVec i,0))
      (fderiv ℝ (fderiv ℝ F) (z,t) (0,1) (realVec i,0)) t := by
    simpa only [Function.comp_def,map_zero,add_zero] using
      (hDF.hasFDerivAt.comp_hasDerivAt t hmapT).clm_apply
        (hasDerivAt_const t (realVec i,0))
  have hS : HasFDerivAt (fun w => fderiv ℝ F (w,t) (0,1))
      (((fderiv ℝ (fderiv ℝ F) (z,t)).comp
        ((ContinuousLinearMap.id ℝ (ComplexVector n)).prod 0)).flip (0,1)) z := by
    have hmapS : HasFDerivAt (fun w : ComplexVector n => (w,t))
        ((ContinuousLinearMap.id ℝ (ComplexVector n)).prod 0) z :=
      (hasFDerivAt_id z).prodMk (hasFDerivAt_const t z)
    simpa only [Function.comp_def,ContinuousLinearMap.comp_zero,zero_add] using
      (hDF.hasFDerivAt.comp z hmapS).clm_apply (hasFDerivAt_const (0,1) z)
  have hnear : ∀ᶠ p in 𝓝 (z,t), DifferentiableAt ℝ F p :=
    (hF.eventually (by norm_num)).mono
      (fun _ hp => hp.differentiableAt (by norm_num))
  have hnearS : ∀ᶠ w in 𝓝 z, DifferentiableAt ℝ F (w,t) :=
    (continuousAt_id.prodMk continuousAt_const).preimage_mem_nhds hnear
  have hnearT : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ F (z,s) :=
    (continuousAt_const.prodMk continuousAt_id).preimage_mem_nhds hnear
  have htimeEq : (fun w => deriv (fun s => F (w,s)) t)=ᶠ[𝓝 z]
      (fun w => fderiv ℝ F (w,t) (0,1)) :=
    hnearS.mono (fun w hw => joint_time_direction F w t hw)
  have hSpaceValue : rDeriv (fun w => deriv (fun s => F (w,s)) t) z i=
      fderiv ℝ (fderiv ℝ F) (z,t) (realVec i,0) (0,1) := by
    unfold rDeriv
    rw [htimeEq.fderiv_eq,hS.fderiv]
    rfl
  rw [hSpaceValue,hF.isSymmSndFDerivAt (by norm_num) (realVec i,0) (0,1)]
  apply hT.congr_of_eventuallyEq
  exact hnearT.mono (fun s hs => joint_spatial_direction F z s hs i)

end Yau.LeafProofs.L23Aux
