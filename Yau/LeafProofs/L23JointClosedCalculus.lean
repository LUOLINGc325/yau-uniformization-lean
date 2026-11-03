import Yau.LeafProofs.L23JointCalculus
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.Calculus.TangentCone.Real

/-! Spatial derivatives retain joint regularity at both closed time faces. -/

noncomputable section
open Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem joint_spatial_direction_within (F : ComplexVector n × ℝ → ℝ)
    (S : Set (ComplexVector n)) (I : Set ℝ) (hS : IsOpen S)
    {z : ComplexVector n} (hz : z ∈ S) {t : ℝ} (ht : t ∈ I)
    (hF : DifferentiableWithinAt ℝ F (S ×ˢ I) (z,t)) (i : RIdx n) :
    rDeriv (fun w => F (w,t)) z i=
      fderivWithin ℝ F (S ×ˢ I) (z,t) (realVec i,0) := by
  have hmap : HasFDerivAt (fun w : ComplexVector n => (w,t))
      ((ContinuousLinearMap.id ℝ (ComplexVector n)).prod 0) z :=
    (hasFDerivAt_id z).prodMk (hasFDerivAt_const t z)
  have hc := (hF.hasFDerivWithinAt.comp z hmap.hasFDerivWithinAt
    (show Set.MapsTo (fun w : ComplexVector n => (w,t)) S (S ×ˢ I) from
      fun w hw => ⟨hw,ht⟩)).hasFDerivAt (hS.mem_nhds hz)
  have he := congrArg (fun L : ComplexVector n →L[ℝ] ℝ => L (realVec i)) hc.fderiv
  simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply,zero_apply,rDeriv] using he

theorem joint_spatial_derivative_contDiffOn_closedInterval
    (F : ComplexVector n × ℝ → ℝ) (S : Set (ComplexVector n)) (hS : IsOpen S)
    (a b : ℝ) (hab : a < b) (hF : ContDiffOn ℝ ∞ F (S ×ˢ Set.Icc a b))
    (i : RIdx n) :
    ContDiffOn ℝ ∞ (fun p => rDeriv (fun w => F (w,p.2)) p.1 i) (S ×ˢ Set.Icc a b) := by
  have hu : UniqueDiffOn ℝ (S ×ˢ Set.Icc a b) :=
    hS.uniqueDiffOn.prod (uniqueDiffOn_Icc hab)
  have hs : ContDiffOn ℝ ∞ (fun p =>
      fderivWithin ℝ F (S ×ˢ Set.Icc a b) p (realVec i,0)) (S ×ˢ Set.Icc a b) :=
    (hF.fderivWithin hu (by simp)).clm_apply (contDiffOn_const (c := (realVec i,0)))
  apply hs.congr
  intro p hp
  exact joint_spatial_direction_within F S (Set.Icc a b) hS hp.1 hp.2
    ((hF p hp).differentiableWithinAt (by simp)) i

end Yau.LeafProofs.L23Aux
