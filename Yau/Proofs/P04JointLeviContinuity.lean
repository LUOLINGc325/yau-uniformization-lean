import Yau.Proofs.P04PoleJointRegularity

noncomputable section
open Set
open scoped Topology ContDiff

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs
variable {n : ℕ}

/-- Actual Levi matrices depend continuously on the joint regularization
parameter wherever the joint scalar function is smooth. -/
theorem joint_leviC_continuousOn {F : ℝ × ComplexVector n → ℝ}
    {U : Set (ℝ × ComplexVector n)} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) :
    ContinuousOn (fun p => leviC (fun z => F (p.1,z)) p.2) U := by
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ F) U := hF.fderiv_of_isOpen hU (by simp)
  have hDD : ContinuousOn (fderiv ℝ (fderiv ℝ F)) U :=
    hD.continuousOn_fderiv_of_isOpen hU (by simp)
  let H (v w : ComplexVector n) (p : ℝ × ComplexVector n) : ℝ :=
    fderiv ℝ (fderiv ℝ F) p (0,v) (0,w)
  have hC (v w : ComplexVector n) : ContinuousOn (H v w) U :=
    (hDD.clm_apply continuousOn_const).clm_apply continuousOn_const
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  let R (p : ℝ × ComplexVector n) : ℝ :=
    (1/4 : ℝ)*(H (stdVec j) (stdVec i) p+H (Complex.I • stdVec j) (Complex.I • stdVec i) p)
  let I (p : ℝ × ComplexVector n) : ℝ :=
    (1/4 : ℝ)*(H (stdVec j) (Complex.I • stdVec i) p-H (Complex.I • stdVec j) (stdVec i) p)
  have hR : ContinuousOn R U := continuousOn_const.mul ((hC _ _).add (hC _ _))
  have hI : ContinuousOn I U := continuousOn_const.mul ((hC _ _).sub (hC _ _))
  have hG : ContinuousOn (fun p => (R p : ℂ)+Complex.I*(I p : ℂ)) U :=
    (Complex.continuous_ofReal.comp_continuousOn hR).add
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hI))
  apply hG.congr
  rintro ⟨ε,z⟩ hp
  have hf : ContDiffAt ℝ 2 F (ε,z) :=
    ((hF (ε,z) hp).contDiffAt (hU.mem_nhds hp)).of_le (by simp)
  have hs : ContDiffAt ℝ 2 (fun w => F (ε,w)) z :=
    hf.comp z (contDiffAt_const.prodMk contDiffAt_id)
  have HH := L18Aux.leviMatrix_entry_re_im hs stdVec i j
  simp only [secondFDeriv_fixed_parameter hf] at HH
  apply Complex.ext
  · simpa only [leviC,Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,
      Complex.I_im,Complex.ofReal_im,zero_mul,one_mul,sub_zero,add_zero,R,H] using HH.1
  · simpa only [leviC,Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,
      Complex.I_im,Complex.ofReal_re,zero_mul,one_mul,zero_add,I,H] using HH.2

end Yau.Proofs.P04Aux
