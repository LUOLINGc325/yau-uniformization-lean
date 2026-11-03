import Yau.Proofs.E02PeanoUnique
import Yau.Proofs.E02MatrixBasic

open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace Yau.NodeProofs.E02Aux
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- The actual rectangular Levi is real-linear in C² germs. This uses
only the unique actual scalar Hessians, not any derivative of uκ. -/
theorem rectLevi_sub_const_mul {n m : ℕ} {f g : Rect n m → ℝ} {M : Rect n m}
    (hf : ContDiffAt ℝ 2 f M) (hg : ContDiffAt ℝ 2 g M) (c : ℝ) (Z : Rect n m) :
    rectLevi (fun N => f N-c*g N) M Z = rectLevi f M Z-c*rectLevi g M Z := by
  have hJ := realSecondJet_add (realSecondJet_of_contDiffAt_two hf)
    (realSecondJet_const_mul (realSecondJet_of_contDiffAt_two hg) (-c))
  have hJet : RealSecondJet (fun N => f N-c*g N) M
      (fderiv ℝ f M+(-c) • fderiv ℝ g M)
      (fderiv ℝ (fderiv ℝ f) M+(-c) • fderiv ℝ (fderiv ℝ g) M) := by
    have hFun : (fun N => f N-c*g N) = (fun N => f N+(-c)*g N) := by
      funext N
      ring
    rw [hFun]
    exact hJ
  have hSecond := realSecondJet_second_fderiv_eq hJet (hf.sub (contDiffAt_const.mul hg))
  unfold rectLevi
  erw [hSecond]
  simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul]
  ring

end Yau.NodeProofs.E02Aux
