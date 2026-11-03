import Yau.LeafProofs.L05PucciHarnackBump

open Filter MeasureTheory Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem harnack_second_scalar_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → ℝ} {s : E → ℝ} (hf : ContDiff ℝ 2 f) (hs : ContDiff ℝ 2 s) (x v w : E) :
    fderiv ℝ (fderiv ℝ (fun z => f (s z))) x v w=
      deriv (deriv f) (s x)*fderiv ℝ s x v*fderiv ℝ s x w+
        deriv f (s x)*fderiv ℝ (fderiv ℝ s) x v w := by
  have hEq : fderiv ℝ (fun z => f (s z))=fun z => deriv f (s z) • fderiv ℝ s z := by
    funext z
    exact ((hf.differentiable (by norm_num) (s z)).hasDerivAt.comp_hasFDerivAt z
      (hs.differentiable (by norm_num) z).hasFDerivAt).fderiv
  have hD1 := ((hf.differentiable_deriv_two (s x)).hasDerivAt).comp_hasFDerivAt x
    (hs.differentiable (by norm_num) x).hasFDerivAt
  have hD2 := ((hs.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x).hasFDerivAt
  have hd := hD1.smul hD2
  rw [hEq]
  have he : fderiv ℝ (fun z => deriv f (s z) • fderiv ℝ s z) x=
      deriv f (s x) • fderiv ℝ (fderiv ℝ s) x+
        (deriv (deriv f) (s x) • fderiv ℝ s x).smulRight (fderiv ℝ s x) := by
    convert! hd.fderiv using 1
  rw [he]
  simp only [add_apply,smul_apply,smul_eq_mul,ContinuousLinearMap.smulRight_apply]
  ring

theorem harnack_radial_level_hasFDerivAt {n : ℕ} (s : ℝ) (c x : Space n) :
    HasFDerivAt (fun z : Space n => s-‖z-c‖^2) ((-2 : ℝ) • spaceInnerBilin n (x-c)) x := by
  have h := (hasFDerivAt_const s x).sub (((hasFDerivAt_id x).sub_const c).norm_sq)
  convert! h using 1
  apply ContinuousLinearMap.ext
  intro v
  simp only [sub_apply,zero_apply,smul_apply,smul_eq_mul,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,innerSL_apply_apply]
  change -2*inner ℝ (x-c) v=0-2 • inner ℝ (id x-c) v
  simp only [id_eq,two_smul]
  ring

theorem harnack_radial_level_second {n : ℕ} (s : ℝ) (c x v w : Space n) :
    fderiv ℝ (fderiv ℝ (fun z : Space n => s-‖z-c‖^2)) x v w = -2*inner ℝ v w := by
  have hEq : fderiv ℝ (fun z : Space n => s-‖z-c‖^2)=fun z => (-2 : ℝ) • spaceInnerBilin n (z-c) := by
    funext z
    exact (harnack_radial_level_hasFDerivAt s c z).fderiv
  rw [hEq]
  have hd := ((spaceInnerBilin n).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const c)).const_smul (-2 : ℝ)
  have hd' : HasFDerivAt (fun z : Space n => (-2 : ℝ) • spaceInnerBilin n (z-c))
      ((-2 : ℝ) • spaceInnerBilin n) x := by
    convert! hd using 1
  rw [hd'.fderiv]
  simp only [smul_apply,smul_eq_mul]
  rfl

theorem harnack_radial_cube_second {n : ℕ} (s : ℝ) (c x v w : Space n) :
    fderiv ℝ (fderiv ℝ (fun z : Space n => harnackPositiveCube (s-‖z-c‖^2))) x v w=
      24*max (s-‖x-c‖^2) 0*inner ℝ (x-c) v*inner ℝ (x-c) w-
        6*(max (s-‖x-c‖^2) 0)^2*inner ℝ v w := by
  have hs : ContDiff ℝ 2 (fun z : Space n => s-‖z-c‖^2) :=
    contDiff_const.sub ((contDiff_id.sub contDiff_const).norm_sq ℝ)
  rw [harnack_second_scalar_comp harnack_positiveCube_contDiff hs,
    (harnack_positiveCube_deriv_hasDerivAt _).deriv,
    (harnack_positiveCube_hasDerivAt _).deriv,
    (harnack_radial_level_hasFDerivAt s c x).fderiv,harnack_radial_level_second]
  simp only [smul_apply,smul_eq_mul]
  change 6*max (s-‖x-c‖^2) 0*((-2)*inner ℝ (x-c) v)*((-2)*inner ℝ (x-c) w)+
    3*(max (s-‖x-c‖^2) 0)^2*((-2)*inner ℝ v w)=_
  ring

def harnackRankOne {n : ℕ} (y : Space n) : Mat n :=
  Matrix.vecMulVec (fun i => inner ℝ y (Yau.realVec i)) (fun i => inner ℝ y (Yau.realVec i))

theorem harnack_rankOne_posSemidef {n : ℕ} (y : Space n) : (harnackRankOne y).PosSemidef := by
  simpa only [harnackRankOne,Pi.star_apply,star_trivial] using
    Matrix.posSemidef_vecMulVec_self_star (fun i : Yau.RIdx n => inner ℝ y (Yau.realVec i))

theorem harnack_rankOne_trace {n : ℕ} (y : Space n) : Matrix.trace (harnackRankOne y)=‖y‖^2 := by
  rw [harnackRankOne,Matrix.trace_vecMulVec]
  have h := (complexVector_realOrthonormalBasis n).sum_sq_inner_left y
  simpa only [dotProduct,pow_two,complexVector_realOrthonormalBasis_apply] using h

theorem harnack_radial_cube_hessian {n : ℕ} (s : ℝ) (c : Space n) (p : Point n) :
    (hessian (fun z : Point n => harnackPositiveCube (s-‖z.1-c‖^2)) p : Mat n)=
      (24*max (s-‖p.1-c‖^2) 0) • harnackRankOne (p.1-c)-
        (6*(max (s-‖p.1-c‖^2) 0)^2) • (1 : Mat n) := by
  have hRaw : (fun i j : Yau.RIdx n =>
      spatialDD (fun z : Point n => harnackPositiveCube (s-‖z.1-c‖^2)) p
        (Yau.realVec i) (Yau.realVec j))=
      (24*max (s-‖p.1-c‖^2) 0) • harnackRankOne (p.1-c)-
        (6*(max (s-‖p.1-c‖^2) 0)^2) • (1 : Mat n) := by
    ext i j
    change fderiv ℝ (fderiv ℝ (fun x : Space n => harnackPositiveCube (s-‖x-c‖^2))) p.1
      (Yau.realVec i) (Yau.realVec j)=_
    rw [harnack_radial_cube_second]
    have hBasis := (complexVector_realOrthonormalBasis n).inner_eq_ite i j
    simp only [complexVector_realOrthonormalBasis_apply] at hBasis
    rw [hBasis]
    change _ = (24*max (s-‖p.1-c‖^2) 0)*
      (inner ℝ (p.1-c) (Yau.realVec i)*inner ℝ (p.1-c) (Yau.realVec j))-
      (6*(max (s-‖p.1-c‖^2) 0)^2)*(if i=j then 1 else 0)
    ring
  unfold hessian
  rw [hRaw]
  apply IsSelfAdjoint.coe_selfAdjointPart_apply
  exact (IsSelfAdjoint.smul (IsSelfAdjoint.all _)
    (harnack_rankOne_posSemidef (p.1-c)).isHermitian.isSelfAdjoint).sub
    (IsSelfAdjoint.smul (IsSelfAdjoint.all _) (IsSelfAdjoint.one (Mat n)))

end Yau.LeafProofs.L05Aux
