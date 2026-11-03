import Yau.Proofs.F03AffineSecondDerivative
import Yau.Proofs.F03KernelProductCoordinates

/-! Actual left/right Hessians under the product chart equivalence. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau Parabolic
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000

def kernelSliceLeftLinear (n : ℕ) : Point n →L[ℝ] ((Space n × Space n) × ℝ) :=
  ((ContinuousLinearMap.fst ℝ (Space n) ℝ).prod 0).prod (ContinuousLinearMap.snd ℝ (Space n) ℝ)

def kernelSliceRightLinear (n : ℕ) : Point n →L[ℝ] ((Space n × Space n) × ℝ) :=
  ((0 : Point n →L[ℝ] Space n).prod (ContinuousLinearMap.fst ℝ (Space n) ℝ)).prod
    (ContinuousLinearMap.snd ℝ (Space n) ℝ)

theorem kernelPairTimePack_symm_realVec_left (n : ℕ) (i : RIdx n) :
    (kernelPairTimePack n).symm (realVec (kernelRealIndexLeft n i),0)=((realVec i,0),0) := by
  change ((kernelPairPack n).symm (realVec (kernelRealIndexLeft n i)),0)=_
  rw [kernelPairPack_symm_realVec_left]

theorem kernelPairTimePack_symm_realVec_right (n : ℕ) (i : RIdx n) :
    (kernelPairTimePack n).symm (realVec (kernelRealIndexRight n i),0)=((0,realVec i),0) := by
  change ((kernelPairPack n).symm (realVec (kernelRealIndexRight n i)),0)=_
  rw [kernelPairPack_symm_realVec_right]

theorem kernelProductHessian_left {n : ℕ} (f : ((Space n × Space n) × ℝ) → ℝ) (p : Point (n+n))
    (hf : ContDiffAt ℝ 2 f ((kernelPairTimePack n).symm p)) (i j : RIdx n) :
    spatialDD (fun q => f ((kernelPairTimePack n).symm q)) p
        (realVec (kernelRealIndexLeft n i)) (realVec (kernelRealIndexLeft n j))=
      spatialDD (fun q : Point n => f ((q.1,((kernelPairPack n).symm p.1).2),q.2))
        (((kernelPairPack n).symm p.1).1,p.2) (realVec i) (realVec j) := by
  let P := (kernelPairTimePack n).symm.toContinuousLinearMap
  let x := ((kernelPairPack n).symm p.1).1
  let y := ((kernelPairPack n).symm p.1).2
  let L := kernelSliceLeftLinear n
  have hSlice : (fun q : Point n => f ((q.1,y),q.2))=(fun q => f (L q+((0,y),0))) := by
    funext q
    congr 1
    simp only [L,kernelSliceLeftLinear,ContinuousLinearMap.prod_apply,ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd',ContinuousLinearMap.zero_apply,Prod.mk_add_mk,add_zero,zero_add]
  have hfp : ContDiffAt ℝ 2 f (P p) := by
    change ContDiffAt ℝ 2 f ((kernelPairTimePack n).symm p)
    exact hf
  have hLpoint : L (x,p.2)+((0,y),0)=P p := by
    simp [L,kernelSliceLeftLinear,P,kernelPairTimePack,x,y,Prod.map]
  have hAt : ContDiffAt ℝ 2 f (L (x,p.2)+((0,y),0)) := by
    rw [hLpoint]
    exact hfp
  have hComp : ContDiffAt ℝ 2 (fun q => f ((kernelPairTimePack n).symm q)) p :=
    hf.comp p (kernelPairTimePack n).symm.contDiff.contDiffAt
  have hLeft : ContDiffAt ℝ 2 (fun q : Point n => f ((q.1,y),q.2)) (x,p.2) := by
    rw [hSlice]
    exact ContDiffAt.comp (f := fun q : Point n => L q+((0,y),0)) (g := f) (x,p.2)
      hAt (L.contDiff.add contDiff_const).contDiffAt
  rw [spatialDD_eq_joint_second _ _ hComp,spatialDD_eq_joint_second _ _ hLeft]
  have hPacked := affine_secondFDeriv P 0 f p (by simpa only [add_zero] using hfp)
    (realVec (kernelRealIndexLeft n i),0) (realVec (kernelRealIndexLeft n j),0)
  have hSliced := affine_secondFDeriv L ((0,y),0) f (x,p.2) hAt (realVec i,0) (realVec j,0)
  rw [← hSlice] at hSliced
  simp only [add_zero] at hPacked
  change fderiv ℝ (fderiv ℝ (fun q => f (P q))) p
      (realVec (kernelRealIndexLeft n i),0) (realVec (kernelRealIndexLeft n j),0)=_
  rw [hPacked,hSliced,hLpoint]
  simp only [P,ContinuousLinearEquiv.coe_coe,kernelPairTimePack_symm_realVec_left,L,kernelSliceLeftLinear,
    ContinuousLinearMap.prod_apply,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.zero_apply,Prod.mk_add_mk,add_zero,zero_add,x,y]

theorem kernelProductHessian_right {n : ℕ} (f : ((Space n × Space n) × ℝ) → ℝ) (p : Point (n+n))
    (hf : ContDiffAt ℝ 2 f ((kernelPairTimePack n).symm p)) (i j : RIdx n) :
    spatialDD (fun q => f ((kernelPairTimePack n).symm q)) p
        (realVec (kernelRealIndexRight n i)) (realVec (kernelRealIndexRight n j))=
      spatialDD (fun q : Point n => f ((((kernelPairPack n).symm p.1).1,q.1),q.2))
        (((kernelPairPack n).symm p.1).2,p.2) (realVec i) (realVec j) := by
  let P := (kernelPairTimePack n).symm.toContinuousLinearMap
  let x := ((kernelPairPack n).symm p.1).1
  let y := ((kernelPairPack n).symm p.1).2
  let L := kernelSliceRightLinear n
  have hSlice : (fun q : Point n => f ((x,q.1),q.2))=(fun q => f (L q+((x,0),0))) := by
    funext q
    congr 1
    simp only [L,kernelSliceRightLinear,ContinuousLinearMap.prod_apply,ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd',ContinuousLinearMap.zero_apply,Prod.mk_add_mk,add_zero,zero_add]
  have hfp : ContDiffAt ℝ 2 f (P p) := by
    change ContDiffAt ℝ 2 f ((kernelPairTimePack n).symm p)
    exact hf
  have hLpoint : L (y,p.2)+((x,0),0)=P p := by
    simp [L,kernelSliceRightLinear,P,kernelPairTimePack,x,y,Prod.map]
  have hAt : ContDiffAt ℝ 2 f (L (y,p.2)+((x,0),0)) := by
    rw [hLpoint]
    exact hfp
  have hComp : ContDiffAt ℝ 2 (fun q => f ((kernelPairTimePack n).symm q)) p :=
    hf.comp p (kernelPairTimePack n).symm.contDiff.contDiffAt
  have hRight : ContDiffAt ℝ 2 (fun q : Point n => f ((x,q.1),q.2)) (y,p.2) := by
    rw [hSlice]
    exact ContDiffAt.comp (f := fun q : Point n => L q+((x,0),0)) (g := f) (y,p.2)
      hAt (L.contDiff.add contDiff_const).contDiffAt
  rw [spatialDD_eq_joint_second _ _ hComp,spatialDD_eq_joint_second _ _ hRight]
  have hPacked := affine_secondFDeriv P 0 f p (by simpa only [add_zero] using hfp)
    (realVec (kernelRealIndexRight n i),0) (realVec (kernelRealIndexRight n j),0)
  have hSliced := affine_secondFDeriv L ((x,0),0) f (y,p.2) hAt (realVec i,0) (realVec j,0)
  rw [← hSlice] at hSliced
  simp only [add_zero] at hPacked
  change fderiv ℝ (fderiv ℝ (fun q => f (P q))) p
      (realVec (kernelRealIndexRight n i),0) (realVec (kernelRealIndexRight n j),0)=_
  rw [hPacked,hSliced,hLpoint]
  simp only [P,ContinuousLinearEquiv.coe_coe,kernelPairTimePack_symm_realVec_right,L,kernelSliceRightLinear,
    ContinuousLinearMap.prod_apply,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.zero_apply,Prod.mk_add_mk,add_zero,zero_add,x,y]

end Yau.Proofs.F03Aux
