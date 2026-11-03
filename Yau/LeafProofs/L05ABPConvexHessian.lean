import Yau.LeafProofs.L05ABPMollifierPeano
import Mathlib.Analysis.Convex.Deriv

noncomputable section

open Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

theorem smooth_convex_secondFDeriv_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hc : ConvexOn ℝ Set.univ f) (x v : E) :
    0≤fderiv ℝ (fderiv ℝ f) x v v := by
  let g : ℝ → ℝ := fun t => f (x+t • v)
  have hg : ContDiff ℝ ∞ g := by dsimp only [g]; fun_prop
  have hgc : ConvexOn ℝ Set.univ g := by
    convert! hc.comp_affineMap (AffineMap.lineMap x (x+v)) using 1
    funext t
    rw [Function.comp_apply,AffineMap.lineMap_apply_module',add_sub_cancel_left,add_comm]
  have hm : Monotone (deriv g) := by
    simpa only [monotoneOn_univ] using hgc.monotoneOn_deriv
      (fun t _ => hg.differentiable (by simp) t)
  have hn : 0≤deriv (deriv g) 0 := hm.deriv_nonneg
  have hfun : deriv g=fun t => fderiv ℝ f (x+t • v) v := by
    funext t
    exact (hf.differentiable (by simp) (x+t • v)).deriv_comp_add_smul
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  have hdv : DifferentiableAt ℝ (fun y => fderiv ℝ f y v) (x+(0:ℝ) • v) := by
    simpa using hdf.clm_apply (differentiableAt_const v)
  have hd2 : deriv (fun t : ℝ => fderiv ℝ f (x+t • v) v) 0=
      fderiv ℝ (fderiv ℝ f) x v v := by
    rw [hdv.deriv_comp_add_smul]
    simp only [zero_smul,add_zero]
    rw [fderiv_clm_apply hdf (differentiableAt_const v)]
    simp
  rwa [hfun,hd2] at hn

theorem jointHessian_add {n : ℕ} (A B : Point n →L[ℝ] Point n →L[ℝ] ℝ) :
    jointHessian (A+B)=jointHessian A+jointHessian B := by
  exact (selfAdjointPart ℝ).map_add _ _

theorem hessian_add_smooth {n : ℕ} {u v : Point n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (z : Point n) :
    hessian (u+v) z=hessian u z+hessian v z := by
  have hf : fderiv ℝ (u+v)=fderiv ℝ u+fderiv ℝ v := by
    funext q
    exact fderiv_fun_add (hu.differentiable (by simp) q) (hv.differentiable (by simp) q)
  have hdu : ContDiff ℝ ∞ (fderiv ℝ u) := hu.fderiv_right (by simp)
  have hdv : ContDiff ℝ ∞ (fderiv ℝ v) := hv.fderiv_right (by simp)
  have hsum : ContDiff ℝ ∞ (u+v) := by convert! hu.add hv using 1
  rw [hessian_eq_jointHessian hsum,hessian_eq_jointHessian hu,hessian_eq_jointHessian hv,hf]
  have ha : fderiv ℝ (fderiv ℝ u+fderiv ℝ v) z=
      fderiv ℝ (fderiv ℝ u) z+fderiv ℝ (fderiv ℝ v) z := by
    convert! fderiv_fun_add (hdu.differentiable (by simp) z) (hdv.differentiable (by simp) z) using 1
  rw [ha,jointHessian_add]

theorem spatial_quadratic_hessian {n : ℕ} (K : ℝ) (z : Point n) :
    (hessian (fun q : Point n => (K/2)*qnorm2 q) z : Mat n)=K • (1 : Mat n) := by
  have hf : (fun q : Point n => (K/2)*qnorm2 q)=
      peanoPolynomial 0 (0 : Point n) 0 0 (K/2) := by
    funext q
    simp [peanoPolynomial]
  rw [hf,peanoPolynomial_hessian 0 0 0 0 (by simp) (K/2) z]
  have he : (fun i j : Yau.RIdx n => (0 : Point n →L[ℝ] Point n →L[ℝ] ℝ)
      (Yau.realVec i,0) (Yau.realVec j,0)+(2*(K/2))*inner ℝ (Yau.realVec i) (Yau.realVec j))=
      K • (1 : Mat n) := by
    funext i j
    have hi := (complexVector_realOrthonormalBasis n).inner_eq_ite i j
    simp only [complexVector_realOrthonormalBasis_apply] at hi
    have hk : 2*(K/2)=K := by ring
    rw [hi,hk]
    by_cases hij : i=j <;> simp [hij]
  rw [he]
  apply IsSelfAdjoint.coe_selfAdjointPart_apply
  exact IsSelfAdjoint.smul (IsSelfAdjoint.all K) (IsSelfAdjoint.one (Mat n))

theorem smooth_convex_hessian_posSemidef {n : ℕ} {u : Point n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hc : ConvexOn ℝ Set.univ u) (z : Point n) :
    (hessian u z : Mat n).PosSemidef := by
  have hnon (v : Space n) : 0 ≤ spatialDD u z v v := by
    have hh := smooth_convex_secondFDeriv_nonneg hu hc z ((v,0) : Point n)
    have he := congrArg (fun B : Space n →L[ℝ] Space n →L[ℝ] ℝ => B v v)
      (spatialDD_eq_joint_second hu z)
    exact he.trans_ge hh
  have hs : ContDiffAt ℝ 2 (fun x : Space n => u (x,z.2)) z.1 :=
    (hu.comp (contDiff_id.prodMk contDiff_const)).contDiffAt.of_le (by simp)
  have hraw : (hessian u z : Mat n)=secondFDerivMatrix (fun x => u (x,z.2)) z.1 :=
    hessian_space_eq_secondFDeriv hs
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (Matrix.isHermitian_iff_isSelfAdjoint.mpr (hessian u z).property)
  intro v
  have hh := hnon (∑ i, v i • Yau.realVec i)
  simp only [map_sum,map_smul,sum_apply,smul_apply,Finset.mul_sum,smul_eq_mul] at hh
  rw [hraw]
  simp only [dotProduct,Matrix.mulVec,secondFDerivMatrix,Pi.star_apply,star_trivial,Finset.mul_sum]
  change 0≤∑ i,∑ j,v i*(spatialDD u z (Yau.realVec i) (Yau.realVec j)*v j)
  have he : (∑ i,∑ j,v i*(spatialDD u z (Yau.realVec i) (Yau.realVec j)*v j))=
      ∑ i,∑ j,v i*(v j*spatialDD u z (Yau.realVec j) (Yau.realVec i)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rwa [he]

theorem smooth_jointSemiconvex_hessian_lower {n : ℕ} {u : Point n → ℝ} {K : ℝ}
    (hu : ContDiff ℝ ∞ u) (hc : jointSemiconvex K u) (z : Point n) :
    ((hessian u z : Mat n)+K • (1 : Mat n)).PosSemidef := by
  have hq : ContDiff ℝ ∞ (fun q : Point n => (K/2)*qnorm2 q) :=
    contDiff_const.mul (qnorm2_smooth n)
  have hh := smooth_convex_hessian_posSemidef (hu.add hq) hc z
  change (hessian (u+(fun q : Point n => (K/2)*qnorm2 q)) z : Mat n).PosSemidef at hh
  rw [hessian_add_smooth hu hq,AddSubgroup.coe_add,spatial_quadratic_hessian] at hh
  exact hh

end Yau.LeafProofs.L05Aux
