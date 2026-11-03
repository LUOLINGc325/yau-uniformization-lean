import Yau.LeafProofs.L05ABPGeometry
import Yau.LeafProofs.L16

noncomputable section

open Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

theorem timeD_univ_eq_joint {n : ℕ} {u : Point n → ℝ} {z : Point n}
    (hu : DifferentiableAt ℝ u z) : timeD Set.univ u z = fderiv ℝ u z (0,1) := by
  have hh : HasDerivAt (fun t => (z.1,t)) ((0,1) : Point n) z.2 :=
    (hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2)
  simpa [timeD,Function.comp_def] using
    (hu.hasFDerivAt.comp_hasDerivAt z.2 hh).deriv

theorem joint_fderiv_decompose {n : ℕ} {u : Point n → ℝ} {z : Point n}
    (hu : DifferentiableAt ℝ u z) (v : Point n) :
    fderiv ℝ u z v = inner ℝ (spatialGrad u z) v.1+timeD Set.univ u z*v.2 := by
  have he : v = (v.1,0)+v.2 • ((0,1) : Point n) := by ext <;> simp
  have hs := congrArg (fun L : Space n →L[ℝ] ℝ => L v.1) (spatialD_eq_joint hu)
  change spatialD u z v.1 = fderiv ℝ u z (v.1,0) at hs
  calc
    _ = fderiv ℝ u z (v.1,0)+v.2*fderiv ℝ u z (0,1) := by
      conv_lhs => rw [he,map_add,map_smul]
      rfl
    _ = _ := by rw [spatialGrad_inner,hs,timeD_univ_eq_joint hu]; ring

def abpBlockDerivative {n : ℕ} (x : Space n) (dg : Point n →L[ℝ] Space n) (a : ℝ) :
    Point n →L[ℝ] Point n :=
  dg.prod (a • ContinuousLinearMap.snd ℝ (Space n) ℝ-(innerSL ℝ x).comp dg)

theorem contactMap_fderiv_eq_block {n : ℕ} {u : Point n → ℝ}
    (hu : ContDiff ℝ ∞ u) (z : Point n) :
    fderiv ℝ (contactMap u) z =
      abpBlockDerivative z.1 (fderiv ℝ (spatialGrad u) z) (timeD Set.univ u z) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [contactMap_derivative_apply hu,joint_fderiv_decompose (hu.differentiable (by simp) z)]
  apply Prod.ext
  · rfl
  · change inner ℝ (spatialGrad u z) v.1+timeD Set.univ u z*v.2-
      inner ℝ (spatialGrad u z) v.1-inner ℝ z.1 (fderiv ℝ (spatialGrad u) z v) =
      timeD Set.univ u z*v.2-inner ℝ z.1 (fderiv ℝ (spatialGrad u) z v)
    ring

def abpJointBasis (n : ℕ) : Module.Basis (RIdx n ⊕ Unit) ℝ (Point n) :=
  (complexVector_realOrthonormalBasis n).toBasis.prod (Module.Basis.singleton Unit ℝ)

def abpSpatialBlock {n : ℕ} (dg : Point n →L[ℝ] Space n) : Mat n :=
  LinearMap.toMatrix (complexVector_realOrthonormalBasis n).toBasis
    (complexVector_realOrthonormalBasis n).toBasis
    (dg.comp (ContinuousLinearMap.inl ℝ (Space n) ℝ)).toLinearMap

def abpTimeColumn {n : ℕ} (dg : Point n →L[ℝ] Space n) : Matrix (RIdx n) Unit ℝ :=
  fun i _ => inner ℝ (complexVector_realOrthonormalBasis n i) (dg (0,1))

def abpSpaceRow {n : ℕ} (x : Space n) : Matrix Unit (RIdx n) ℝ :=
  fun _ i => inner ℝ x (complexVector_realOrthonormalBasis n i)

theorem abpSpatialBlock_apply {n : ℕ} (dg : Point n →L[ℝ] Space n) (i j : RIdx n) :
    abpSpatialBlock dg i j = inner ℝ (complexVector_realOrthonormalBasis n i)
      (dg (complexVector_realOrthonormalBasis n j,0)) := by
  simp [abpSpatialBlock,LinearMap.toMatrix_apply,OrthonormalBasis.repr_apply_apply]

theorem abpSpaceRow_mul_spatial {n : ℕ} (x : Space n) (dg : Point n →L[ℝ] Space n)
    (j : RIdx n) (k : Unit) :
    (abpSpaceRow x*abpSpatialBlock dg) k j =
      inner ℝ x (dg (complexVector_realOrthonormalBasis n j,0)) := by
  simp only [Matrix.mul_apply,abpSpaceRow,abpSpatialBlock_apply]
  exact (complexVector_realOrthonormalBasis n).sum_inner_mul_inner x _

theorem abpSpaceRow_mul_time {n : ℕ} (x : Space n) (dg : Point n →L[ℝ] Space n)
    (j k : Unit) : (abpSpaceRow x*abpTimeColumn dg) j k = inner ℝ x (dg (0,1)) := by
  simp only [Matrix.mul_apply,abpSpaceRow,abpTimeColumn]
  exact (complexVector_realOrthonormalBasis n).sum_inner_mul_inner x _

theorem abpBlock_toMatrix {n : ℕ} (x : Space n) (dg : Point n →L[ℝ] Space n) (a : ℝ) :
    LinearMap.toMatrix (abpJointBasis n) (abpJointBasis n) (abpBlockDerivative x dg a).toLinearMap =
      Matrix.fromBlocks (abpSpatialBlock dg) (abpTimeColumn dg)
        (-(abpSpaceRow x*abpSpatialBlock dg))
        (a • (1 : Matrix Unit Unit ℝ)-abpSpaceRow x*abpTimeColumn dg) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [abpJointBasis,LinearMap.toMatrix_apply,abpBlockDerivative,Module.Basis.prod_apply,
      OrthonormalBasis.repr_apply_apply,abpSpatialBlock_apply,abpTimeColumn,
      abpSpaceRow_mul_spatial,abpSpaceRow_mul_time]

theorem abpBlock_det {n : ℕ} (x : Space n) (dg : Point n →L[ℝ] Space n) (a : ℝ) :
    (abpBlockDerivative x dg a).det = (abpSpatialBlock dg).det*a := by
  rw [ContinuousLinearMap.det,← LinearMap.det_toMatrix (abpJointBasis n),abpBlock_toMatrix,
    contact_block_det]

theorem contactMap_det_eq_spatialBlock {n : ℕ} {u : Point n → ℝ}
    (hu : ContDiff ℝ ∞ u) (z : Point n) :
    (fderiv ℝ (contactMap u) z).det =
      (abpSpatialBlock (fderiv ℝ (spatialGrad u) z)).det*timeD Set.univ u z := by
  rw [contactMap_fderiv_eq_block hu,abpBlock_det]

theorem spatialGrad_derivative_inner {n : ℕ} {u : Point n → ℝ}
    (hu : ContDiff ℝ ∞ u) (z : Point n) (v w : Space n) :
    inner ℝ (fderiv ℝ (spatialGrad u) z (v,0)) w = spatialDD u z v w := by
  let e := (InnerProductSpace.toDual ℝ (Space n)).symm.toContinuousLinearEquiv
  have hd := ((spatialD_smooth hu).differentiable (by simp) z).hasFDerivAt
  have hg : fderiv ℝ (spatialGrad u) z =
      e.toContinuousLinearMap.comp (fderiv ℝ (spatialD u) z) :=
    (e.toContinuousLinearMap.hasFDerivAt.comp z hd).fderiv
  have hi : HasFDerivAt (fun x : Space n => (x,z.2))
      (ContinuousLinearMap.inl ℝ (Space n) ℝ) z.1 := by
    simpa only [ContinuousLinearMap.inl_apply,Prod.mk_add_mk,add_zero,zero_add] using
      ((ContinuousLinearMap.inl ℝ (Space n) ℝ).hasFDerivAt).add_const ((0,z.2) : Point n)
  have hs : spatialDD u z = (fderiv ℝ (spatialD u) z).comp
      (ContinuousLinearMap.inl ℝ (Space n) ℝ) := by
    have hs0 := (hd.comp z.1 hi).fderiv
    exact hs0
  rw [hg]
  change inner ℝ ((InnerProductSpace.toDual ℝ (Space n)).symm
    (fderiv ℝ (spatialD u) z (v,0))) w = spatialDD u z v w
  rw [InnerProductSpace.toDual_symm_apply,hs]
  rfl

theorem abpSpatialBlock_eq_hessian_transpose {n : ℕ} {u : Point n → ℝ}
    (hu : ContDiff ℝ ∞ u) (z : Point n) :
    abpSpatialBlock (fderiv ℝ (spatialGrad u) z) = (hessian u z : Mat n).transpose := by
  have hs : ContDiffAt ℝ 2 (fun x : Space n => u (x,z.2)) z.1 :=
    (hu.comp (contDiff_id.prodMk contDiff_const)).contDiffAt.of_le (by simp)
  have hh : (hessian u z : Mat n) = secondFDerivMatrix (fun x => u (x,z.2)) z.1 :=
    hessian_space_eq_secondFDeriv hs
  ext i j
  rw [abpSpatialBlock_apply,Matrix.transpose_apply,hh]
  simp only [complexVector_realOrthonormalBasis_apply,secondFDerivMatrix]
  rw [real_inner_comm,spatialGrad_derivative_inner hu]
  rfl

theorem contactMap_det {n : ℕ} {u : Point n → ℝ}
    (hu : ContDiff ℝ ∞ u) (z : Point n) :
    (fderiv ℝ (contactMap u) z).det =
      timeD Set.univ u z*Matrix.det (hessian u z : Mat n) := by
  rw [contactMap_det_eq_spatialBlock hu,abpSpatialBlock_eq_hessian_transpose hu,Matrix.det_transpose]
  ring

theorem smoothContact_time_nonneg {n : ℕ} {R a b : ℝ} {u : Point n → ℝ}
    (hu : ContDiff ℝ ∞ u) {z : Point n} (hz : z ∈ smoothContact R a b u) :
    0 ≤ timeD Set.univ u z := by
  let f : ℝ → ℝ := fun t => u (z.1,t)
  have hmax : IsMaxOn f (Set.Icc a z.2) z.2 := by
    intro s hs
    have hh := hz.2 z.1 (Metric.ball_subset_closedBall hz.1.1) s hs
    change f s ≤ f z.2
    simpa only [f,Prod.eta,sub_self,inner_zero_right,add_zero] using hh
  have hder : DifferentiableAt ℝ f z.2 :=
    (hu.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) z.2
  have hcone : a-z.2 ∈ posTangentConeAt (Set.Icc a z.2) z.2 :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc a z.2).segment_subset ⟨hz.1.2.1.le,le_rfl⟩ ⟨le_rfl,hz.1.2.1.le⟩)
  have hh := hmax.isLocalMaxOn.hasFDerivWithinAt_nonpos hder.hasFDerivAt.hasFDerivWithinAt hcone
  rw [fderiv_eq_deriv_mul] at hh
  have hneg : a-z.2 < 0 := sub_neg.mpr hz.1.2.1
  have ht : timeD Set.univ u z = deriv f z.2 := by simp [timeD,f]
  rw [ht]
  nlinarith

theorem smoothContact_hessian_nonpos {n : ℕ} {R a b : ℝ} {u : Point n → ℝ}
    (hu : ContDiff ℝ ∞ u) {z : Point n} (hz : z ∈ smoothContact R a b u) :
    (-(hessian u z : Mat n)).PosSemidef := by
  let xi := spatialGrad u z
  let f : Space n → ℝ := fun y => u (y,z.2)-inner ℝ xi y
  have hs : ContDiffAt ℝ 2 (fun y : Space n => u (y,z.2)) z.1 :=
    (hu.comp (contDiff_id.prodMk contDiff_const)).contDiffAt.of_le (by simp)
  have hmax : IsLocalMax f z.1 := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz.1.1] with y hy
    have hh := hz.2 y (Metric.ball_subset_closedBall hy) z.2 ⟨hz.1.2.1.le,le_rfl⟩
    rw [inner_sub_right] at hh
    change u (y,z.2)-inner ℝ xi y ≤ u z-inner ℝ xi z.1
    linarith
  have hnon (v : Space n) : spatialDD u z v v ≤ 0 := by
    have hf : ContDiffAt ℝ 2 f z.1 := hs.sub ((innerSL ℝ xi).contDiff.contDiffAt)
    have hh := L16Aux.secondFDeriv_nonpos_of_isLocalMax hf hmax v
    have he : fderiv ℝ (fderiv ℝ f) z.1 = spatialDD u z := by
      have hnear : (fderiv ℝ f) =ᶠ[𝓝 z.1]
          (fun y => fderiv ℝ (fun x : Space n => u (x,z.2)) y-innerSL ℝ xi) := by
        filter_upwards [hs.eventually (by norm_num)] with y hy
        change fderiv ℝ (fun y => u (y,z.2)-(innerSL ℝ xi) y) y = _
        rw [fderiv_fun_sub (hy.differentiableAt (by norm_num))
          (innerSL ℝ xi).differentiableAt,ContinuousLinearMap.fderiv]
      rw [hnear.fderiv_eq]
      exact fderiv_sub_const _
    rwa [he] at hh
  have hraw : (hessian u z : Mat n) = secondFDerivMatrix (fun x => u (x,z.2)) z.1 :=
    hessian_space_eq_secondFDeriv hs
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (Matrix.isHermitian_iff_isSelfAdjoint.mpr (hessian u z).property.neg)
  intro v
  have hh := hnon (∑ i, v i • realVec i)
  simp only [map_sum,map_smul,sum_apply,smul_apply,Finset.mul_sum,smul_eq_mul] at hh
  rw [hraw]
  simp only [dotProduct,Matrix.mulVec,Matrix.neg_apply,secondFDerivMatrix,
    Pi.star_apply,star_trivial,Finset.mul_sum]
  change 0 ≤ ∑ i, ∑ j, v i*(-(spatialDD u z (realVec i) (realVec j))*v j)
  have he : (∑ i, ∑ j, v i*(-(spatialDD u z (realVec i) (realVec j))*v j)) =
      -(∑ i, ∑ j, v i*(v j*spatialDD u z (realVec j) (realVec i))) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  linarith

theorem contactMap_abs_det {n : ℕ} {R a b : ℝ} {u : Point n → ℝ}
    (hu : ContDiff ℝ ∞ u) {z : Point n} (hz : z ∈ smoothContact R a b u) :
    |(fderiv ℝ (contactMap u) z).det| =
      timeD Set.univ u z*Matrix.det (-(hessian u z : Mat n)) := by
  have ht := smoothContact_time_nonneg hu hz
  have hH := smoothContact_hessian_nonpos hu hz
  have hdet : Matrix.det (-(hessian u z : Mat n)) = Matrix.det (hessian u z : Mat n) := by
    rw [Matrix.det_neg]
    simp [RIdx]
  rw [contactMap_det hu,abs_mul,abs_of_nonneg ht,← hdet,abs_of_nonneg hH.det_nonneg]

end Yau.LeafProofs.L05Aux
