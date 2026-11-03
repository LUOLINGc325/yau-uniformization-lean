import Yau.LeafProofs.L05ABPMollifierConvexity
import Yau.LeafProofs.L05ABPConvexHessian

noncomputable section

open Filter MeasureTheory Asymptotics
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

theorem jointPeanoJet_lower_test {n : ℕ} {w : Point n → ℝ} {z : Point n}
    {l : Point n →L[ℝ] ℝ} {B : Point n →L[ℝ] Point n →L[ℝ] ℝ}
    (h : jointPeanoJet w z l B) {eta : ℝ} (heta : 0<eta) :
    touchBelow (peanoPolynomial (w z) z l B (-eta)) w z := by
  refine ⟨by simp [peanoPolynomial,qnorm2],?_⟩
  filter_upwards [h.2.bound heta] with y hy
  have hn := norm_sq_le_qnorm2 (y-z)
  have hlo := neg_abs_le (w y-w z-l (y-z)-(1/2 : ℝ)*B (y-z) (y-z))
  simp only [Real.norm_eq_abs,abs_pow,abs_norm] at hy
  have hm := mul_le_mul_of_nonneg_left hn heta.le
  dsimp only [peanoPolynomial]
  linarith

theorem jointPeanoJet_semiconvex_hessian_lower {n : ℕ} {w : Point n → ℝ} {z : Point n}
    {l : Point n →L[ℝ] ℝ} {B : Point n →L[ℝ] Point n →L[ℝ] ℝ} {K : ℝ}
    (hu : Continuous w) (hw : jointSemiconvex K w) (h : jointPeanoJet w z l B) :
    ((jointHessian B : Mat n)+K • (1 : Mat n)).PosSemidef := by
  have hc : Continuous (fun H : Sym n => (H : Mat n)+K • (1 : Mat n)) :=
    continuous_subtype_val.add continuous_const
  have hs : IsClosed {H : Sym n | ((H : Mat n)+K • (1 : Mat n)).PosSemidef} :=
    Matrix.posSemidef_is_closed.preimage hc
  apply hs.mem_of_tendsto (jointPeanoJet_mollifier_hessian_tendsto hu h)
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact smooth_jointSemiconvex_hessian_lower (abpMollify_smooth hr hu)
    (abpMollify_jointSemiconvex hr hu hw) z

theorem jointPeanoJet_pastSupport_time_nonneg {n : ℕ} {R a b : ℝ} {w : Point n → ℝ}
    {z : Point n} {xi : Space n} {l : Point n →L[ℝ] ℝ}
    {B : Point n →L[ℝ] Point n →L[ℝ] ℝ}
    (hz : z ∈ abpOpen n R a b) (hs : pastSupports R a w z xi) (h : jointPeanoJet w z l B) :
    0≤l (0,1) := by
  let f : ℝ → ℝ := fun t => w (z.1,t)
  have hp : HasDerivAt (fun t : ℝ => (z.1,t)) ((0,1) : Point n) z.2 := by
    simpa using (hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2)
  have ht : HasDerivAt f (l (0,1)) z.2 := by
    simpa only [f,Function.comp_def] using (jointPeanoJet_hasFDerivAt h).comp_hasDerivAt z.2 hp
  have hm : IsMaxOn f (Set.Icc a z.2) z.2 := by
    intro s hst
    have hh := hs z.1 (Metric.ball_subset_closedBall hz.1) s hst
    change f s≤f z.2
    simpa only [f,Prod.eta,sub_self,inner_zero_right,add_zero] using hh
  have hcone : a-z.2 ∈ posTangentConeAt (Set.Icc a z.2) z.2 :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc a z.2).segment_subset ⟨hz.2.1.le,le_rfl⟩ ⟨le_rfl,hz.2.1.le⟩)
  have hh := hm.isLocalMaxOn.hasFDerivWithinAt_nonpos
    ht.differentiableAt.hasFDerivAt.hasFDerivWithinAt hcone
  rw [fderiv_eq_deriv_mul,ht.deriv] at hh
  nlinarith [sub_neg.mpr hz.2.1]

theorem smooth_spatial_localMax_hessian_nonpos {n : ℕ} {u : Point n → ℝ}
    (hu : ContDiff ℝ ∞ u) (z : Point n)
    (hmax : IsLocalMax (fun x : Space n => u (x,z.2)) z.1) :
    (-(hessian u z : Mat n)).PosSemidef := by
  have hs : ContDiffAt ℝ 2 (fun x : Space n => u (x,z.2)) z.1 :=
    (hu.comp (contDiff_id.prodMk contDiff_const)).contDiffAt.of_le (by simp)
  have hnon (v : Space n) : spatialDD u z v v≤0 :=
    L16Aux.secondFDeriv_nonpos_of_isLocalMax hs hmax v
  have hraw : (hessian u z : Mat n)=secondFDerivMatrix (fun x => u (x,z.2)) z.1 :=
    hessian_space_eq_secondFDeriv hs
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (Matrix.isHermitian_iff_isSelfAdjoint.mpr (hessian u z).property.neg)
  intro v
  have hh := hnon (∑ i, v i • Yau.realVec i)
  simp only [map_sum,map_smul,sum_apply,smul_apply,Finset.mul_sum,smul_eq_mul] at hh
  rw [hraw]
  simp only [dotProduct,Matrix.mulVec,Matrix.neg_apply,secondFDerivMatrix,
    Pi.star_apply,star_trivial,Finset.mul_sum]
  change 0≤∑ i,∑ j,v i*(-(spatialDD u z (Yau.realVec i) (Yau.realVec j))*v j)
  have he : (∑ i,∑ j,v i*(-(spatialDD u z (Yau.realVec i) (Yau.realVec j))*v j))=
      -(∑ i,∑ j,v i*(v j*spatialDD u z (Yau.realVec j) (Yau.realVec i))) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  linarith

theorem peanoPolynomial_hessian_coe {n : ℕ} (c : ℝ) (z : Point n)
    (l : Point n →L[ℝ] ℝ) (B : Point n →L[ℝ] Point n →L[ℝ] ℝ)
    (hB : ∀ v w, B v w=B w v) (eta : ℝ) (y : Point n) :
    (hessian (peanoPolynomial c z l B eta) y : Mat n)=
      (jointHessian B : Mat n)+(2*eta) • (1 : Mat n) := by
  rw [peanoPolynomial_hessian c z l B hB eta y]
  let A : Mat n := fun i j => B (Yau.realVec i,0) (Yau.realVec j,0)
  have he : (fun i j : Yau.RIdx n => B (Yau.realVec i,0) (Yau.realVec j,0)+
      (2*eta)*inner ℝ (Yau.realVec i) (Yau.realVec j))=A+(2*eta) • (1 : Mat n) := by
    funext i j
    change B (Yau.realVec i,0) (Yau.realVec j,0)+
      (2*eta)*inner ℝ (Yau.realVec i) (Yau.realVec j)=
      B (Yau.realVec i,0) (Yau.realVec j,0)+(2*eta)*(if i=j then 1 else 0)
    have hi := (complexVector_realOrthonormalBasis n).inner_eq_ite i j
    simp only [complexVector_realOrthonormalBasis_apply] at hi
    rw [hi]
  rw [he]
  change (selfAdjointPart ℝ (A+(2*eta) • (1 : Mat n)) : Mat n)=_
  rw [map_add,AddSubgroup.coe_add]
  have hI : (selfAdjointPart ℝ ((2*eta) • (1 : Mat n)) : Mat n)=(2*eta) • (1 : Mat n) := by
    apply IsSelfAdjoint.coe_selfAdjointPart_apply
    exact IsSelfAdjoint.smul (IsSelfAdjoint.all _) (IsSelfAdjoint.one (Mat n))
  rw [hI]
  rfl

theorem jointPeanoJet_pastSupport_hessian_nonpos {n : ℕ} {R a b : ℝ} {w : Point n → ℝ}
    {z : Point n} {xi : Space n} {l : Point n →L[ℝ] ℝ}
    {B : Point n →L[ℝ] Point n →L[ℝ] ℝ}
    (hz : z ∈ abpOpen n R a b) (hs : pastSupports R a w z xi) (h : jointPeanoJet w z l B) :
    (-(jointHessian B : Mat n)).PosSemidef := by
  have hEta (eta : ℝ) (heta : 0<eta) :
      (-(jointHessian B : Mat n)+(2*eta) • (1 : Mat n)).PosSemidef := by
    let A := (innerSL ℝ xi).comp (ContinuousLinearMap.fst ℝ (Space n) ℝ)
    let P := peanoPolynomial (w z) z (l-A) B (-eta)
    have hlow := jointPeanoJet_lower_test h heta
    have hpath : Tendsto (fun x : Space n => (x,z.2)) (𝓝 z.1) (𝓝 z) := by
      have hc : Continuous (fun x : Space n => (x,z.2)) := by fun_prop
      simpa only [Prod.eta] using hc.tendsto z.1
    have he (x : Space n) : P (x,z.2)=peanoPolynomial (w z) z l B (-eta) (x,z.2)-
        inner ℝ xi (x-z.1) := by
      simp only [P,peanoPolynomial,A,sub_apply,ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_fst',Prod.fst_sub,innerSL_apply_apply]
      ring
    have hPz : P z=w z := by simp [P,peanoPolynomial,qnorm2]
    have hmax : IsLocalMax (fun x : Space n => P (x,z.2)) z.1 := by
      filter_upwards [hpath hlow.2,Metric.isOpen_ball.mem_nhds hz.1] with x hxl hx
      change P (x,z.2)≤P z
      rw [he,hPz]
      change peanoPolynomial (w z) z l B (-eta) (x,z.2)≤w (x,z.2) at hxl
      have hupper := hs x (Metric.ball_subset_closedBall hx) z.2 ⟨hz.2.1.le,le_rfl⟩
      linarith
    have hmat := smooth_spatial_localMax_hessian_nonpos (peanoPolynomial_smooth (w z) z (l-A) B (-eta)) z hmax
    change (-(hessian (peanoPolynomial (w z) z (l-A) B (-eta)) z : Mat n)).PosSemidef at hmat
    rw [peanoPolynomial_hessian_coe (w z) z (l-A) B h.1 (-eta) z] at hmat
    convert! hmat using 1
    module
  have hcont : Continuous (fun eta : ℝ => -(jointHessian B : Mat n)+(2*eta) • (1 : Mat n)) := by fun_prop
  have ht : Tendsto (fun eta : ℝ => -(jointHessian B : Mat n)+(2*eta) • (1 : Mat n))
      (𝓝[>] 0) (𝓝 (-(jointHessian B : Mat n))) := by
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  apply Matrix.posSemidef_is_closed.mem_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with eta heta
  exact hEta eta heta

end Yau.LeafProofs.L05Aux
