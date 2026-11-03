import Yau.LeafProofs.L05ABPMollifier
import Yau.LeafProofs.L05ABPPeano
import Yau.LeafProofs.L05ABPJacobian

noncomputable section

open Filter MeasureTheory Asymptotics
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius Convolution

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

local instance L05ABPMollifierPeano_pointVolumeHaar (n : ℕ) :
    (volume : Measure (Point n)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _

theorem peanoPolynomial_sub_expand {n : ℕ} (c : ℝ) (z : Point n)
    (l : Point n →L[ℝ] ℝ) (B : Point n →L[ℝ] Point n →L[ℝ] ℝ)
    (hB : ∀ v w, B v w=B w v) (w x : Point n) :
    peanoPolynomial c z l B 0 (w-x)=peanoPolynomial c z l B 0 w-
      (l+B (w-z)) x+(1/2 : ℝ)*B x x := by
  have he : w-x-z=(w-z)-x := by abel
  simp only [peanoPolynomial,zero_mul,add_zero,he,map_sub,sub_apply,add_apply]
  rw [hB x w,hB x z]
  ring

theorem abpMollify_peanoPolynomial {n : ℕ} {r : ℝ} (hr : 0<r) (c : ℝ) (z : Point n)
    (l : Point n →L[ℝ] ℝ) (B : Point n →L[ℝ] Point n →L[ℝ] ℝ)
    (hB : ∀ v w, B v w=B w v) :
    abpMollify r (peanoPolynomial c z l B 0)=fun w => peanoPolynomial c z l B 0 w+
      ∫ x, scaledKernel n r x*((1/2 : ℝ)*B x x) := by
  funext w
  let L := l+B (w-z)
  have hlin : Continuous (fun x : Point n => scaledKernel n r x*L x) :=
    (scaledKernel_smooth n r).continuous.mul L.continuous
  have hlinI := hlin.integrable_of_hasCompactSupport (scaledKernel_compactSupport hr).mul_right
    (μ := volume)
  have hquad : Continuous (fun x : Point n => scaledKernel n r x*((1/2 : ℝ)*B x x)) := by
    have hk := (scaledKernel_smooth n r).continuous
    fun_prop
  have hquadI := hquad.integrable_of_hasCompactSupport (scaledKernel_compactSupport hr).mul_right
    (μ := volume)
  have hconstI : Integrable (fun x : Point n => scaledKernel n r x*peanoPolynomial c z l B 0 w) :=
    abpMollify_integrand_integrable hr continuous_const w
  have he : (fun x : Point n => scaledKernel n r x*peanoPolynomial c z l B 0 (w-x))=
      (fun x => scaledKernel n r x*peanoPolynomial c z l B 0 w)-
      (fun x => scaledKernel n r x*L x)+(fun x => scaledKernel n r x*((1/2 : ℝ)*B x x)) := by
    funext x
    rw [peanoPolynomial_sub_expand c z l B hB w x]
    dsimp only [L,Pi.sub_apply,Pi.add_apply]
    ring
  change (∫ x, scaledKernel n r x*peanoPolynomial c z l B 0 (w-x))=_
  rw [he]
  change (∫ x, (scaledKernel n r x*peanoPolynomial c z l B 0 w-scaledKernel n r x*L x)+
    scaledKernel n r x*((1/2 : ℝ)*B x x))=_
  have ha : (∫ x, (scaledKernel n r x*peanoPolynomial c z l B 0 w-scaledKernel n r x*L x)+
      scaledKernel n r x*((1/2 : ℝ)*B x x))=
      (∫ x, scaledKernel n r x*peanoPolynomial c z l B 0 w-scaledKernel n r x*L x)+
        ∫ x, scaledKernel n r x*((1/2 : ℝ)*B x x) := by
    convert! integral_add (hconstI.sub hlinI) hquadI using 1
  have hs : (∫ x, scaledKernel n r x*peanoPolynomial c z l B 0 w-scaledKernel n r x*L x)=
      (∫ x, scaledKernel n r x*peanoPolynomial c z l B 0 w)-(∫ x, scaledKernel n r x*L x) := by
    convert! integral_sub hconstI hlinI using 1
  rw [ha,hs,
    scaledKernel_linear_integral_zero,integral_mul_const,scaledKernel_integral hr,one_mul,sub_zero]

theorem littleO_quadratic_uniform_ball {n : ℕ} {u : Point n → ℝ} {z : Point n}
    (h : u =o[𝓝 z] (fun y => ‖y-z‖^2)) {c : ℝ} (hc : 0<c) :
    ∃ delta : ℝ, 0<delta ∧ ∀ r : ℝ, 0<r → r<delta →
      ∀ x ∈ Metric.closedBall (0 : Point n) r, |u (z-x)|≤c*r^2 := by
  obtain ⟨delta,hdelta,hsub⟩ := Metric.mem_nhds_iff.mp (h.bound hc)
  refine ⟨delta,hdelta,?_⟩
  intro r hr hrd x hx
  have hxn : ‖x‖≤r := by simpa only [Metric.mem_closedBall,dist_eq_norm,sub_zero] using hx
  have he : (z-x)-z= -x := by abel
  have hpoint : z-x ∈ Metric.ball z delta := by
    rw [Metric.mem_ball,dist_eq_norm,he,norm_neg]
    exact hxn.trans_lt hrd
  have hh := hsub hpoint
  change ‖u (z-x)‖≤c*‖‖(z-x)-z‖^2‖ at hh
  rw [he,norm_neg,Real.norm_eq_abs,Real.norm_eq_abs,abs_pow,abs_norm] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hxn 2) hc.le)

theorem mollifier_quadratic_remainder_estimates {n : ℕ} {u : Point n → ℝ} {z : Point n}
    (hu : Continuous u) (h : u =o[𝓝 z] (fun y => ‖y-z‖^2)) :
    ∀ eta : ℝ, 0<eta → ∃ delta : ℝ, 0<delta ∧ ∀ r : ℝ, 0<r → r<delta →
      ‖fderiv ℝ (abpMollify r u) z‖<eta ∧
        ‖fderiv ℝ (fderiv ℝ (abpMollify r u)) z‖<eta := by
  intro eta heta
  let I1 := ∫ x, ‖fderiv ℝ (abpKernel n) x‖
  let I2 := ∫ x, ‖fderiv ℝ (fderiv ℝ (abpKernel n)) x‖
  have hI1 : 0≤I1 := integral_nonneg (fun _ => norm_nonneg _)
  have hI2 : 0≤I2 := integral_nonneg (fun x : Point n =>
    ContinuousLinearMap.opNorm_nonneg (fderiv ℝ (fderiv ℝ (abpKernel n)) x))
  let c := eta/(I1+I2+1)
  have hc : 0<c := by dsimp only [c]; positivity
  have hceq : c*(I1+I2+1)=eta := div_mul_cancel₀ eta (by positivity : I1+I2+1≠0)
  have hci1 : c*I1<eta := by nlinarith [mul_nonneg hc.le hI2]
  have hci2 : c*I2<eta := by nlinarith [mul_nonneg hc.le hI1]
  obtain ⟨R,hR,hball⟩ := littleO_quadratic_uniform_ball h hc
  refine ⟨min R 1,lt_min hR (by norm_num),?_⟩
  intro r hr hrd
  have hrR := (lt_min_iff.mp hrd).1
  have hr1 := (lt_min_iff.mp hrd).2
  have hlocal := hball r hr hrR
  have hb1 := abpMollify_fderiv_local_bound hr hu z hlocal
  have hb2 := abpMollify_secondFDeriv_local_bound hr hu z hlocal
  change ‖fderiv ℝ (abpMollify r u) z‖≤(c*r^2)*r⁻¹*I1 at hb1
  change ‖fderiv ℝ (fderiv ℝ (abpMollify r u)) z‖≤(c*r^2)*(r⁻¹*r⁻¹)*I2 at hb2
  have he1 : (c*r^2)*r⁻¹*I1=c*r*I1 := by field_simp [hr.ne']
  have he2 : (c*r^2)*(r⁻¹*r⁻¹)*I2=c*I2 := by field_simp [hr.ne']
  rw [he1] at hb1
  rw [he2] at hb2
  refine ⟨?_,hb2.trans_lt hci2⟩
  have hm := mul_le_mul_of_nonneg_left hr1.le (mul_nonneg hc.le hI1)
  have hle : c*r*I1≤c*I1 := by nlinarith
  exact hb1.trans_lt (hle.trans_lt hci1)

theorem peanoPolynomial_fderiv_zero {n : ℕ} (c : ℝ) (z : Point n)
    (l : Point n →L[ℝ] ℝ) (B : Point n →L[ℝ] Point n →L[ℝ] ℝ)
    (hB : ∀ v w, B v w=B w v) (y : Point n) :
    fderiv ℝ (peanoPolynomial c z l B 0) y=l+B (y-z) := by
  simpa only [mul_zero,zero_smul,add_zero] using
    (peanoPolynomial_hasFDerivAt c z l B hB 0 y).fderiv

theorem peanoPolynomial_secondFDeriv_zero {n : ℕ} (c : ℝ) (z : Point n)
    (l : Point n →L[ℝ] ℝ) (B : Point n →L[ℝ] Point n →L[ℝ] ℝ)
    (hB : ∀ v w, B v w=B w v) (y : Point n) :
    fderiv ℝ (fderiv ℝ (peanoPolynomial c z l B 0)) y=B := by
  have he : fderiv ℝ (peanoPolynomial c z l B 0)=fun y => l+B (y-z) :=
    funext (peanoPolynomial_fderiv_zero c z l B hB)
  rw [he]
  have hd := (B.hasFDerivAt.comp y ((hasFDerivAt_id (𝕜 := ℝ) y).sub_const z)).const_add l
  simpa using hd.fderiv

theorem abpMollify_peanoPolynomial_jets {n : ℕ} {r : ℝ} (hr : 0<r) (c : ℝ) (z : Point n)
    (l : Point n →L[ℝ] ℝ) (B : Point n →L[ℝ] Point n →L[ℝ] ℝ)
    (hB : ∀ v w, B v w=B w v) :
    fderiv ℝ (abpMollify r (peanoPolynomial c z l B 0)) z=l ∧
      fderiv ℝ (fderiv ℝ (abpMollify r (peanoPolynomial c z l B 0))) z=B := by
  have hfun : fderiv ℝ (abpMollify r (peanoPolynomial c z l B 0))=
      fderiv ℝ (peanoPolynomial c z l B 0) := by
    funext y
    rw [abpMollify_peanoPolynomial hr c z l B hB]
    exact fderiv_add_const _
  constructor
  · rw [hfun,peanoPolynomial_fderiv_zero c z l B hB z,sub_self,map_zero,add_zero]
  · rw [hfun,peanoPolynomial_secondFDeriv_zero c z l B hB z]

theorem jointPeanoJet_mollifier_estimates {n : ℕ} {u : Point n → ℝ} {z : Point n}
    {l : Point n →L[ℝ] ℝ} {B : Point n →L[ℝ] Point n →L[ℝ] ℝ}
    (hu : Continuous u) (h : jointPeanoJet u z l B) :
    ∀ eta : ℝ, 0<eta → ∃ delta : ℝ, 0<delta ∧ ∀ r : ℝ, 0<r → r<delta →
      ‖fderiv ℝ (abpMollify r u) z-l‖<eta ∧
        ‖fderiv ℝ (fderiv ℝ (abpMollify r u)) z-B‖<eta := by
  let P := peanoPolynomial (u z) z l B 0
  let R := u-P
  have hP : Continuous P := (peanoPolynomial_smooth (u z) z l B 0).continuous
  have hR : Continuous R := hu.sub hP
  have hsmall : R =o[𝓝 z] (fun y => ‖y-z‖^2) := by
    have he : R=(fun y => u y-u z-l (y-z)-(1/2 : ℝ)*B (y-z) (y-z)) := by
      funext y
      simp only [R,P,peanoPolynomial,Pi.sub_apply,zero_mul,add_zero]
      ring
    rw [he]
    exact h.2
  intro eta heta
  obtain ⟨delta,hdelta,hball⟩ := mollifier_quadratic_remainder_estimates hR hsmall eta heta
  refine ⟨delta,hdelta,?_⟩
  intro r hr hrd
  obtain ⟨hb1,hb2⟩ := hball r hr hrd
  have hpoly := abpMollify_peanoPolynomial_jets hr (u z) z l B h.1
  have hU : ContDiff ℝ ∞ (abpMollify r u) := abpMollify_smooth hr hu
  have hMP : ContDiff ℝ ∞ (abpMollify r P) := abpMollify_smooth hr hP
  have hfirst : fderiv ℝ (abpMollify r R)=
      fderiv ℝ (abpMollify r u)-fderiv ℝ (abpMollify r P) := by
    rw [show R=u-P from rfl,abpMollify_sub hr hu hP]
    funext y
    exact fderiv_fun_sub (hU.differentiable (by simp) y) (hMP.differentiable (by simp) y)
  have hsecond : fderiv ℝ (fderiv ℝ (abpMollify r R)) z=
      fderiv ℝ (fderiv ℝ (abpMollify r u)) z-fderiv ℝ (fderiv ℝ (abpMollify r P)) z := by
    rw [hfirst]
    have hUD : ContDiff ℝ ∞ (fderiv ℝ (abpMollify r u)) := hU.fderiv_right (by simp)
    have hPD : ContDiff ℝ ∞ (fderiv ℝ (abpMollify r P)) := hMP.fderiv_right (by simp)
    exact fderiv_fun_sub (hUD.differentiable (by simp) z) (hPD.differentiable (by simp) z)
  rw [hfirst,Pi.sub_apply,hpoly.1] at hb1
  rw [hsecond,hpoly.2] at hb2
  exact ⟨hb1,hb2⟩

theorem jointPeanoJet_mollifier_jets_tendsto {n : ℕ} {u : Point n → ℝ} {z : Point n}
    {l : Point n →L[ℝ] ℝ} {B : Point n →L[ℝ] Point n →L[ℝ] ℝ}
    (hu : Continuous u) (h : jointPeanoJet u z l B) :
    Tendsto (fun r : ℝ => fderiv ℝ (abpMollify r u) z) (𝓝[>] 0) (𝓝 l) ∧
      Tendsto (fun r : ℝ => fderiv ℝ (fderiv ℝ (abpMollify r u)) z) (𝓝[>] 0) (𝓝 B) := by
  constructor
  · apply (Metric.tendsto_nhds (α := Point n →L[ℝ] ℝ) (β := ℝ)).mpr
    intro eta heta
    obtain ⟨delta,hdelta,hbound⟩ := jointPeanoJet_mollifier_estimates hu h eta heta
    have hlt : ∀ᶠ r in 𝓝[>] (0:ℝ), r<delta :=
      (eventually_lt_nhds hdelta).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin,hlt] with r hr hrd
    simpa only [dist_eq_norm] using (hbound r hr hrd).1
  · apply (Metric.tendsto_nhds (α := Point n →L[ℝ] Point n →L[ℝ] ℝ) (β := ℝ)).mpr
    intro eta heta
    obtain ⟨delta,hdelta,hbound⟩ := jointPeanoJet_mollifier_estimates hu h eta heta
    have hlt : ∀ᶠ r in 𝓝[>] (0:ℝ), r<delta :=
      (eventually_lt_nhds hdelta).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin,hlt] with r hr hrd
    have hd : dist (fderiv ℝ (fderiv ℝ (abpMollify r u)) z) B=
        ‖fderiv ℝ (fderiv ℝ (abpMollify r u)) z-B‖ := by
      convert! (dist_eq_norm (fderiv ℝ (fderiv ℝ (abpMollify r u)) z) B) using 1
    rw [hd]
    exact (hbound r hr hrd).2

theorem spatialDD_eq_joint_second {n : ℕ} {u : Point n → ℝ} (hu : ContDiff ℝ ∞ u)
    (z : Point n) : spatialDD u z=(fderiv ℝ (fderiv ℝ u) z).bilinearComp
      (ContinuousLinearMap.inl ℝ (Space n) ℝ) (ContinuousLinearMap.inl ℝ (Space n) ℝ) := by
  let i := ContinuousLinearMap.inl ℝ (Space n) ℝ
  have hG : ContDiff ℝ ∞ (fderiv ℝ u) := hu.fderiv_right (by simp)
  have hd := (hG.differentiable (by simp) z).hasFDerivAt
  have hc := hd.clm_comp (hasFDerivAt_const i z)
  have hi : HasFDerivAt (fun x : Space n => (x,z.2)) i z.1 := by
    simpa only [i,ContinuousLinearMap.inl_apply,Prod.mk_add_mk,zero_add,add_zero] using
      (i.hasFDerivAt (x := z.1)).add_const ((0,z.2) : Point n)
  have hs := hc.comp z.1 hi
  have he : (fun x : Space n => spatialD u (x,z.2))=
      (fun x : Space n => (fderiv ℝ u (x,z.2)).comp i) := by
    funext x
    exact spatialD_eq_joint (hu.differentiable (by simp) (x,z.2))
  change fderiv ℝ (fun x : Space n => spatialD u (x,z.2)) z.1=_
  have hsf := hs.fderiv
  simp only [Function.comp_def] at hsf
  rw [he,hsf]
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  simp [i,ContinuousLinearMap.bilinearComp_apply]

def jointHessian {n : ℕ} (B : Point n →L[ℝ] Point n →L[ℝ] ℝ) : Sym n :=
  sym (fun i j => B (Yau.realVec i,0) (Yau.realVec j,0))

theorem hessian_eq_jointHessian {n : ℕ} {u : Point n → ℝ} (hu : ContDiff ℝ ∞ u)
    (z : Point n) : hessian u z=jointHessian (fderiv ℝ (fderiv ℝ u) z) := by
  unfold hessian jointHessian
  rw [spatialDD_eq_joint_second hu z]
  rfl

theorem jointHessian_continuous (n : ℕ) : Continuous (jointHessian (n := n)) := by
  have hentries : Continuous (fun B : Point n →L[ℝ] Point n →L[ℝ] ℝ =>
      fun i j : Yau.RIdx n => B (Yau.realVec i,0) (Yau.realVec j,0)) := by fun_prop
  exact (continuous_selfAdjointPart ℝ (Mat n)).comp hentries

theorem jointPeanoJet_mollifier_hessian_tendsto {n : ℕ} {u : Point n → ℝ} {z : Point n}
    {l : Point n →L[ℝ] ℝ} {B : Point n →L[ℝ] Point n →L[ℝ] ℝ}
    (hu : Continuous u) (h : jointPeanoJet u z l B) :
    Tendsto (fun r : ℝ => hessian (abpMollify r u) z) (𝓝[>] 0) (𝓝 (jointHessian B)) := by
  have ht := ((jointHessian_continuous n).tendsto B).comp
    (jointPeanoJet_mollifier_jets_tendsto hu h).2
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (hessian_eq_jointHessian (abpMollify_smooth hr hu) z).symm

theorem jointPeanoJet_mollifier_timeD_tendsto {n : ℕ} {u : Point n → ℝ} {z : Point n}
    {l : Point n →L[ℝ] ℝ} {B : Point n →L[ℝ] Point n →L[ℝ] ℝ}
    (hu : Continuous u) (h : jointPeanoJet u z l B) :
    Tendsto (fun r : ℝ => timeD Set.univ (abpMollify r u) z) (𝓝[>] 0) (𝓝 (l (0,1))) := by
  have hev : Continuous (fun L : Point n →L[ℝ] ℝ => L (0,1)) := by fun_prop
  have ht := (hev.tendsto l).comp (jointPeanoJet_mollifier_jets_tendsto hu h).1
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (timeD_univ_eq_joint ((abpMollify_smooth hr hu).differentiable (by simp) z)).symm

theorem jointPeanoJet_mollifier_spatialGrad_tendsto {n : ℕ} {u : Point n → ℝ} {z : Point n}
    {l : Point n →L[ℝ] ℝ} {B : Point n →L[ℝ] Point n →L[ℝ] ℝ}
    (hu : Continuous u) (h : jointPeanoJet u z l B) :
    Tendsto (fun r : ℝ => spatialGrad (abpMollify r u) z) (𝓝[>] 0) (𝓝 (spatialGrad u z)) := by
  let i := ContinuousLinearMap.inl ℝ (Space n) ℝ
  have hc : Continuous (fun L : Point n →L[ℝ] ℝ => L.comp i) := by fun_prop
  have hd := (InnerProductSpace.toDual ℝ (Space n)).symm.toContinuousLinearEquiv.continuous.comp hc
  have he : spatialGrad u z=(InnerProductSpace.toDual ℝ (Space n)).symm (l.comp i) := by
    unfold spatialGrad
    rw [jointPeanoJet_spatialD h]
  rw [he]
  have ht := (hd.tendsto l).comp (jointPeanoJet_mollifier_jets_tendsto hu h).1
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  unfold spatialGrad
  rw [spatialD_eq_joint ((abpMollify_smooth hr hu).differentiable (by simp) z)]
  rfl

end Yau.LeafProofs.L05Aux
