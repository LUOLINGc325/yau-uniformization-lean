import Yau.LeafProofs.L05ABPMollifierConvexity
import Yau.LeafProofs.L05ABPConvexHessian
import Yau.LeafProofs.L05ABPLimit

noncomputable section

open Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

local instance L05ABPSemiconvexBounds_pointVolumeHaar (n : ℕ) :
    (volume : Measure (Point n)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _

theorem qnorm2_smul {n : ℕ} (a : ℝ) (z : Point n) : qnorm2 (a • z)=a^2*qnorm2 z := by
  simp only [qnorm2,Prod.smul_fst,Prod.smul_snd,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,smul_eq_mul]
  ring

theorem qnorm2_le_two_norm_sq {n : ℕ} (z : Point n) : qnorm2 z≤2*‖z‖^2 := by
  rw [Prod.norm_def]
  simp only [qnorm2,Real.norm_eq_abs]
  have h1 := pow_le_pow_left₀ (norm_nonneg z.1) (le_max_left ‖z.1‖ |z.2|) 2
  have h2 := pow_le_pow_left₀ (abs_nonneg z.2) (le_max_right ‖z.1‖ |z.2|) 2
  nlinarith [sq_abs z.2]

theorem qnorm2_mix {n : ℕ} (z y : Point n) {a b : ℝ} (hab : a+b=1) :
    qnorm2 (a • z+b • y)=a*qnorm2 z+b*qnorm2 y-a*b*qnorm2 (z-y) := by
  simp only [qnorm2,Prod.fst_add,Prod.smul_fst,Prod.snd_add,Prod.smul_snd,
    Prod.fst_sub,Prod.snd_sub,norm_add_sq_real,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,
    real_inner_smul_left,real_inner_smul_right,norm_sub_sq_real,smul_eq_mul]
  have hb : b=1-a := by linarith
  rw [hb]
  ring

theorem jointSemiconvex_jensen {n : ℕ} {w : Point n → ℝ} {K : ℝ}
    (hw : jointSemiconvex K w) (x y : Point n) {a b : ℝ}
    (ha : 0≤a) (hb : 0≤b) (hab : a+b=1) :
    w (a • x+b • y)≤a*w x+b*w y+(K/2)*a*b*qnorm2 (x-y) := by
  have hh := hw.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  change w (a • x+b • y)+(K/2)*qnorm2 (a • x+b • y)≤
    a*(w x+(K/2)*qnorm2 x)+b*(w y+(K/2)*qnorm2 y) at hh
  rw [qnorm2_mix x y hab] at hh
  nlinarith

/-- A bounded globally semiconvex function has a finite global Lipschitz
constant. This constant is used only inside a fixed regularization stage. -/
theorem bounded_jointSemiconvex_lipschitz {n : ℕ} {w : Point n → ℝ} {K B : ℝ}
    (hw : jointSemiconvex K w) (hK : 0≤K) (hB : 0≤B) (hb : ∀ z, |w z|≤B) :
    LipschitzWith ⟨2*B+K,by positivity⟩ w := by
  have hone (x y : Point n) : w y-w x≤(2*B+K)*‖y-x‖ := by
    by_cases hxy : y=x
    · simp [hxy]
    let h := ‖y-x‖
    have hh : 0<h := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    have hdiff : w y-w x≤2*B := by linarith [(abs_le.mp (hb y)).2,(abs_le.mp (hb x)).1]
    by_cases hlarge : 1≤h
    · have hm := mul_le_mul_of_nonneg_left hlarge (by positivity : 0≤2*B+K)
      change w y-w x≤(2*B+K)*h
      nlinarith
    · have hsmall : h<1 := lt_of_not_ge hlarge
      let v := h⁻¹ • (y-x)
      let q := x+v
      have hv : ‖v‖=1 := by
        simp only [v,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hh)]
        exact inv_mul_cancel₀ hh.ne'
      have hmix : (1-h) • x+h • q=y := by
        calc
          _ = x+(h*h⁻¹) • (y-x) := by dsimp only [q,v]; module
          _ = y := by rw [mul_inv_cancel₀ hh.ne',one_smul]; abel
      have hj := jointSemiconvex_jensen hw x q (sub_nonneg.mpr hsmall.le) hh.le
        (by ring : (1-h)+h=1)
      rw [hmix] at hj
      have hquad : qnorm2 (x-q)≤2 := by
        have hupper := qnorm2_le_two_norm_sq (x-q)
        have he : x-q= -v := by dsimp only [q]; abel
        rw [he,norm_neg,hv] at hupper
        rw [he]
        simpa only [one_pow,mul_one] using hupper
      have hcoef : 0≤(K/2)*(1-h)*h := by positivity
      have hcorr := mul_le_mul_of_nonneg_left hquad hcoef
      have hcorr2 : (K/2)*(1-h)*h*2≤K*h := by nlinarith [mul_nonneg hK (sq_nonneg h)]
      have hqdiff : w q-w x≤2*B := by linarith [(abs_le.mp (hb q)).2,(abs_le.mp (hb x)).1]
      have hmul := mul_le_mul_of_nonneg_left hqdiff hh.le
      change w y-w x≤(2*B+K)*h
      nlinarith
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq,dist_eq_norm x y]
  change |w x-w y|≤(2*B+K)*‖x-y‖
  apply abs_le.mpr
  constructor
  · have hh := hone x y
    rw [norm_sub_rev] at hh
    linarith
  · exact hone y x

theorem abpMollify_bounded {n : ℕ} {w : Point n → ℝ} {r B : ℝ}
    (hr : 0<r) (hB : 0≤B) (hw : Continuous w) (hb : ∀ z, |w z|≤B) :
    ∀ z, |abpMollify r w z|≤B := by
  intro z
  have hi := dist_convolution_le hB (scaledKernel_support hr) (scaledKernel_nonneg hr)
    (scaledKernel_integral hr) hw.aestronglyMeasurable
    (fun y (_hy : y ∈ Metric.ball z r) => (show dist (w y) (0:ℝ)≤B by simpa [Real.dist_eq] using hb y))
  simpa only [abpMollify,Real.dist_eq,sub_zero] using hi

theorem abpMollify_lipschitz_approx {n : ℕ} {w : Point n → ℝ} {r : ℝ} {C : NNReal}
    (hr : 0<r) (hw : LipschitzWith C w) (z : Point n) :
    |abpMollify r w z-w z|≤C*r := by
  have hlocal (y : Point n) (hy : y ∈ Metric.ball z r) : dist (w y) (w z)≤C*r :=
    (hw.dist_le_mul y z).trans (mul_le_mul_of_nonneg_left (Metric.mem_ball.mp hy).le C.coe_nonneg)
  have hi := abpMollify_approx hr (by positivity : 0≤(C:ℝ)*r) hw.continuous.aestronglyMeasurable z hlocal
  simpa only [Real.dist_eq] using hi

theorem smooth_boundedSemiconvex_timeD {n : ℕ} {w : Point n → ℝ} {K B : ℝ}
    (hu : ContDiff ℝ ∞ w) (hw : jointSemiconvex K w)
    (hK : 0≤K) (hB : 0≤B) (hb : ∀ z, |w z|≤B) (z : Point n) :
    |timeD Set.univ w z|≤2*B+K := by
  have hLip := bounded_jointSemiconvex_lipschitz hw hK hB hb
  have hdf : ‖fderiv ℝ w z‖≤2*B+K := norm_fderiv_le_of_lipschitz ℝ hLip
  have he := (fderiv ℝ w z).le_opNorm ((0,1) : Point n)
  have hev : |fderiv ℝ w z (0,1)|≤‖fderiv ℝ w z‖ := by simpa using he
  rw [timeD_univ_eq_joint (hu.differentiable (by simp) z)]
  exact hev.trans hdf

theorem posSemidef_det_le_trace_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : Matrix ι ι ℝ} (hB : B.PosSemidef) : B.det≤(Matrix.trace B)^Fintype.card ι := by
  have he (i : ι) : hB.isHermitian.eigenvalues i≤Matrix.trace B := by
    rw [hB.isHermitian.trace_eq_sum_eigenvalues]
    exact Finset.single_le_sum (fun j _ => hB.eigenvalues_nonneg j) (Finset.mem_univ i)
  rw [hB.isHermitian.det_eq_prod_eigenvalues]
  calc
    _ ≤ ∏ _i : ι, Matrix.trace B := Finset.prod_le_prod₀
      (fun i _ => hB.eigenvalues_nonneg i) (fun i _ => he i)
    _ = _ := by simp only [Finset.prod_const,Finset.card_univ]

theorem posSemidef_det_le_scalar_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : Matrix ι ι ℝ} {K : ℝ} (hB : B.PosSemidef)
    (hupper : (K • (1 : Matrix ι ι ℝ)-B).PosSemidef) :
    B.det≤((Fintype.card ι : ℝ)*K)^Fintype.card ι := by
  have ht := hupper.trace_nonneg
  simp only [Matrix.trace_sub,Matrix.trace_smul,Matrix.trace_one,smul_eq_mul] at ht
  have htrace : Matrix.trace B≤(Fintype.card ι : ℝ)*K := by nlinarith
  exact (posSemidef_det_le_trace_pow hB).trans
    (pow_le_pow_left₀ hB.trace_nonneg htrace _)

def semiconvexDensityBound (n : ℕ) (B K : ℝ) : ℝ :=
  (2*B+K)*(((2*n : ℕ) : ℝ)*K)^(2*n)

theorem semiconvexDensityBound_nonneg (n : ℕ) {B K : ℝ} (hB : 0≤B) (hK : 0≤K) :
    0 ≤ semiconvexDensityBound n B K := by
  unfold semiconvexDensityBound
  positivity

theorem smooth_boundedSemiconvex_density_bound {n : ℕ} {w : Point n → ℝ} {K B : ℝ}
    (hu : ContDiff ℝ ∞ w) (hw : jointSemiconvex K w)
    (hK : 0≤K) (hB : 0≤B) (hb : ∀ z, |w z|≤B) (R a b : ℝ) (z : Point n) :
    smoothContactDensity R a b w z ≤ semiconvexDensityBound n B K := by
  by_cases hz : z ∈ smoothContact R a b w
  · rw [smoothContactDensity,Set.indicator_of_mem hz,contactMap_abs_det hu hz]
    have hH := smoothContact_hessian_nonpos hu hz
    have hlower := smooth_jointSemiconvex_hessian_lower hu hw z
    have hupper : (K • (1 : Mat n)-(-(hessian w z : Mat n))).PosSemidef := by
      simpa only [sub_neg_eq_add,add_comm] using hlower
    have hdet := posSemidef_det_le_scalar_pow hH hupper
    have hd : Matrix.det (-(hessian w z : Mat n))≤(((2*n : ℕ) : ℝ)*K)^(2*n) := by
      simpa only [Fintype.card_prod,Fintype.card_fin,Nat.mul_comm] using hdet
    have ht : timeD Set.univ w z≤2*B+K :=
      (le_abs_self _).trans (smooth_boundedSemiconvex_timeD hu hw hK hB hb z)
    exact mul_le_mul ht hd hH.det_nonneg (by positivity : 0≤2*B+K)
  · simp only [smoothContactDensity,Set.indicator_of_notMem hz]
    exact semiconvexDensityBound_nonneg n hB hK

theorem abpMollify_boundedSemiconvex_density_bound {n : ℕ} {w : Point n → ℝ} {K B r : ℝ}
    (hr : 0<r) (hu : Continuous w) (hw : jointSemiconvex K w)
    (hK : 0≤K) (hB : 0≤B) (hb : ∀ z, |w z|≤B) (R a b : ℝ) (z : Point n) :
    smoothContactDensity R a b (abpMollify r w) z ≤ semiconvexDensityBound n B K :=
  smooth_boundedSemiconvex_density_bound (abpMollify_smooth hr hu)
    (abpMollify_jointSemiconvex hr hu hw) hK hB (abpMollify_bounded hr hB hu hb) R a b z

theorem abpMollify_lipschitz_tendsto {n : ℕ} {w : Point n → ℝ} {C : NNReal}
    (hw : LipschitzWith C w) (z : Point n) :
    Tendsto (fun r : ℝ => abpMollify r w z) (𝓝[>] 0) (𝓝 (w z)) := by
  apply Metric.tendsto_nhds.mpr
  intro eta heta
  have hlim : Tendsto (fun r : ℝ => (C:ℝ)*r) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun r : ℝ => (C:ℝ)*r) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hsmall := hlim (eventually_lt_nhds heta)
  filter_upwards [self_mem_nhdsWithin,hsmall] with r hr hbound
  change (C:ℝ)*r<eta at hbound
  rw [Real.dist_eq]
  exact (abpMollify_lipschitz_approx hr hw z).trans_lt hbound

end Yau.LeafProofs.L05Aux
