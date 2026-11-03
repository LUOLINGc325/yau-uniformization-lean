import Yau.LeafProofs.L17HolomorphicCharts
import Yau.LeafProofs.L22Locality

/-!
Pluriharmonic logarithmic Jacobians and the Chern Ricci coordinate law.
All derivatives are the original real Fréchet and nested Wirtinger derivatives.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff Manifold Matrix

namespace Yau.LeafProofs.L17Aux

variable {n : ℕ}

theorem scalar_secondFDeriv_restrict_complex
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : E → F} {z : E} (hf : ContDiffAt ℂ 2 f z) (v w : E) :
    fderiv ℝ (fderiv ℝ f) z v w = fderiv ℂ (fderiv ℂ f) z v w := by
  have h := congrArg (fun A => A ![v, w]) (hf.restrictScalars_iteratedFDeriv (𝕜 := ℝ))
  simpa only [Function.comp_apply, ContinuousMultilinearMap.coe_restrictScalars,
    iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using h.symm

theorem secondFDeriv_re
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} {z : E} (hf : ContDiffAt ℝ 2 f z) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun x => (f x).re)) z v w =
      (fderiv ℝ (fderiv ℝ f) z v w).re := by
  have h := congrArg (fun A => A ![v, w])
    (Complex.reCLM.iteratedFDeriv_comp_left hf (by norm_num))
  simpa only [Function.comp_def, Complex.reCLM_apply,
    ContinuousLinearMap.compContinuousMultilinearMap_coe,
    iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using h

theorem leviC_re_holomorphic {f : ComplexVector n → ℂ} {z : ComplexVector n}
    (hf : ContDiffAt ℂ 2 f z) : leviC (fun x => (f x).re) z = 0 := by
  have hfr := hf.restrict_scalars ℝ
  have hr : ContDiffAt ℝ 2 (fun x => (f x).re) z :=
    hfr.continuousLinearMap_comp Complex.reCLM
  ext i j
  apply Complex.ext
  · rw [leviC, (L18Aux.leviMatrix_entry_re_im hr stdVec i j).1]
    simp [secondFDeriv_re hfr, scalar_secondFDeriv_restrict_complex hf, map_smul]
  · rw [leviC, (L18Aux.leviMatrix_entry_re_im hr stdVec i j).2]
    simp [secondFDeriv_re hfr, scalar_secondFDeriv_restrict_complex hf, map_smul]

theorem leviC_const (c : ℝ) (z : ComplexVector n) :
    leviC (fun _ => c) z = 0 := by
  ext i j
  simp [leviC, leviMatrix, wirt, wirtBar]

theorem leviC_add {f g : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) :
    leviC (fun x => f x + g x) z = leviC f z + leviC g z := by
  apply matrix_eq_of_quadratic_eq
  intro v
  rw [Matrix.add_mulVec, dotProduct_add]
  have hleft := L22Aux.leviC_quadratic (hf.add hg) (WithLp.toLp 2 v)
  rw [hleft, L22Aux.leviC_quadratic hf (WithLp.toLp 2 v),
    L22Aux.leviC_quadratic hg (WithLp.toLp 2 v), L22Aux.complexLeviQuadratic_add hf hg]
  simp

theorem leviC_const_mul {f : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (c : ℝ) :
    leviC (fun x => c * f x) z = (c : ℂ) • leviC f z := by
  apply matrix_eq_of_quadratic_eq
  intro v
  rw [Matrix.smul_mulVec, dotProduct_smul]
  have hleft := L22Aux.leviC_quadratic ((contDiffAt_const (c := c)).mul hf)
    (WithLp.toLp 2 v)
  rw [hleft, L22Aux.leviC_quadratic hf (WithLp.toLp 2 v),
    L22Aux.complexLeviQuadratic_const_mul hf c]
  simp [smul_eq_mul]

theorem leviC_log_normSq_holomorphic
    {f : ComplexVector n → ℂ} {z : ComplexVector n}
    (hf : ContDiffAt ℂ 2 f z) (hne : f z ≠ 0) :
    leviC (fun x => Real.log (Complex.normSq (f x))) z = 0 := by
  let q : ComplexVector n → ℂ := fun x => f x / f z
  have hq : ContDiffAt ℂ 2 q z := hf.div_const _
  have hqz : q z = 1 := div_self hne
  have hlog : ContDiffAt ℂ 2 (fun x => Complex.log (q x)) z :=
    (Complex.contDiffAt_log (by rw [hqz]; exact Complex.one_mem_slitPlane)).comp z hq
  have hre : ContDiffAt ℝ 2 (fun x => (Complex.log (q x)).re) z :=
    (hlog.restrict_scalars ℝ).continuousLinearMap_comp Complex.reCLM
  have heq : (fun x => Real.log (Complex.normSq (f x))) =ᶠ[𝓝 z]
      (fun x => 2 * (Complex.log (q x)).re + Real.log (Complex.normSq (f z))) := by
    filter_upwards [hf.continuousAt.eventually_ne hne] with x hx
    simp only [Complex.normSq_eq_norm_sq, Real.log_pow, Complex.log_re, q, norm_div,
      Real.log_div (norm_ne_zero_iff.mpr hx) (norm_ne_zero_iff.mpr hne)]
    ring
  rw [L22Aux.leviC_congr_of_eventuallyEq heq,
    leviC_add (contDiffAt_const.mul hre) contDiffAt_const,
    leviC_const_mul hre, leviC_re_holomorphic hlog, leviC_const]
  simp

theorem contDiffAt_log_normSq
    {f : ComplexVector n → ℂ} {z : ComplexVector n}
    (hf : ContDiffAt ℂ 2 f z) (hne : f z ≠ 0) :
    ContDiffAt ℝ 2 (fun x => Real.log (Complex.normSq (f x))) z := by
  have hr := (hf.restrict_scalars ℝ).continuousLinearMap_comp Complex.reCLM
  have hi := (hf.restrict_scalars ℝ).continuousLinearMap_comp Complex.imCLM
  have hnorm : ContDiffAt ℝ 2 (fun x => Complex.normSq (f x)) z := by
    simpa only [Function.comp_def, Complex.reCLM_apply, Complex.imCLM_apply,
      Complex.normSq_apply, pow_two] using (hr.pow 2).add (hi.pow 2)
  exact hnorm.log (Complex.normSq_pos.mpr hne).ne'

theorem jacobian_det_contDiffAt
    {T : ComplexVector n → ComplexVector n} {z : ComplexVector n}
    (hT : ContDiffAt ℂ 3 T z) :
    ContDiffAt ℂ 2 (fun x => (linearMatrix (fderiv ℂ T x)).det) z := by
  have hD : ContDiffAt ℂ 2 (fderiv ℂ T) z := hT.fderiv_right (by norm_num)
  have hentry (i j : Fin n) :
      ContDiffAt ℂ 2 (fun x => linearMatrix (fderiv ℂ T x) i j) z := by
    have he := (hD.clm_apply (contDiffAt_const (c := stdVec j))).continuousLinearMap_comp
      (EuclideanSpace.proj i : ComplexVector n →L[ℂ] ℂ)
    simpa only [linearMatrix, Function.comp_def, EuclideanSpace.proj, PiLp.proj_apply] using he
  simp_rw [Matrix.det_apply']
  exact ContDiffAt.sum fun σ _ => contDiffAt_const.mul
    (contDiffAt_prod fun i _ => hentry (σ i) i)

set_option maxHeartbeats 800000 in
/-- A holomorphic Jacobian contributes no Chern Ricci term. -/
theorem leviC_logdet_congruence
    {T : ComplexVector n → ComplexVector n}
    {G : ComplexVector n → Matrix (Fin n) (Fin n) ℂ} {z : ComplexVector n}
    (hT : ContDiffAt ℂ 3 T z)
    (hG : ContDiffAt ℝ 2 (fun y => Real.log (G y).det.re) (T z))
    (hGpos : ∀ᶠ x in 𝓝 z, 0 < (G (T x)).det.re)
    (hJ : (linearMatrix (fderiv ℂ T z)).det ≠ 0) :
    leviC (fun x => Real.log (((linearMatrix (fderiv ℂ T x))ᴴ *
      G (T x) * linearMatrix (fderiv ℂ T x)).det.re)) z =
      (linearMatrix (fderiv ℂ T z))ᴴ *
        leviC (fun y => Real.log (G y).det.re) (T z) *
          linearMatrix (fderiv ℂ T z) := by
  have hd := jacobian_det_contDiffAt hT
  have ht2 : ContDiffAt ℂ 2 T z := hT.of_le (by norm_num)
  have heq : (fun x => Real.log (((linearMatrix (fderiv ℂ T x))ᴴ *
        G (T x) * linearMatrix (fderiv ℂ T x)).det.re)) =ᶠ[𝓝 z]
      (fun x => Real.log (Complex.normSq (linearMatrix (fderiv ℂ T x)).det) +
        Real.log (G (T x)).det.re) := by
    filter_upwards [hd.continuousAt.eventually_ne hJ, hGpos] with x hx hpos
    rw [congruence_det_re, Real.log_mul (Complex.normSq_pos.mpr hx).ne' hpos.ne']
  have hcomp : ContDiffAt ℝ 2 (fun x => Real.log (G (T x)).det.re) z :=
    hG.comp z (ht2.restrict_scalars ℝ)
  have hadd := leviC_add
    (f := fun x => Real.log (Complex.normSq (linearMatrix (fderiv ℂ T x)).det))
    (g := fun x => Real.log (G (T x)).det.re)
    (contDiffAt_log_normSq hd hJ) hcomp
  have hzero := leviC_log_normSq_holomorphic
    (f := fun x => (linearMatrix (fderiv ℂ T x)).det) hd hJ
  have hchain := leviC_comp (T := T) (f := fun y => Real.log (G y).det.re) ht2 hG
  calc
    _ = leviC (fun x => Real.log (Complex.normSq (linearMatrix (fderiv ℂ T x)).det) +
        Real.log (G (T x)).det.re) z := L22Aux.leviC_congr_of_eventuallyEq heq
    _ = _ := hadd
    _ = leviC (fun x => Real.log (G (T x)).det.re) z := by rw [hzero, zero_add]
    _ = _ := by simpa only [Function.comp_def] using hchain

variable {M : ComplexManifold n}

/-- Chern Ricci computed in the actual holomorphic background chart. -/
def pullbackRicci (g : HermitianField M)
    (e : ComplexVector n → M.Carrier) (z : ComplexVector n) :
    Matrix (Fin n) (Fin n) ℂ :=
  -leviC (fun w => Real.log (pullbackMatrix g e w).det.re) z

theorem pullbackRicci_eq_canonical
    (g : HermitianField M) (hg : MetricSmooth g)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    (a : M.Carrier) {z : ComplexVector n} (hz : z ∈ e.source)
    (ha : e z ∈ (extChartAt (ComplexModel n) a).source) :
    pullbackRicci g e z = (linearMatrix (coordinateDifferential e a z))ᴴ *
      (-leviC (logDet g a) (chartPt a (e z))) *
        linearMatrix (coordinateDifferential e a z) := by
  let T : ComplexVector n → ComplexVector n := fun w => chartPt a (e w)
  have hU := (forwardChartDomain_isOpen e a).mem_nhds ⟨hz, ha⟩
  have hTsmooth := (forwardChart_contDiffOn e he a).contDiffAt hU
  have hT : ContDiffAt ℂ 3 T z := hTsmooth.of_le (by simp)
  have htgt : T z ∈ chartTarget a := (extChartAt (ComplexModel n) a).map_source ha
  have hG : ContDiffAt ℝ 2 (fun y => Real.log (hMat g a y).det.re) (T z) :=
    ((logDet_contDiffOn_of_metricSmooth g hg a).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) a).mem_nhds htgt)).of_le (by simp)
  have hpos : ∀ᶠ w in 𝓝 z, 0 < (hMat g a (T w)).det.re := by
    filter_upwards [hU] with w hw
    exact L12Aux.hMat_det_re_pos g a ((extChartAt (ComplexModel n) a).map_source hw.2)
  have hJ : (linearMatrix (fderiv ℂ T z)).det ≠ 0 := by
    rw [← coordinateDifferential_eq_fderiv e he a hz ha]
    exact linearMatrix_det_ne_zero _ (coordinateDifferential_injective e he hei a hz ha)
  have heq : (fun w => Real.log (pullbackMatrix g e w).det.re) =ᶠ[𝓝 z]
      (fun w => Real.log (((linearMatrix (fderiv ℂ T w))ᴴ *
        hMat g a (T w) * linearMatrix (fderiv ℂ T w)).det.re)) := by
    filter_upwards [hU] with w hw
    rw [pullbackMatrix_eq_congruence g e a w hw.2,
      coordinateDifferential_eq_fderiv e he a hw.1 hw.2]
  rw [pullbackRicci, L22Aux.leviC_congr_of_eventuallyEq heq,
    leviC_logdet_congruence hT hG hpos hJ,
    coordinateDifferential_eq_fderiv e he a hz ha]
  simp only [Matrix.mul_neg, Matrix.neg_mul]
  rfl

theorem pullbackRicci_eq_ricci
    (g : HermitianField M) (hg : MetricSmooth g)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {z : ComplexVector n} (hz : z ∈ e.source) :
    pullbackRicci g e z = (linearMatrix (coordinateDifferential e (e z) z))ᴴ *
      ricci g (e z) * linearMatrix (coordinateDifferential e (e z) z) :=
  pullbackRicci_eq_canonical g hg e he hei (e z) hz (mem_extChartAt_source (e z))

end Yau.LeafProofs.L17Aux
