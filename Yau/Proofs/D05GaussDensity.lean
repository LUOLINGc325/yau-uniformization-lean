import Yau.Proofs.D05GramGreen
import Yau.Proofs.V03GaussTransport
import Yau.Proofs.V03FrameSmooth

/-! The actual Gauss density is half the planar Laplacian of the same
ambient frame Gram potential. All chart changes are fixed locally. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

noncomputable section
namespace Yau.Blueprint.D05Proof
open Yau V03Proof

variable {n q : ℕ} {M : ComplexManifold n}

def frameGramPotential (G : CotangentPoint M → ComplexVector q)
    (f : ℂ → CotangentPoint M) (E : ℂ → CotangentMatrix n) (z : ℂ) : ℝ :=
  Real.log ((ambientFrame G f E z)ᴴ * ambientFrame G f E z).det.re

theorem frameInChart_det_ne_zero {f : ℂ → CotangentPoint M}
    {E : ℂ → CotangentMatrix n} (hE : IsDiscFrame f E)
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) (x : M.Carrier)
    (hx : f z ∈ cotangentSource x) : (frameInChart x f E z).det ≠ 0 := by
  have hT := cotangentTransition_mulVec_injective (f z).1 x (f z)
    (mem_extChartAt_source _) hx
  have hTd := ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hT)).ne_zero
  exact (Matrix.det_mul _ _).trans_ne (mul_ne_zero hTd (hE.1 z hz))

theorem ambientFrame_gram_det_re_pos {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentImmersion G) {f : ℂ → CotangentPoint M}
    {E : ℂ → CotangentMatrix n} (hE : IsDiscFrame f E)
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    0 < ((ambientFrame G f E z)ᴴ * ambientFrame G f E z).det.re := by
  have hEinj : Function.Injective (E z).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (hE.1 z hz)))
  have hUinj : Function.Injective (ambientFrame G f E z).mulVec := by
    intro v w hvw
    apply hEinj
    apply cotangentDG_mulVec_injective hG (f z)
    simpa only [ambientFrame, Matrix.mulVec_mulVec] using hvw
  exact (Complex.pos_iff.mp (Matrix.PosDef.conjTranspose_mul_self _ hUinj).det_pos).1

theorem frameGramPotential_contDiffOn {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentImmersion G) {f : ℂ → CotangentPoint M}
    {E : ℂ → CotangentMatrix n} (hE : IsDiscFrame f E) :
    ContDiffOn ℝ ∞ (frameGramPotential G f E) (Metric.closedBall (0 : ℂ) 1) := by
  have hU := ambientFrame_entry_contDiffOn hE hG.1
  exact (Complex.reCLM.contDiff.comp_contDiffOn
    (complex_det_contDiffOn (gramEntry_contDiffOn hU))).log
      (fun z hz => (ambientFrame_gram_det_re_pos hG hE hz).ne')

theorem frameInCenteredChart_contDiffAt {f : ℂ → CotangentPoint M}
    {E : ℂ → CotangentMatrix n} (hE : IsDiscFrame f E)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) (i j : CotangentIndex n) :
    ContDiffAt ℂ ∞ (fun w => frameInChart (f z).1 f E w i j) z := by
  obtain ⟨V, hV, hzV, hsource, hframe⟩ := hE.2.2 z (Metric.ball_subset_closedBall hz)
  have hnhds : Metric.closedBall (0 : ℂ) 1 ∩ V ∈ 𝓝 z :=
    inter_mem (mem_of_superset (Metric.isOpen_ball.mem_nhds hz) Metric.ball_subset_closedBall)
      (hV.mem_nhds hzV)
  exact (hframe i j z ⟨Metric.ball_subset_closedBall hz, hzV⟩).contDiffAt hnhds

theorem frameInCenteredChart_det_contDiffAt {f : ℂ → CotangentPoint M}
    {E : ℂ → CotangentMatrix n} (hE : IsDiscFrame f E)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    ContDiffAt ℂ 2 (fun w => (frameInChart (f z).1 f E w).det) z := by
  simp only [Matrix.det_apply']
  exact ContDiffAt.sum fun σ _ => contDiffAt_const.mul
    (contDiffAt_prod fun i _ => (frameInCenteredChart_contDiffAt hE hz (σ i) i).of_le (by simp))

theorem frameGramPotential_local_decomposition {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentImmersion G) {f : ℂ → CotangentPoint M}
    {E : ℂ → CotangentMatrix n} (hE : IsDiscFrame f E)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    (fun w => (frameGramPotential G f E w : ℂ)) =ᶠ[𝓝 z]
      fun w => ((gaussPotential G (f z).1 (cotangentChart (f z).1 (f w)) +
        Real.log (Complex.normSq (frameInChart (f z).1 f E w).det) : ℝ) : ℂ) := by
  obtain ⟨V, hV, hzV, hsource, hframe⟩ := hE.2.2 z (Metric.ball_subset_closedBall hz)
  filter_upwards [hV.mem_nhds hzV, Metric.isOpen_ball.mem_nhds hz] with w hwV hw
  have hwc := Metric.ball_subset_closedBall hw
  have hws := hsource w ⟨hwc, hwV⟩
  have hVpos := cotangentDG_gram_det_re_pos_in_chart hG (f z).1 (f w) hws
  have hSne := frameInChart_det_ne_zero hE hwc (f z).1 hws
  have hSnorm : ‖(frameInChart (f z).1 f E w).det‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr hSne)
  apply congrArg Complex.ofReal
  unfold frameGramPotential
  rw [ambientFrame_in_fixed_chart hG.1 f E (f z).1 w hws,
    gram_det_right_mul, Real.log_mul hVpos.ne' hSnorm]
  unfold gaussPotential
  rw [cotangentChart_left_inv (f z).1 hws, Complex.normSq_eq_norm_sq]

theorem gauss_density_eq_half_closedLaplacian {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentImmersion G) {f : ℂ → CotangentPoint M}
    {E : ℂ → CotangentMatrix n} (hE : IsDiscFrame f E)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    let x := (f z).1
    let v := fderiv ℂ (fun w => cotangentChart x (f w)) z 1
    2 * (wirt (fun w => wirtBar (fun w' => (gaussPotential G x w' : ℂ)) w v)
      (cotangentChart x (f z)) v).re =
      (1 / 2 : ℝ) * closedLaplacian (frameGramPotential G f E) z := by
  let c : ℂ → CotangentCoord n := fun w => cotangentChart (f z).1 (f w)
  let S : ℂ → ℂ := fun w => (frameInChart (f z).1 f E w).det
  have hself : f z ∈ cotangentSource (f z).1 := mem_extChartAt_source _
  have hnhds : Metric.closedBall (0 : ℂ) 1 ∈ 𝓝 z :=
    mem_of_superset (Metric.isOpen_ball.mem_nhds hz) Metric.ball_subset_closedBall
  have hc : ContDiffAt ℂ 2 c z :=
    ((cotangentDisc_coords_contDiffWithinAt hE.2.1 (Metric.ball_subset_closedBall hz)
      (f z).1 hself).contDiffAt hnhds).of_le (by simp)
  have hP : ContDiffAt ℝ 2 (gaussPotential G (f z).1) (c z) :=
    (gaussPotential_contDiffAt hG (f z).1 (cotangentChart_mapsTo (f z).1 hself)).of_le (by simp)
  have hcomp : ContDiffAt ℝ 2 (fun w => gaussPotential G (f z).1 (c w)) z :=
    hP.comp z (hc.restrict_scalars ℝ)
  have hS : ContDiffAt ℂ 2 S z := frameInCenteredChart_det_contDiffAt hE hz
  have hSne : S z ≠ 0 := frameInChart_det_ne_zero hE (Metric.ball_subset_closedBall hz) (f z).1 hself
  have hlogS : ContDiffAt ℝ 2 (fun w => Real.log (Complex.normSq (S w))) z := by
    simp_rw [Complex.normSq_eq_norm_sq]
    exact ((hS.restrict_scalars ℝ).norm_sq (𝕜 := ℂ)).log
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr hSne))
  have hGram : ContDiffAt ℝ 2 (frameGramPotential G f E) z :=
    ((frameGramPotential_contDiffOn hG hE).contDiffAt hnhds).of_le (by simp)
  have hm : (wirt (fun w => wirtBar (fun w' => (frameGramPotential G f E w' : ℂ)) w 1) z 1).re =
      (wirt (fun w => wirtBar (fun w' => (gaussPotential G (f z).1 w' : ℂ)) w
        (fderiv ℂ c z 1)) (c z) (fderiv ℂ c z 1)).re := by
    rw [mixedWirt_congr (frameGramPotential_local_decomposition hG hE hz),
      mixedWirt_real_add hcomp hlogS,
      mixedWirt_log_normSq_holomorphic_zero hS hSne, add_zero]
    exact mixedWirt_holomorphic_comp_re hc hP 1
  dsimp only
  change 2 * (wirt (fun w => wirtBar (fun w' => (gaussPotential G (f z).1 w' : ℂ)) w
    (fderiv ℂ c z 1)) (c z) (fderiv ℂ c z 1)).re = _
  rw [← hm, mixedWirt_real_diagonal hGram, closedLaplacian_eq hz]
  simp only [smul_eq_mul, mul_one]
  ring

theorem gauss_density_integrableOn {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentImmersion G) {f : ℂ → CotangentPoint M}
    {E : ℂ → CotangentMatrix n} (hE : IsDiscFrame f E) :
    IntegrableOn (fun z =>
      let x := (f z).1
      let v := fderiv ℂ (fun w => cotangentChart x (f w)) z 1
      2 * (wirt (fun w => wirtBar (fun w' => (gaussPotential G x w' : ℂ)) w v)
        (cotangentChart x (f z)) v).re) (Metric.ball (0 : ℂ) 1) volume := by
  have hLap : IntegrableOn (closedLaplacian (frameGramPotential G f E))
      (Metric.ball (0 : ℂ) 1) volume :=
    ((closedLaplacian_contDiffOn (frameGramPotential_contDiffOn hG hE)).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : ℂ) 1)).mono_set Metric.ball_subset_closedBall
  apply (hLap.const_mul (1 / 2 : ℝ)).congr
  filter_upwards [self_mem_ae_restrict measurableSet_ball] with z hz
  exact (gauss_density_eq_half_closedLaplacian hG hE hz).symm

theorem gaussArea_eq_frameGram_integral {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentImmersion G) {f : ℂ → CotangentPoint M}
    {E : ℂ → CotangentMatrix n} (hE : IsDiscFrame f E) :
    gaussArea G f = (1 / 2 : ℝ) * ∫ z in Metric.ball (0 : ℂ) 1,
      closedLaplacian (frameGramPotential G f E) z := by
  unfold gaussArea
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_ball
  intro z hz
  dsimp only
  exact gauss_density_eq_half_closedLaplacian hG hE hz

theorem normalizedFrame_gaussFourier {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentImmersion G) {f : ℂ → CotangentPoint M}
    {E : ℂ → CotangentMatrix n} (hE : IsDiscFrame f E)
    (hBoundary : ∀ θ : ℝ,
      (ambientFrame G f E (circlePoint θ))ᴴ * ambientFrame G f E (circlePoint θ) = 1) :
    matrixDSq (fun θ => ambientFrame G f E (circlePoint θ)) =
      ENNReal.ofReal (gaussArea G f / (2 * Real.pi)) := by
  rw [gaussArea_eq_frameGram_integral hG hE]
  exact normalized_gram_fourier (ambientFrame_entry_contDiffOn hE hG.1)
    (fun z hz => (ambientFrame_gram_det_re_pos hG hE hz).ne') hBoundary

end Yau.Blueprint.D05Proof
