import Yau.Proofs.B01Coordinate
import Yau.LeafProofs.L14Gauge
import Yau.LeafProofs.L23FieldMetric

open scoped Manifold Topology ContDiff ENNReal Matrix ComplexOrder
open MeasureTheory Set

noncomputable section

namespace Yau.Proofs.B01Aux
open Yau Yau.Blueprint Yau.Blueprint.BundlePresentation

variable {M : ComplexManifold 1}

def discPullbackMetric (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (η : ℂ → ℝ) (hη : ∀ z ∈ puncturedUnitDisc, 0 < η z) : HermitianField M := fun x =>
  { toFun := fun u v => (η (c x) : ℂ) * star (discDerivative c x u) * discDerivative c x v
    map_add_left := by intros; simp only [map_add, star_add]; ring
    map_smul_left := by intros; simp only [map_smul, smul_eq_mul, star_mul]; ring
    map_add_right := by intros; simp only [map_add]; ring
    map_smul_right := by intros; simp only [map_smul, smul_eq_mul]; ring
    conjugate_symmetric := by
      intros
      simp only [star_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
      ring
    self_adjoint := by
      intro u
      simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.star_def, Complex.conj_re, Complex.conj_im]
      ring
    positive_definite := by
      intro u
      have hηx := hη (c x) (disc_mem c hc x)
      have he : ((η (c x) : ℂ) * star (discDerivative c x u) * discDerivative c x u).re =
          η (c x) * Complex.normSq (discDerivative c x u) := by
        simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
        ring
      rw [he]
      refine ⟨mul_nonneg hηx.le (Complex.normSq_nonneg _), ?_⟩
      constructor
      · intro hz
        have hd := Complex.normSq_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hηx.ne')
        apply disc_mfderiv_injective c hc x
        change discDerivative c x u = discDerivative c x 0
        rw [map_zero]
        exact hd
      · rintro rfl
        simp only [map_zero, mul_zero] }

@[simp] theorem discPullbackMetric_apply (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (η : ℂ → ℝ) (hη : ∀ z ∈ puncturedUnitDisc, 0 < η z)
    (x : M.Carrier) (u v : TangentVector M x) :
    (discPullbackMetric c hc η hη x).toFun u v = (η (c x) : ℂ) *
      star (show ℂ from mfderiv (ComplexModel 1) 𝓘(ℂ, ℂ) c x u) *
        (show ℂ from mfderiv (ComplexModel 1) 𝓘(ℂ, ℂ) c x v) := rfl

theorem discPullbackMetric_normSq (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (η : ℂ → ℝ) (hη : ∀ z ∈ puncturedUnitDisc, 0 < η z)
    (x : M.Carrier) (u : TangentVector M x) :
    hermitianNormSq (discPullbackMetric c hc η hη x) u =
      η (c x) * Complex.normSq (discDerivative c x u) := by
  simp only [hermitianNormSq, discPullbackMetric, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im, Complex.normSq_apply]
  ring

theorem discDerivative_chartVec (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (a : M.Carrier) {z : ComplexVector 1} (hz : z ∈ chartTarget a) (v : ComplexVector 1) :
    discDerivative c (chartInv a z) (chartVec a (chartInv a z) v) =
      wirt (fun w => c (chartInv a w)) z v :=
  (disc_inChart_fderiv c hc a hz v).symm.trans
    (LeafProofs.L14Aux.wirt_eq_fderiv_of_complex_differentiable _ _ _
      ((disc_inChart_contDiffAt c hc a hz).differentiableAt (by simp))).symm

theorem discPullbackMetric_pairing_contDiffOn (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (η : ℂ → ℝ) (hη : ∀ z ∈ puncturedUnitDisc, 0 < η z)
    (hηs : ContDiffOn ℝ ∞ η puncturedUnitDisc) (a : M.Carrier) (v w : ComplexVector 1) :
    ContDiffOn ℝ ∞ (fun z => (discPullbackMetric c hc η hη (chartInv a z)).toFun
      (chartVec a (chartInv a z) v) (chartVec a (chartInv a z) w)) (chartTarget a) := by
  have hF : ContDiffOn ℝ ∞ (fun z => c (chartInv a z)) (chartTarget a) :=
    fun z hz => ((disc_inChart_contDiffAt c hc a hz).restrict_scalars ℝ).contDiffWithinAt
  have hηF := hηs.comp hF (fun z _ => disc_mem c hc (chartInv a z))
  have hηC : ContDiffOn ℝ ∞ (fun z => (η (c (chartInv a z)) : ℂ)) (chartTarget a) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hηF
  have hV := LeafProofs.L14Aux.wirt_contDiffOn (isOpen_extChartAt_target a) _ hF v
  have hW := LeafProofs.L14Aux.wirt_contDiffOn (isOpen_extChartAt_target a) _ hF w
  have hVc : ContDiffOn ℝ ∞ (fun z => star (wirt (fun t => c (chartInv a t)) z v))
      (chartTarget a) := Complex.conjCLE.contDiff.comp_contDiffOn hV
  apply ((hηC.mul hVc).mul hW).congr
  intro z hz
  change (η (c (chartInv a z)) : ℂ) *
    star (discDerivative c (chartInv a z) (chartVec a (chartInv a z) v)) *
      discDerivative c (chartInv a z) (chartVec a (chartInv a z) w) = _
  rw [discDerivative_chartVec c hc a hz v, discDerivative_chartVec c hc a hz w]

theorem discPullbackMetric_smooth (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (η : ℂ → ℝ) (hη : ∀ z ∈ puncturedUnitDisc, 0 < η z)
    (hηs : ContDiffOn ℝ ∞ η puncturedUnitDisc) : MetricSmooth (discPullbackMetric c hc η hη) := by
  intro a i j
  exact contDiffOn_const.mul (Complex.reCLM.contDiff.comp_contDiffOn
    (discPullbackMetric_pairing_contDiffOn c hc η hη hηs a (realVec i) (realVec j)))

theorem discPullbackMetric_coordinate_smooth (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (η : ℂ → ℝ) (hη : ∀ z ∈ puncturedUnitDisc, 0 < η z)
    (hηs : ContDiffOn ℝ ∞ η puncturedUnitDisc) (a : M.Carrier) (i j : Fin 1) :
    ContDiffOn ℝ ∞ (chartCoefficientFunction (discPullbackMetric c hc η hη) a i j)
      (extChartAt (ComplexModel 1) a).target :=
  discPullbackMetric_pairing_contDiffOn c hc η hη hηs a (stdVec i) (stdVec j)

theorem chartVectorInFrame_eq_chartVec (a x : M.Carrier) (u : ComplexVector 1) :
    chartVectorInFrame a x u = chartVec a x u := by
  have hu : u = u 0 • stdVec 0 := by
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [stdVec]
  let d : ComplexVector 1 →ₗ[ℂ] TangentVector M x :=
    ((mfderiv (ComplexModel 1) (ComplexModel 1) (extChartAt (ComplexModel 1) a).symm
      (chartPt a x)).comp (tangentSpaceCastModel (ComplexModel 1) (chartPt a x)).symm.toContinuousLinearMap).toLinearMap
  change (∑ i : Fin 1, u i • d (stdVec i)) = d u
  simp only [Fin.sum_univ_one]
  exact (d.map_smul (u 0) (stdVec 0)).symm.trans (congrArg d hu.symm)

theorem hermitianField_chartTransition (h : HermitianField M) : HermitianFieldChartTransition h := by
  intro a b x ha hb u v
  have ht (w : ComplexVector 1) : chartVec b x (chartFrameChange b a x w) = chartVec a x w := by
    have hp : chartInv a (chartPt a x) = x := (extChartAt (ComplexModel 1) a).left_inv ha
    have hz : chartPt a x ∈ chartTarget a := (extChartAt (ComplexModel 1) a).map_source ha
    have he := LeafProofs.L12Aux.chartTransition_fderiv a b hz (hp.symm ▸ hb) w
    change chartFrameChange b a x w = _ at he
    rw [hp] at he
    rw [he]
    exact LeafProofs.L12Aux.chartVec_tangentCoords b x hb _
  simp only [chartVectorInFrame_eq_chartVec, ht]

theorem hermitianField_kahler_one (h : HermitianField M) : KahlerCoordinateCondition h := by
  intro x a b c
  have hdiag (i : RIdx 1) : (fun z => kahlerFormFn h x z i i) = 0 := by
    funext z
    simp only [kahlerFormFn, (h (chartInv x z)).self_adjoint, mul_zero, Pi.zero_apply]
  have hswap : (fun z => kahlerFormFn h x z (0, 1) (0, 0)) =
      -(fun z => kahlerFormFn h x z (0, 0) (0, 1)) := by
    funext z
    unfold kahlerFormFn
    rw [(h (chartInv x z)).conjugate_symmetric]
    simp only [Complex.star_def, Complex.conj_im, Pi.neg_apply, mul_neg]
  rcases a with ⟨a, a'⟩
  rcases b with ⟨b, b'⟩
  rcases c with ⟨c, c'⟩
  fin_cases a <;> fin_cases b <;> fin_cases c
  fin_cases a' <;> fin_cases b' <;> fin_cases c' <;>
    simp [rDeriv, hdiag, hswap, fderiv_neg]

theorem completeDiscDensity_pos {z : ℂ} (hz : z ∈ puncturedUnitDisc) :
    0 < completeDiscDensity z := by
  have hlog : Real.log ‖z‖ < 0 := Real.log_neg hz.1 hz.2
  exact inv_pos.mpr (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hz.1)) (sq_pos_of_neg hlog))

theorem completeDiscDensity_contDiffOn : ContDiffOn ℝ ∞ completeDiscDensity puncturedUnitDisc := by
  intro z hz
  have hn : ContDiffAt ℝ ∞ (fun w : ℂ => ‖w‖) z := contDiffAt_norm ℝ (norm_pos_iff.mp hz.1)
  have hl := hn.log hz.1.ne'
  have hden : 2 * ‖z‖ ^ 2 * (Real.log ‖z‖) ^ 2 ≠ 0 :=
    ne_of_gt (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hz.1))
      (sq_pos_of_neg (Real.log_neg hz.1 hz.2)))
  have hdenS : ContDiffAt ℝ ∞ (fun w : ℂ => (2 : ℝ) * ‖w‖ ^ 2 * (Real.log ‖w‖) ^ 2) z :=
    (contDiffAt_const.mul (hn.pow 2)).mul (hl.pow 2)
  exact (hdenS.inv hden).contDiffWithinAt

def flatDiscField (c : DiscCoordinate M) (hc : IsDiscCoordinate c) : HermitianField M :=
  discPullbackMetric c hc (fun _ => 1) (fun _ _ => zero_lt_one)

theorem flatDiscField_smooth (c : DiscCoordinate M) (hc : IsDiscCoordinate c) :
    MetricSmooth (flatDiscField c hc) :=
  discPullbackMetric_smooth c hc _ _ contDiffOn_const

def cuspDiscField (c : DiscCoordinate M) (hc : IsDiscCoordinate c) : HermitianField M :=
  discPullbackMetric c hc completeDiscDensity (fun _ hz => completeDiscDensity_pos hz)

theorem cuspDiscField_smooth (c : DiscCoordinate M) (hc : IsDiscCoordinate c) :
    MetricSmooth (cuspDiscField c hc) :=
  discPullbackMetric_smooth c hc _ _ completeDiscDensity_contDiffOn

end Yau.Proofs.B01Aux
