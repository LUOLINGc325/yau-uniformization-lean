import Yau.Proofs.V03GaussPositive
import Yau.Proofs.V03TransitionInverse
import Yau.Proofs.V03Pluriharmonic

/-! Smoothness and the exact determinant chart law of the actual Gauss
potential, with the transition determinant computed from the native charts. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {M : ComplexManifold n}

theorem cotangentDGMinor_contDiffAt_infty {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentHolomorphic G) (x : M.Carrier) {z : CotangentCoord n}
    (hz : z ∈ cotangentTarget x) (p : CotangentIndex n → Fin q) :
    ContDiffAt ℂ ∞ (cotangentDGMinor G x p) z := by
  have ho : IsOpen (cotangentTarget x) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ
  have hchart := (cotangentHolomorphic_chart_contDiffOn hG x).contDiffAt (ho.mem_nhds hz)
  have hD := hchart.fderiv_right (m := ∞) (by simp)
  let J : CotangentCoord n → Matrix (Fin q) (CotangentIndex n) ℂ := fun w a b =>
    (fderiv ℂ (fun w' => G (cotangentChartInv x w')) w (cotangentDir b)) a
  have hentry (a : Fin q) (b : CotangentIndex n) : ContDiffAt ℂ ∞ (fun w => J w a b) z :=
    (contDiffAt_piLp_apply (p := 2) (i := a)).comp z (hD.clm_apply contDiffAt_const)
  have hminor : ContDiffAt ℂ ∞ (fun w => ((J w).submatrix p id).det) z := by
    simp only [Matrix.det_apply', Matrix.submatrix_apply, id_eq]
    exact ContDiffAt.sum fun σ _ => contDiffAt_const.mul
      (contDiffAt_prod fun i _ => hentry (p (σ i)) i)
  apply hminor.congr_of_eventuallyEq
  filter_upwards [ho.mem_nhds hz] with w hw
  unfold cotangentDGMinor cotangentDG
  rw [cotangentChart_right_inv x hw]

theorem gaussPotential_contDiffAt {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentImmersion G) (x : M.Carrier) {z : CotangentCoord n}
    (hz : z ∈ cotangentTarget x) : ContDiffAt ℝ ∞ (gaussPotential G x) z := by
  have hS := holomorphicSqSum_contDiffAt (cotangentDGMinor_contDiffAt_infty hG.1 x hz)
  have hpos := cotangentDG_gram_det_re_pos_in_chart hG x (cotangentChartInv x z)
    (cotangentChartInv_mapsTo x hz)
  rw [gram_det_re_eq_sum_tuple_minors] at hpos
  change 0 < (Fintype.card (Equiv.Perm (CotangentIndex n)) : ℝ)⁻¹ *
    holomorphicSqSum (cotangentDGMinor G x) z at hpos
  have hlog : ContDiffAt ℝ ∞ (fun w => Real.log
      ((Fintype.card (Equiv.Perm (CotangentIndex n)) : ℝ)⁻¹ *
        holomorphicSqSum (cotangentDGMinor G x) w)) z :=
    (contDiffAt_const.mul hS).log hpos.ne'
  exact hlog.congr_of_eventuallyEq (Eventually.of_forall (gaussPotential_eq_log_sqSum G x))

theorem gram_det_right_mul {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (J : Matrix κ ι ℂ) (T : Matrix ι ι ℂ) :
    ((J * T)ᴴ * (J * T)).det.re = (Jᴴ * J).det.re * ‖T.det‖ ^ 2 := by
  have hm : (J * T)ᴴ * (J * T) = Tᴴ * (Jᴴ * J) * T := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [hm, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
  have hp : star T.det * (Jᴴ * J).det * T.det = (Jᴴ * J).det * (star T.det * T.det) := by
    ring
  rw [hp, star_mul_self_eq_norm_sq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

def cotangentTransitionDet (x x' : M.Carrier) (z : CotangentCoord n) : ℂ :=
  (cotangentTransition x x' (cotangentChartInv x z)).det

theorem cotangentTransitionDet_ne_zero (x x' : M.Carrier) {z : CotangentCoord n}
    (hz : z ∈ cotangentTarget x)
    (hz' : chartInv x z.1 ∈ (extChartAt (ComplexModel n) x').source) :
    cotangentTransitionDet x x' z ≠ 0 := by
  have hi := cotangentTransition_mulVec_injective x x' (cotangentChartInv x z)
    (cotangentChartInv_mapsTo x hz) hz'
  exact ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp hi)).ne_zero

theorem cotangentTransitionDet_contDiffAt (x x' : M.Carrier) {z : CotangentCoord n}
    (hz : z ∈ cotangentTarget x)
    (hz' : chartInv x z.1 ∈ (extChartAt (ComplexModel n) x').source) :
    ContDiffAt ℂ 2 (cotangentTransitionDet x x') z := by
  have hT := cotangentChartTransition_contDiffAt x x' hz hz'
  have hD := hT.fderiv_right (m := 2) (by simp)
  let J : CotangentCoord n → CotangentMatrix n := fun w a b =>
    cotangentCoordsVector (fderiv ℂ
      (fun w' => cotangentChart x' (cotangentChartInv x w')) w (cotangentDir b)) a
  have hentry (a b : CotangentIndex n) : ContDiffAt ℂ 2 (fun w => J w a b) z := by
    have hc : ContDiffAt ℂ 2 (fun w => fderiv ℂ
        (fun w' => cotangentChart x' (cotangentChartInv x w')) w (cotangentDir b)) z :=
      hD.clm_apply contDiffAt_const
    cases a with
    | inl a =>
      exact (contDiffAt_piLp_apply (p := 2) (i := a)).comp z hc.fst
    | inr a =>
      exact (contDiffAt_piLp_apply (p := 2) (i := a)).comp z hc.snd
  have hdet : ContDiffAt ℂ 2 (fun w => (J w).det) z := by
    simp only [Matrix.det_apply']
    exact ContDiffAt.sum fun σ _ => contDiffAt_const.mul
      (contDiffAt_prod fun i _ => hentry (σ i) i)
  apply hdet.congr_of_eventuallyEq
  filter_upwards [((isOpen_extChartAt_target (I := ComplexModel n) x).prod
    isOpen_univ).mem_nhds hz] with w hw
  unfold cotangentTransitionDet cotangentTransition
  rw [cotangentChart_right_inv x hw]

theorem gaussPotential_chart_change {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentImmersion G) (x x' : M.Carrier) {z : CotangentCoord n}
    (hz : z ∈ cotangentTarget x)
    (hz' : chartInv x z.1 ∈ (extChartAt (ComplexModel n) x').source) :
    gaussPotential G x z =
      gaussPotential G x' (cotangentChart x' (cotangentChartInv x z)) +
        Real.log (Complex.normSq (cotangentTransitionDet x x' z)) := by
  have hy := cotangentChartInv_mapsTo x hz
  have hround : cotangentChartInv x' (cotangentChart x' (cotangentChartInv x z)) =
      cotangentChartInv x z := cotangentChart_left_inv x' hz'
  have hJ := cotangentDG_transition hG.1 x x' (cotangentChartInv x z) hy hz'
  have hp := cotangentDG_gram_det_re_pos_in_chart hG x' (cotangentChartInv x z) hz'
  have hne : ‖(cotangentTransition x x' (cotangentChartInv x z)).det‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (cotangentTransitionDet_ne_zero x x' hz hz'))
  dsimp only [gaussPotential]
  rw [hround, hJ, gram_det_right_mul, Real.log_mul hp.ne' hne,
    Complex.normSq_eq_norm_sq]
  rfl

end Yau.Blueprint.V03Proof
