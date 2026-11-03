import Yau.Proofs.V03LogSumPositive
import Yau.Proofs.V03HolomorphicSmooth
import Yau.Proofs.V03Charts

/-! Semipositivity of the actual local Plücker potential of the original
immersion. Its computed Gauss area is therefore nonnegative. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {M : ComplexManifold n}

def cotangentDGMinor (G : CotangentPoint M → ComplexVector q) (x : M.Carrier)
    (p : CotangentIndex n → Fin q) (z : CotangentCoord n) : ℂ :=
  ((cotangentDG G x (cotangentChartInv x z)).submatrix p id).det

theorem cotangentDGMinor_contDiffAt {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentHolomorphic G) (x : M.Carrier) {z : CotangentCoord n}
    (hz : z ∈ cotangentTarget x) (p : CotangentIndex n → Fin q) :
    ContDiffAt ℂ 2 (cotangentDGMinor G x p) z := by
  have ho : IsOpen (cotangentTarget x) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ
  have hchart := (cotangentHolomorphic_chart_contDiffOn hG x).contDiffAt (ho.mem_nhds hz)
  have hD := hchart.fderiv_right (m := 2) (by simp)
  let J : CotangentCoord n → Matrix (Fin q) (CotangentIndex n) ℂ := fun w a b =>
    (fderiv ℂ (fun w' => G (cotangentChartInv x w')) w (cotangentDir b)) a
  have hentry (a : Fin q) (b : CotangentIndex n) : ContDiffAt ℂ 2 (fun w => J w a b) z :=
    (contDiffAt_piLp_apply (p := 2) (i := a)).comp z (hD.clm_apply contDiffAt_const)
  have hminor : ContDiffAt ℂ 2 (fun w => ((J w).submatrix p id).det) z := by
    simp only [Matrix.det_apply', Matrix.submatrix_apply, id_eq]
    exact ContDiffAt.sum fun σ _ => contDiffAt_const.mul
      (contDiffAt_prod fun i _ => hentry (p (σ i)) i)
  apply hminor.congr_of_eventuallyEq
  filter_upwards [ho.mem_nhds hz] with w hw
  unfold cotangentDGMinor cotangentDG
  rw [cotangentChart_right_inv x hw]

theorem gaussPotential_eq_log_sqSum (G : CotangentPoint M → ComplexVector q)
    (x : M.Carrier) (z : CotangentCoord n) :
    gaussPotential G x z = Real.log
      ((Fintype.card (Equiv.Perm (CotangentIndex n)) : ℝ)⁻¹ *
        holomorphicSqSum (cotangentDGMinor G x) z) := by
  dsimp only [gaussPotential]
  rw [gram_det_re_eq_sum_tuple_minors]
  rfl

theorem gaussPotential_levi_nonneg {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentImmersion G) (y : CotangentPoint M) (v : CotangentCoord n) :
    0 ≤ (wirt (fun z => wirtBar (fun z' => (gaussPotential G y.1 z' : ℂ)) z v)
      (cotangentChart y.1 y) v).re := by
  let z := cotangentChart y.1 y
  have hsource : y ∈ cotangentSource y.1 := mem_extChartAt_source _
  have hz : z ∈ cotangentTarget y.1 := cotangentChart_mapsTo y.1 hsource
  have hminor := cotangentDGMinor_contDiffAt hG.1 y.1 hz
  have hS := holomorphicSqSum_contDiffAt hminor
  have hc : 0 < (Fintype.card (Equiv.Perm (CotangentIndex n)) : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Equiv.Perm (CotangentIndex n)))
  have hg := cotangentDG_gram_det_re_pos hG y
  have heq := gram_det_re_eq_sum_tuple_minors (cotangentDG G y.1 y)
  have hpoint : cotangentChartInv y.1 z = y := cotangentChart_left_inv y.1 hsource
  have hsum : holomorphicSqSum (cotangentDGMinor G y.1) z =
      ∑ p : CotangentIndex n → Fin q, ‖((cotangentDG G y.1 y).submatrix p id).det‖ ^ 2 := by
    simp only [holomorphicSqSum, cotangentDGMinor, hpoint]
  rw [heq, ← hsum] at hg
  have hs : 0 < holomorphicSqSum (cotangentDGMinor G y.1) z :=
    pos_of_mul_pos_right hg (inv_nonneg.mpr hc.le)
  simp_rw [gaussPotential_eq_log_sqSum]
  rw [mixedWirt_log_const_mul hS.continuousAt hs.ne' (inv_ne_zero hc.ne')]
  exact log_holomorphicSqSum_levi_nonneg hminor hs v

theorem gaussArea_nonneg_of_immersion {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentImmersion G) (f : ℂ → CotangentPoint M) : 0 ≤ gaussArea G f := by
  apply integral_nonneg
  intro ζ
  exact mul_nonneg (by norm_num) (gaussPotential_levi_nonneg hG (f ζ) _)

end Yau.Blueprint.V03Proof
