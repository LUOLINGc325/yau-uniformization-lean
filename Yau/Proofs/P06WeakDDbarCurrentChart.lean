import Yau.Proofs.P06WeakDDbarCurrentGreen
import Yau.Proofs.P06WeakDDbarCurrentMatrixDual
import Yau.Proofs.G04TraceChart
import Yau.Proofs.G04RicciForm

noncomputable section
open MeasureTheory Filter
open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.P06Aux.WeakCurrent
open Yau Yau.LeafProofs Yau.LeafProofs.L03 Yau.NodeProofs.G04Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

/-- The actual Hermitian coefficient matrix in a fixed chart. -/
def chartHermitianMatrix (B : RealForm M 2) (c : M.Carrier) (z : ComplexVector n) :
    Matrix (Fin n) (Fin n) ℂ := alternatingMatrix (chartForm B c z)

theorem chartHermitianMatrix_hermitian (B : RealForm M 2) (h11 : RealOneOne B)
    (c : M.Carrier) (z : ComplexVector n) : (chartHermitianMatrix B c z).IsHermitian :=
  alternatingMatrix_hermitian _ (chartForm_oneOne B h11 c z)

theorem chartHermitianMatrix_raw (B : RealForm M 2) (h11 : RealOneOne B)
    (c : M.Carrier) (z : ComplexVector n) :
    chartFormMatrix B c z = (-2 : ℝ) •
      (G01Aux.rawReal (chartHermitianMatrix B c z) * L12Aux.jMatrix n) := by
  ext a b
  rw [chartFormMatrix_apply]
  simpa only [alternatingBilin_apply, chartHermitianMatrix] using
    (alternatingMatrix_basis _ (chartForm_oneOne B h11 c z) a b).trans
      (matrixImagBilin_basis_raw _ a b)

theorem chartHermitianMatrix_contDiffOn (B : RealForm M 2) (hB : SmoothRealForm B)
    (c : M.Carrier) (a b : Fin n) :
    ContDiffOn ℝ ∞ (fun z => chartHermitianMatrix B c z a b) (chartTarget c) := by
  have hP := chartForm_contDiffOn B hB c
  have h₀ := (ContinuousAlternatingMap.apply ℝ (ComplexVector n) ℝ
    ![stdVec a, stdVec b]).contDiff.comp_contDiffOn hP
  have h₁ := (ContinuousAlternatingMap.apply ℝ (ComplexVector n) ℝ
    ![stdVec a, Complex.I • stdVec b]).contDiff.comp_contDiffOn hP
  exact ((Complex.ofRealCLM.contDiff.comp_contDiffOn h₁).add
    (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn h₀))).div_const 2

/-- The actual alternating form pairing in any chart has the complex
Hermitian trace formula, with the paper normalization and no extra factor. -/
theorem formInner_chart_oneOne (h : HermitianField M) (A B : RealForm M 2)
    (hA : RealOneOne A) (hB : RealOneOne B) (c : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    formInner h A B (chartInv c z) = (Matrix.trace
      ((hMat h c z)⁻¹ * chartHermitianMatrix A c z *
        (hMat h c z)⁻¹ * chartHermitianMatrix B c z)).re := by
  let H := hMat h c z
  let C := chartHermitianMatrix A c z
  let D := chartHermitianMatrix B c z
  have hinv : (realMetricFn h c z)⁻¹ = (1 / 2 : ℝ) • G01Aux.rawReal H⁻¹ :=
    G01Aux.realMetricFn_inverse_eq h c z hz
  rw [formInner_chart_trace h A B c hz, hinv,
    chartHermitianMatrix_raw A hA, chartHermitianMatrix_raw B hB]
  change -(1 / 2 : ℝ) * Matrix.trace
    (((1 / 2 : ℝ) • G01Aux.rawReal H⁻¹) * ((-2 : ℝ) • (G01Aux.rawReal C * L12Aux.jMatrix n)) *
      ((1 / 2 : ℝ) • G01Aux.rawReal H⁻¹) * ((-2 : ℝ) • (G01Aux.rawReal D * L12Aux.jMatrix n))) = _
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  norm_num only [show (1 / 2 : ℝ) * (-2) * (1 / 2) * (-2) = 1 by norm_num, one_smul]
  have hp : G01Aux.rawReal H⁻¹ * (G01Aux.rawReal C * L12Aux.jMatrix n) *
      G01Aux.rawReal H⁻¹ * (G01Aux.rawReal D * L12Aux.jMatrix n) =
      -G01Aux.rawReal (H⁻¹ * C * H⁻¹ * D) := by
    calc
      _ = G01Aux.rawReal H⁻¹ * G01Aux.rawReal C *
          (L12Aux.jMatrix n * G01Aux.rawReal H⁻¹) * G01Aux.rawReal D * L12Aux.jMatrix n := by noncomm_ring
      _ = G01Aux.rawReal H⁻¹ * G01Aux.rawReal C *
          (G01Aux.rawReal H⁻¹ * L12Aux.jMatrix n) * G01Aux.rawReal D * L12Aux.jMatrix n := by
        rw [rawReal_commute_J]
      _ = G01Aux.rawReal H⁻¹ * G01Aux.rawReal C * G01Aux.rawReal H⁻¹ *
          (L12Aux.jMatrix n * G01Aux.rawReal D) * L12Aux.jMatrix n := by noncomm_ring
      _ = G01Aux.rawReal H⁻¹ * G01Aux.rawReal C * G01Aux.rawReal H⁻¹ *
          (G01Aux.rawReal D * L12Aux.jMatrix n) * L12Aux.jMatrix n := by rw [rawReal_commute_J]
      _ = -(G01Aux.rawReal H⁻¹ * G01Aux.rawReal C * G01Aux.rawReal H⁻¹ * G01Aux.rawReal D) := by
        simp only [Matrix.mul_assoc, L12Aux.jMatrix_sq, Matrix.mul_neg, Matrix.mul_one]
      _ = _ := by simp only [G01Aux.rawReal_mul]
  rw [hp, Matrix.trace_neg, G01Aux.rawReal_trace]
  dsimp only [H, C, D]
  ring

theorem alternatingMatrix_eq_of_represents
    (P : (ComplexVector n) [⋀^Fin 2]→L[ℝ] ℝ) (D : Matrix (Fin n) (Fin n) ℂ)
    (hP : ∀ u v, P ![u,v] = 2 * (matrixPairing D u v).im) :
    alternatingMatrix P = D := by
  ext a b
  have h₀ := hP (stdVec a) (stdVec b)
  have h₁ := hP (stdVec a) (Complex.I • stdVec b)
  rw [matrixPairing_std] at h₀
  rw [matrixPairing_smul_right, matrixPairing_std] at h₁
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    zero_add] at h₁
  simp only [alternatingMatrix, h₀, h₁]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

theorem chartHermitianMatrix_congruence (B : RealForm M 2) (h11 : RealOneOne B)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    chartHermitianMatrix B c z =
      let y := chartInv c z
      let D := L17Aux.linearMatrix (L17Aux.coordinateDifferential (inverseChart c) y z)
      Dᴴ * formHermitianMatrix B y * D := by
  apply alternatingMatrix_eq_of_represents
  intro u v
  have hD (w : ComplexVector n) :
      L17Aux.coordinateDifferential (inverseChart c) (chartInv c z) z w =
        tangentCoords (chartInv c z) (chartInv c z) (chartVec c (chartInv c z) w) := by
    rw [chartVec_inverseChart c hz]
    rfl
  rw [matrixPairing_congruence, chartForm_apply_two]
  simp only [hD]
  simpa only [matrixPairing, L12Aux.chartVec_tangentCoords _ _ (mem_extChartAt_source _)] using
    (representsSelf B h11).1 (chartInv c z)
      (tangentCoords (chartInv c z) (chartInv c z) (chartVec c (chartInv c z) u))
      (tangentCoords (chartInv c z) (chartInv c z) (chartVec c (chartInv c z) v))

theorem chartHermitianMatrix_nonnegative (B : RealForm M 2) (h11 : RealOneOne B)
    (hp : FormLE 0 B) (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    (chartHermitianMatrix B c z).PosSemidef := by
  rw [chartHermitianMatrix_congruence B h11 c hz]
  apply Matrix.PosSemidef.conjTranspose_mul_mul_same
  simpa only [formHermitianMatrix_zero, sub_zero] using hp (chartInv c z)

theorem chartHermitianMatrix_dd (f : M.Carrier → ℝ) (hf : SmoothFn f)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    chartHermitianMatrix (ddRealForm f) c z = leviC (inChart c f) z := by
  apply alternatingMatrix_eq_of_represents
  intro u v
  rw [← alternatingBilin_apply,
    L12Aux.realBilin_eq_sum (alternatingBilin (chartForm (ddRealForm f) c z)) u v,
    ← matrixImagBilin_apply, L12Aux.realBilin_eq_sum (matrixImagBilin (leviC (inChart c f) z)) u v]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have he : alternatingBilin (chartForm (ddRealForm f) c z) (realVec a) (realVec b) =
      matrixImagBilin (leviC (inChart c f) z) (realVec a) (realVec b) := by
    rw [alternatingBilin_apply, ← chartFormMatrix_apply]
    exact dd_coefficients f hf c hz ![a,b]
  rw [he]

/-- The positive chart matrix dual retains the actual volume density. -/
def weightedChartMatrix (g : HermitianField M) (B : RealForm M 2)
    (c : M.Carrier) (z : ComplexVector n) : Matrix (Fin n) (Fin n) ℂ :=
  (Real.sqrt (realMetricFn g c z).det : ℂ) •
    ((hMat g c z)⁻¹ * chartHermitianMatrix B c z * (hMat g c z)⁻¹)

theorem weightedChartMatrix_nonnegative (g : HermitianField M) (B : RealForm M 2)
    (h11 : RealOneOne B) (hp : FormLE 0 B) (c : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    (weightedChartMatrix g B c z).PosSemidef := by
  have hC := chartHermitianMatrix_nonnegative B h11 hp c hz
  have hi := (L12Aux.hMat_posDef g c z hz).inv.isHermitian
  have hQ := hC.mul_mul_conjTranspose_same ((hMat g c z)⁻¹)
  rw [hi.eq] at hQ
  exact hQ.smul (by exact_mod_cast Real.sqrt_nonneg (realMetricFn g c z).det)

theorem weightedChartMatrix_dd_pair (g : HermitianField M)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (B : RealForm M 2) (h11 : RealOneOne B)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    Real.sqrt (realMetricFn g c z).det * formInner g (ddRealForm f) B (chartInv c z) =
      (Matrix.trace (leviC (inChart c f) z * weightedChartMatrix g B c z)).re := by
  rw [formInner_chart_oneOne g _ B (dd_properties f hf).2.1 h11 c hz,
    chartHermitianMatrix_dd f hf c hz]
  simp only [weightedChartMatrix, Matrix.mul_smul, Matrix.trace_smul,
    smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  congr 1
  have he : Matrix.trace ((hMat g c z)⁻¹ * leviC (inChart c f) z *
      (hMat g c z)⁻¹ * chartHermitianMatrix B c z) =
      Matrix.trace (leviC (inChart c f) z *
        ((hMat g c z)⁻¹ * chartHermitianMatrix B c z * (hMat g c z)⁻¹)) := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]
    congr 1
    noncomm_ring
  rw [he]

end Yau.NodeProofs.P06Aux.WeakCurrent
