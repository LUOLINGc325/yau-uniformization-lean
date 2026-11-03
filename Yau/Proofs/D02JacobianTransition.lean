import Yau.Proofs.D02Geometry

/-! The computed immersion potential is independent of the valid chart.
Both the Gram determinant and the metric determinant use the same actual
frame change, so their ratio is invariant. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof
set_option backward.isDefEq.respectTransparency false

variable {n N : ℕ} {M : ComplexManifold n}

theorem immersionDerivativeMatrix_apply {F : M.Carrier → ComplexVector N}
    (hF : IsHolomorphicVecMap F) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (a : Fin N) (b : Fin n) :
    immersionDerivativeMatrix F x z a b =
      (NormedSpace.fromTangentSpace (𝕜 := ℂ) (F (chartInv x z)))
        (mfderiv (ComplexModel n) (ComplexModel N) F (chartInv x z)
          (chartVec x (chartInv x z) (stdVec b))) a := by
  exact congrArg (fun v : ComplexVector N => v a) (immersionInChart_fderiv_apply hF x hz (stdVec b))

theorem immersionDerivativeMatrix_centered_apply {F : M.Carrier → ComplexVector N}
    (hF : IsHolomorphicVecMap F) (y : M.Carrier) (a : Fin N) (b : Fin n) :
    immersionDerivativeMatrix F y (chartPt y y) a b =
      (NormedSpace.fromTangentSpace (𝕜 := ℂ) (F y))
        (mfderiv (ComplexModel n) (ComplexModel N) F y (chartVec y y (stdVec b))) a := by
  have hh := immersionDerivativeMatrix_apply hF y
    ((extChartAt (ComplexModel n) y).map_source (mem_extChartAt_source y)) a b
  have hround : chartInv y (chartPt y y) = y :=
    (extChartAt (ComplexModel n) y).left_inv (mem_extChartAt_source y)
  change immersionDerivativeMatrix F y (chartPt y y) a b =
    (NormedSpace.fromTangentSpace (𝕜 := ℂ) (F (chartInv y (chartPt y y))))
      (mfderiv (ComplexModel n) (ComplexModel N) F (chartInv y (chartPt y y))
        (chartVec y (chartInv y (chartPt y y)) (stdVec b))) a at hh
  rw [hround] at hh
  exact hh

theorem immersionDerivativeMatrix_eq_centered_mul {F : M.Carrier → ComplexVector N}
    (hF : IsHolomorphicVecMap F) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) :
    immersionDerivativeMatrix F x z =
      immersionDerivativeMatrix F (chartInv x z) (chartPt (chartInv x z) (chartInv x z)) *
        tangentFrameMatrix x (chartInv x z) (chartInv x z) := by
  ext a b
  rw [Matrix.mul_apply, immersionDerivativeMatrix_apply hF x hz]
  rw [chartVec_eq_centered_sum x (chartInv x z)
    ((extChartAt (ComplexModel n) x).map_target hz) (stdVec b)]
  simp only [map_sum, map_smul]
  simp only [immersionDerivativeMatrix_centered_apply hF, tangentFrameMatrix,
    WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem immersionGram_eq_centered_congruence {F : M.Carrier → ComplexVector N}
    (hF : IsHolomorphicVecMap F) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) :
    immersionGram F x z =
      (tangentFrameMatrix x (chartInv x z) (chartInv x z))ᴴ *
        immersionGram F (chartInv x z) (chartPt (chartInv x z) (chartInv x z)) *
          tangentFrameMatrix x (chartInv x z) (chartInv x z) := by
  unfold immersionGram
  rw [immersionDerivativeMatrix_eq_centered_mul hF x hz]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- The determinant ratio is invariant under one invertible Hermitian congruence. -/
theorem det_re_congruence_ratio (A H T : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosDef) (hH : H.PosDef) (hT : IsUnit T) :
    (Tᴴ * A * T).det.re / (Tᴴ * H * T).det.re = A.det.re / H.det.re := by
  have hTin : Function.Injective T.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr hT
  have hTA : (Tᴴ * A * T).PosDef := hA.conjTranspose_mul_mul_same hTin
  have hTH : (Tᴴ * H * T).PosDef := hH.conjTranspose_mul_mul_same hTin
  have hdetT : T.det ≠ 0 := (hT.map Matrix.detMonoidHom).ne_zero
  have hdetH : H.det ≠ 0 := ne_of_gt hH.det_pos
  have hratio : (Tᴴ * A * T).det / (Tᴴ * H * T).det = A.det / H.det := by
    simp only [Matrix.det_mul, Matrix.det_conjTranspose]
    field_simp [hdetT, hdetH]
  have hreal {Q : Matrix (Fin n) (Fin n) ℂ} (hQ : Q.PosDef) : Q.det = (Q.det.re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using (Complex.pos_iff.mp hQ.det_pos).2.symm
  rw [hreal hTA, hreal hTH, hreal hA, hreal hH,
    ← Complex.ofReal_div, ← Complex.ofReal_div] at hratio
  exact Complex.ofReal_injective hratio

/-- The original global weight has the expected formula in every valid chart. -/
theorem immersionJacobianWeight_in_fixed_chart (g : HermitianField M)
    {F : M.Carrier → ComplexVector N} (hF : IsHolomorphicVecMap F) (hImm : IsImmersionMap F)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    immersionJacobianWeight g F (chartInv x z) =
      (immersionGram F x z).det.re / (hMat g x z).det.re := by
  have hy : chartInv x z ∈ (extChartAt (ComplexModel n) x).source :=
    (extChartAt (ComplexModel n) x).map_target hz
  have hround : chartPt x (chartInv x z) = z := (extChartAt (ComplexModel n) x).right_inv hz
  have hH := hMat_eq_centered_congruence g x (chartInv x z) hy
  rw [hround] at hH
  rw [immersionGram_eq_centered_congruence hF x hz, hH]
  exact (det_re_congruence_ratio
    (immersionGram F (chartInv x z) (chartPt (chartInv x z) (chartInv x z)))
    (gMat g (chartInv x z)) (tangentFrameMatrix x (chartInv x z) (chartInv x z))
    (immersionGram_posDef hF hImm _
      ((extChartAt (ComplexModel n) (chartInv x z)).map_source (mem_extChartAt_source _)))
    (gMat_posDef g _) (tangentFrameMatrix_isUnit x (chartInv x z) hy)).symm

theorem immersionPotential_in_fixed_chart (g : HermitianField M)
    {F : M.Carrier → ComplexVector N} (hF : IsHolomorphicVecMap F) (hImm : IsImmersionMap F)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    immersionPotential g F (chartInv x z) =
      Real.log (immersionGram F x z).det.re - Real.log (hMat g x z).det.re := by
  rw [immersionPotential, immersionJacobianWeight_in_fixed_chart g hF hImm x hz]
  exact Real.log_div
    (Complex.pos_iff.mp (immersionGram_posDef hF hImm x hz).det_pos).1.ne'
    (Complex.pos_iff.mp (hMat_posDef g x z hz).det_pos).1.ne'

/-- The actual globally defined potential is smooth; no free local potential is supplied. -/
theorem immersionPotential_smooth (g : HermitianField M) (hg : MetricSmooth g)
    {F : M.Carrier → ComplexVector N} (hF : IsHolomorphicVecMap F) (hImm : IsImmersionMap F) :
    SmoothFn (immersionPotential g F) := by
  intro x
  exact (localImmersionPotential_contDiffOn g hg hF hImm x).congr
    fun z hz => immersionPotential_in_fixed_chart g hF hImm x hz

end Yau.NodeProofs.D02Aux
