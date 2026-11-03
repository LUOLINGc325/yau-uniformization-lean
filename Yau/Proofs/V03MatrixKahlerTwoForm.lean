import Yau.Proofs.V03BilinearTwoForm
import Yau.Proofs.V03LeviChain
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-! The actual Hermitian matrix defines the genuine real Kähler two-form
with the paper factor two, smoothly in all of its entries. -/

open scoped Topology ContDiff Matrix

noncomputable section
namespace Yau.Blueprint.V03Proof

def complexPairBilinear {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : E →L[ℝ] ℂ) : E →L[ℝ] E →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ E ℂ ℝ) Complex.imCLM).comp
    (((ContinuousLinearMap.compL ℝ E ℂ ℂ).flip b).comp ((ContinuousLinearMap.mul ℝ ℂ).comp a))

theorem complexPairBilinear_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : E →L[ℝ] ℂ) (u v : E) : complexPairBilinear a b u v = (a u * b v).im := by
  rfl

theorem complexPairBilinear_contDiffOn {P E : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {U : Set P} (a : E →L[ℝ] ℂ) {b : P → E →L[ℝ] ℂ} (hb : ContDiffOn ℝ ∞ b U) :
    ContDiffOn ℝ ∞ (fun p => complexPairBilinear a (b p)) U := by
  apply contDiffOn_clm_apply.mpr
  intro u
  apply contDiffOn_clm_apply.mpr
  intro v
  simp only [complexPairBilinear_apply]
  exact Complex.imCLM.contDiff.comp_contDiffOn (contDiffOn_const.mul (hb.clm_apply contDiffOn_const))

variable {ι : Type*} [Fintype ι]

def euclideanCoordinateReal (i : ι) : EuclideanSpace ℂ ι →L[ℝ] ℂ :=
  (PiLp.proj (𝕜 := ℂ) 2 (fun _ : ι => ℂ) i).restrictScalars ℝ

theorem euclideanCoordinateReal_apply (i : ι) (u : EuclideanSpace ℂ ι) :
    euclideanCoordinateReal i u = u i := rfl

def matrixKahlerBilinear (H : Matrix ι ι ℂ) :
    EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι →L[ℝ] ℝ :=
  (2 : ℝ) • ∑ bc : ι × ι, complexPairBilinear
    (Complex.conjCLE.toContinuousLinearMap.comp (euclideanCoordinateReal bc.1))
    (H bc.1 bc.2 • euclideanCoordinateReal bc.2)

theorem matrixKahlerBilinear_apply (H : Matrix ι ι ℂ) (u v : EuclideanSpace ℂ ι) :
    matrixKahlerBilinear H u v = 2 * (star (fun i => u i) ⬝ᵥ (H *ᵥ fun i => v i)).im := by
  simp only [matrixKahlerBilinear, smul_apply, ContinuousLinearMap.sum_apply, smul_eq_mul,
    complexPairBilinear_apply, ContinuousLinearMap.comp_apply, euclideanCoordinateReal_apply]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Fintype.sum_prod_type, Pi.star_apply,
    Complex.im_sum, Complex.star_def]
  congr 1

def matrixKahlerTwoForm (H : Matrix ι ι ℂ) : EuclideanSpace ℂ ι [⋀^Fin 2]→L[ℝ] ℝ :=
  bilinearTwoForm (matrixKahlerBilinear H)

theorem matrixKahlerTwoForm_apply {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (u v : EuclideanSpace ℂ ι) :
    matrixKahlerTwoForm H ![u, v] = 2 * (star (fun i => u i) ⬝ᵥ (H *ᵥ fun i => v i)).im := by
  rw [matrixKahlerTwoForm, bilinearTwoForm_apply, matrixKahlerBilinear_apply, matrixKahlerBilinear_apply,
    ← hH.star_dotProduct_mulVec_comm (fun i => u i) (fun i => v i)]
  simp only [Complex.star_def, Complex.conj_im]
  ring

theorem matrixKahlerBilinear_contDiffOn {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {U : Set P} {H : P → Matrix ι ι ℂ}
    (hH : ∀ b c, ContDiffOn ℝ ∞ (fun p => H p b c) U) :
    ContDiffOn ℝ ∞ (fun p => matrixKahlerBilinear (H p)) U := by
  apply contDiffOn_clm_apply.mpr
  intro u
  apply contDiffOn_clm_apply.mpr
  intro v
  simp only [matrixKahlerBilinear_apply]
  have hs : ContDiffOn ℝ ∞ (fun p => star (fun i => u i) ⬝ᵥ (H p *ᵥ fun i => v i)) U :=
    ContDiffOn.sum (fun b _ => contDiffOn_const.mul
      (ContDiffOn.sum (fun c _ => (hH b c).mul contDiffOn_const)))
  exact contDiffOn_const.mul (Complex.imCLM.contDiff.comp_contDiffOn hs)

theorem matrixKahlerTwoForm_contDiffOn {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {U : Set P} {H : P → Matrix ι ι ℂ}
    (hH : ∀ b c, ContDiffOn ℝ ∞ (fun p => H p b c) U) :
    ContDiffOn ℝ ∞ (fun p => matrixKahlerTwoForm (H p)) U :=
  bilinearTwoForm_contDiffOn (matrixKahlerBilinear_contDiffOn hH)

end Yau.Blueprint.V03Proof
