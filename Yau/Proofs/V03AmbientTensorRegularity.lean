import Yau.Proofs.V03AmbientTensorAlgebra
import Yau.Proofs.V03MetricSmooth
import Yau.Proofs.V03DifferentialTransport

/-! The genuine Gram ambient tensor has smooth entries wherever the
original immersion Gram matrix is nonsingular. -/

open scoped Topology ContDiff Matrix Manifold

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem gramLeftInverse_entry_contDiffOn {P ι κ : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [Fintype ι] [DecidableEq ι] [Fintype κ]
    {S : Set P} {A : P → Matrix κ ι ℂ}
    (hA : ∀ k i, ContDiffOn ℝ ∞ (fun p => A p k i) S)
    (hdet : ∀ p ∈ S, ((A p)ᴴ * A p).det ≠ 0) (i : ι) (k : κ) :
    ContDiffOn ℝ ∞ (fun p => gramLeftInverse (A p) i k) S := by
  have hGram (a b : ι) : ContDiffOn ℝ ∞ (fun p => ((A p)ᴴ * A p) a b) S := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    exact ContDiffOn.sum fun t _ =>
      (Complex.conjCLE.contDiff.comp_contDiffOn (hA t a)).mul (hA t b)
  have hi := entrywise_matrix_inv_contDiffOn hGram hdet
  simp only [gramLeftInverse, Matrix.mul_apply, Matrix.conjTranspose_apply]
  exact ContDiffOn.sum fun t _ =>
    (hi i t).mul (Complex.conjCLE.contDiff.comp_contDiffOn (hA k t))

theorem ambientLeviTensor_entry_contDiffOn {P ι κ : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [Fintype ι] [DecidableEq ι] [Fintype κ]
    {S : Set P} {A : P → Matrix κ ι ℂ} {H : P → Matrix ι ι ℂ}
    (hA : ∀ k i, ContDiffOn ℝ ∞ (fun p => A p k i) S)
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun p => H p i j) S)
    (hdet : ∀ p ∈ S, ((A p)ᴴ * A p).det ≠ 0) (a b : κ) :
    ContDiffOn ℝ ∞ (fun p => ambientLeviTensor (A p) (H p) a b) S := by
  have hJ := gramLeftInverse_entry_contDiffOn hA hdet
  simp only [ambientLeviTensor, Matrix.mul_apply, Matrix.conjTranspose_apply]
  exact ContDiffOn.sum fun k _ =>
    (ContDiffOn.sum fun i _ =>
      (Complex.conjCLE.contDiff.comp_contDiffOn (hJ i a)).mul (hH i k)).mul (hJ k b)

theorem cotangentDG_chart_entry_contDiffOn {n q : ℕ} {M : ComplexManifold n}
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentHolomorphic G)
    (x : M.Carrier) (a : Fin q) (b : CotangentIndex n) :
    ContDiffOn ℂ ∞ (fun z => cotangentDG G x (cotangentChartInv x z) a b)
      (cotangentTarget x) := by
  have hopen : IsOpen (cotangentTarget x) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ
  have hD := (cotangentHolomorphic_chart_contDiffOn hG x).fderiv_of_isOpen hopen
    (m := ∞) (by simp)
  have he : ContDiffOn ℂ ∞ (fun z =>
      (fderiv ℂ (fun w => G (cotangentChartInv x w)) z (cotangentDir b)) a)
      (cotangentTarget x) :=
    (contDiff_piLp_apply (p := 2) (i := a)).comp_contDiffOn (hD.clm_apply contDiffOn_const)
  apply he.congr
  intro z hz
  unfold cotangentDG
  rw [cotangentChart_right_inv x hz]

end Yau.Blueprint.V03Proof
