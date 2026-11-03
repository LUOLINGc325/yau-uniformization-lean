import Yau.Proofs.V04WallErrorPullback
import Yau.Proofs.V04WallErrorPolynomial
import Yau.Proofs.V03WirtingerDirections

/-! Exact degree two of `p` under real fiber dilation. -/

open scoped Topology ContDiff Matrix
noncomputable section
namespace Yau.Blueprint.V04Proof.WallErrorAux
open Yau Yau.Blueprint V03Proof
variable {n : ℕ}

def fiberDilation (c : ℝ) : CotangentCoord n →L[ℂ] CotangentCoord n :=
  (ContinuousLinearMap.fst ℂ (ComplexVector n) (ComplexVector n)).prod
    ((c : ℂ) • ContinuousLinearMap.snd ℂ (ComplexVector n) (ComplexVector n))

theorem fiberDilation_apply (c : ℝ) (z : CotangentCoord n) :
    fiberDilation c z = (z.1, (c : ℂ) • z.2) := rfl

theorem fiberDilation_inl (c : ℝ) (i : Fin n) :
    fiberDilation c (cotangentDir (Sum.inl i)) = cotangentDir (Sum.inl i) := by
  simp [fiberDilation_apply, cotangentDir]

theorem fiberDilation_inr (c : ℝ) (i : Fin n) :
    fiberDilation c (cotangentDir (Sum.inr i)) = (c : ℂ) • cotangentDir (Sum.inr i) := by
  simp [fiberDilation_apply, cotangentDir, Prod.smul_mk]

def fiberDilatedMatrix (c : ℝ) (W : CotangentMatrix n) : CotangentMatrix n :=
  Matrix.fromBlocks W.toBlocks₁₁ (c • W.toBlocks₁₂) (c • W.toBlocks₂₁) (c ^ 2 • W.toBlocks₂₂)

theorem leviMatrix_fiberDilation {f : CotangentCoord n → ℝ} {p : CotangentCoord n}
    (c : ℝ) (hf : ContDiffAt ℝ 2 f (fiberDilation c p)) :
    leviMatrix (fun z => f (fiberDilation c z)) p cotangentDir =
      fiberDilatedMatrix c (leviMatrix f (fiberDilation c p) cotangentDir) := by
  rw [leviMatrix_comp_clm (fiberDilation c) hf cotangentDir]
  have hF : ContDiffAt ℝ 2 (fun u => (f u : ℂ)) (fiberDilation c p) :=
    hf.continuousLinearMap_comp Complex.ofRealCLM
  ext (i | i) (j | j)
  · simp only [leviMatrix, fiberDilation_inl, fiberDilatedMatrix, Matrix.fromBlocks_apply₁₁,
      Matrix.toBlocks₁₁, Matrix.of_apply]
  · simp only [leviMatrix, fiberDilation_inl, fiberDilation_inr,
      wirt_smul_direction, fiberDilatedMatrix, Matrix.fromBlocks_apply₁₂,
      Matrix.smul_apply, Matrix.toBlocks₁₂, Matrix.of_apply, Complex.real_smul]
  · simp only [leviMatrix, fiberDilation_inl, fiberDilation_inr,
      mixedWirt_smul_left hF, fiberDilatedMatrix, Matrix.fromBlocks_apply₂₁,
      Matrix.smul_apply, Matrix.toBlocks₂₁, Matrix.of_apply, Complex.real_smul, Complex.star_def, Complex.conj_ofReal]
  · simp only [leviMatrix, fiberDilation_inr, wirt_smul_direction,
      mixedWirt_smul_left hF, fiberDilatedMatrix, Matrix.fromBlocks_apply₂₂,
      Matrix.smul_apply, Matrix.toBlocks₂₂, Matrix.of_apply, Complex.real_smul, Complex.star_def, Complex.conj_ofReal,
      Complex.ofReal_pow, pow_two]
    push_cast
    ring

theorem symplecticP_fiberDilatedMatrix (c : ℝ) (W : CotangentMatrix n) :
    symplecticP (fiberDilatedMatrix c W) = c ^ 2 * symplecticP W := by
  simp only [symplecticP, fiberDilatedMatrix, Matrix.toBlocks_fromBlocks₁₁,
    Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₂,
    Matrix.transpose_smul, Matrix.mul_smul, Matrix.trace_smul,
    Matrix.smul_apply, star_smul, star_trivial, smul_mul_assoc, mul_smul_comm,
    smul_smul, ← Finset.smul_sum, ← smul_sub, pow_two]
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

theorem symplecticP_leviMatrix_fiberDilation {f : CotangentCoord n → ℝ} {p : CotangentCoord n}
    (c : ℝ) (hf : ContDiffAt ℝ 2 f (fiberDilation c p)) :
    symplecticP (leviMatrix (fun z => f (fiberDilation c z)) p cotangentDir) =
      c ^ 2 * symplecticP (leviMatrix f (fiberDilation c p) cotangentDir) := by
  rw [leviMatrix_fiberDilation c hf, symplecticP_fiberDilatedMatrix]

end Yau.Blueprint.V04Proof.WallErrorAux
