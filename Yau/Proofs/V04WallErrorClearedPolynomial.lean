import Yau.Proofs.V04WallErrorPolynomial

/-! A polynomial continuation of the cleared fiber-wall error. Its
coefficients have no reciprocal cutoff factors. -/

open scoped Matrix
noncomputable section
namespace Yau.Blueprint.V04Proof.WallErrorAux
open Yau
variable {n : ℕ}

def clearedFiberPolynomial (A S B F : CotangentMatrix n) (δ ε r a : ℝ) : ℝ :=
  δ ^ 6 * ε ^ 3 * symplecticCross A (a • F) +
  r ^ 2 * δ ^ 6 * ε ^ 3 * symplecticCross S (a • F) +
  r ^ 2 * δ ^ 3 * ε ^ 3 * symplecticCross (a • B) (a • F) +
  r ^ 2 * δ ^ 6 * symplecticP (a • F)

theorem clearedFiberPolynomial_eq (A S B F : CotangentMatrix n) (δ ε r a : ℝ) :
    clearedFiberPolynomial A S (δ ^ 3 • B) (ε ^ 3 • F) δ ε r a =
      (δ * ε) ^ 6 * (symplecticCross A (a • F) +
        r ^ 2 * symplecticCross (S + a • B) (a • F) +
        r ^ 2 * symplecticP (a • F)) := by
  have hF : a • (ε ^ 3 • F) = ε ^ 3 • (a • F) := smul_comm _ _ _
  have hB : a • (δ ^ 3 • B) = δ ^ 3 • (a • B) := smul_comm _ _ _
  simp only [clearedFiberPolynomial, hF, hB, symplecticCross_smul_right,
    symplecticCross_smul_left, symplecticCross_add_left, symplecticP_smul_real]
  ring

theorem symplecticP_rescaled_difference (A S B F : CotangentMatrix n)
    {b : ℝ} (hb : b ≠ 0) (a : ℝ) :
    b⁻¹ ^ 2 * (symplecticP (b ^ 2 • A + S + a • B + a • F) -
      symplecticP (b ^ 2 • A + S + a • B)) =
      symplecticCross A (a • F) +
        b⁻¹ ^ 2 * symplecticCross (S + a • B) (a • F) +
        b⁻¹ ^ 2 * symplecticP (a • F) := by
  rw [symplecticP_add]
  simp only [symplecticCross_add_left, symplecticCross_smul_left]
  field_simp
  ring

end Yau.Blueprint.V04Proof.WallErrorAux
