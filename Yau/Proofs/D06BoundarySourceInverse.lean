import Yau.Proofs.D06HardyRelativeMean
import Yau.Proofs.D06MeasurableEnergy

/-! The source inverse is the original P P* on the boundary, with the exact
spectral bound m⁻¹ and actual bounded measurable entries. -/

open scoped ComplexOrder Matrix Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

open Yau.Blueprint
variable {r : ℕ}
variable (L : HardyCircle → Matrix (Fin r) (Fin r) ℂ)
variable (hLp : ∀ i j, MemLp (fun t => L t i j) ⊤ hardyCircleMeasure)
variable (hHerm : ∀ t, (L t).IsHermitian)
variable (m : ℝ) (hm : 0 < m)
variable (hLower : ∀ t, (L t - (m : ℂ) • 1).PosSemidef)
variable (M : ℝ) (hM : 0 ≤ M)
variable (hUpper : ∀ t, ((M : ℂ) • 1 - L t).PosSemidef)

def hardySourceInverse (t : HardyCircle) : Matrix (Fin r) (Fin r) ℂ :=
  hardyPTrace L hLp hHerm m hm hLower M hM hUpper t *
    (hardyPTrace L hLp hHerm m hm hLower M hM hUpper t)ᴴ

theorem hardySourceInverse_memLp (i j : Fin r) :
    MemLp (fun t => hardySourceInverse L hLp hHerm m hm hLower M hM hUpper t i j)
      ⊤ hardyCircleMeasure := by
  apply matrix_entries_memLp_mul
  · exact hardyPTrace_memLp L hLp hHerm m hm hLower M hM hUpper
  · intro i j
    exact (hardyPTrace_memLp L hLp hHerm m hm hLower M hM hUpper j i).star

theorem hardySourceInverse_bound : ∀ᵐ t ∂hardyCircleMeasure,
    matOpNormR (hardySourceInverse L hLp hHerm m hm hLower M hM hUpper t) ≤ m⁻¹ := by
  filter_upwards [hardyPTrace_bound L hLp hHerm m hm hLower M hM hUpper] with t ht
  let P := hardyPTrace L hLp hHerm m hm hLower M hM hUpper t
  change ‖P * Pᴴ‖ ≤ m⁻¹
  have hp : ‖P‖ ≤ (Real.sqrt m)⁻¹ := ht
  calc
    _ ≤ ‖P‖ * ‖Pᴴ‖ := norm_mul_le _ _
    _ = ‖P‖ ^ 2 := by rw [Matrix.l2_opNorm_conjTranspose, pow_two]
    _ ≤ ((Real.sqrt m)⁻¹) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (inv_nonneg.mpr (Real.sqrt_nonneg _))).mpr hp
    _ = m⁻¹ := by rw [inv_pow, Real.sq_sqrt hm.le]

theorem hardySourceInverse_inverse : ∀ᵐ t ∂hardyCircleMeasure,
    L t * hardySourceInverse L hLp hHerm m hm hLower M hM hUpper t = 1 ∧
      hardySourceInverse L hLp hHerm m hm hLower M hM hUpper t * L t = 1 := by
  filter_upwards [hardyPTrace_inverse L hLp hHerm m hm hLower M hM hUpper,
    hardyQTrace_factor L hLp hHerm m hm hLower M hM hUpper] with t hi hf
  let P := hardyPTrace L hLp hHerm m hm hLower M hM hUpper t
  let Q := hardyQTrace L hLp hHerm m hm hLower M hM hUpper t
  have hPQ : P * Q = 1 := hi.1
  have hQP : Q * P = 1 := hi.2
  change L t * (P * Pᴴ) = 1 ∧ (P * Pᴴ) * L t = 1
  rw [hf]
  change (Qᴴ * Q) * (P * Pᴴ) = 1 ∧ (P * Pᴴ) * (Qᴴ * Q) = 1
  constructor
  · calc
      _ = Qᴴ * ((Q * P) * Pᴴ) := by simp only [Matrix.mul_assoc]
      _ = Qᴴ * Pᴴ := by rw [hQP, one_mul]
      _ = (P * Q)ᴴ := (Matrix.conjTranspose_mul P Q).symm
      _ = 1 := by rw [hPQ, Matrix.conjTranspose_one]
  · calc
      _ = P * ((Pᴴ * Qᴴ) * Q) := by simp only [Matrix.mul_assoc]
      _ = P * Q := by rw [← Matrix.conjTranspose_mul, hQP, Matrix.conjTranspose_one, one_mul]
      _ = 1 := hPQ

end Yau.NodeProofs.D06Aux
