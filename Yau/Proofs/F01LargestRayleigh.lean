import Yau.Proofs.F01RayleighOrder
import Yau.Proofs.F01RelativeMetricOrder

/-! The largest relative eigenvalue is the supremum of the actual quadratic
quotients. Its finiteness follows from positivity in finite dimension. -/
noncomputable section
open Set
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def largestMatrixRayleigh (H K : Matrix ι ι ℂ) : ℝ :=
  sSup (range (matrixRayleigh H K))

theorem matrixRayleigh_range_bddAbove {H K : Matrix ι ι ℂ}
    (hH : H.PosDef) (hK : K.PosDef) : BddAbove (range (matrixRayleigh H K)) := by
  obtain ⟨C, hC, horder⟩ := exists_relative_metric_upper_order hH hK
  exact ⟨C, by rintro _ ⟨v, rfl⟩; exact matrixRayleigh_le_of_posSemidef hH hC.le horder v⟩

theorem matrixRayleigh_le_largest {H K : Matrix ι ι ℂ}
    (hH : H.PosDef) (hK : K.PosDef) (v : ι → ℂ) :
    matrixRayleigh H K v ≤ largestMatrixRayleigh H K :=
  le_csSup (matrixRayleigh_range_bddAbove hH hK) (mem_range_self v)

theorem largestMatrixRayleigh_nonneg {H K : Matrix ι ι ℂ}
    (hH : H.PosDef) (hK : K.PosDef) : 0 ≤ largestMatrixRayleigh H K := by
  have hh := matrixRayleigh_le_largest hH hK (0 : ι → ℂ)
  simpa [matrixRayleigh, matrixQuadraticValue] using hh

theorem largestMatrixRayleigh_le_of_order {H K : Matrix ι ι ℂ}
    (hH : H.PosDef) {C : ℝ} (hC : 0 ≤ C)
    (horder : ((C : ℂ) • H - K).PosSemidef) :
    largestMatrixRayleigh H K ≤ C := by
  apply csSup_le (range_nonempty _)
  rintro _ ⟨v, rfl⟩
  exact matrixRayleigh_le_of_posSemidef hH hC horder v

theorem largestMatrixRayleigh_congruence (A H K : Matrix ι ι ℂ)
    (hA : IsUnit A) : largestMatrixRayleigh (Aᴴ * H * A) (Aᴴ * K * A) =
      largestMatrixRayleigh H K := by
  have hsurj : Function.Surjective (fun v => A *ᵥ v) := by
    intro v
    refine ⟨(↑hA.unit⁻¹ : Matrix ι ι ℂ) *ᵥ v, ?_⟩
    change A *ᵥ ((↑hA.unit⁻¹ : Matrix ι ι ℂ) *ᵥ v) = v
    have hmul : A * (↑hA.unit⁻¹ : Matrix ι ι ℂ) = 1 := by
      calc
        A * (↑hA.unit⁻¹ : Matrix ι ι ℂ) = ↑hA.unit * ↑hA.unit⁻¹ :=
          congrArg (fun B : Matrix ι ι ℂ => B * ↑hA.unit⁻¹) hA.unit_spec.symm
        _ = 1 := hA.unit.val_inv
    rw [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]
  exact congrArg sSup (matrixRayleigh_range_congruence A H K hsurj)

end Yau.NodeProofs.F01Aux
