import Yau.Proofs.E01MaximizerTrace
import Yau.Proofs.E01OptimizerExistence
import Yau.Proofs.E01CometricDet
import Yau.Proofs.E02LogdetSupport

/-! Uniqueness uses the canonical shared trace-logdet equality theorem.
This source awaits the genuine own-prefix E02 SOURCE consumer before compilation. -/

noncomputable section
open scoped Matrix ComplexOrder

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint

variable {n : ℕ}

theorem positive_minorant_max_unique
    (v : ComplexVector n → EReal) (A : Herm n) (hA : A.PosDef)
    (hAv : ∀ η, (ellipsoidQuadratic A η : EReal) ≤ v η)
    (hmaxA : ∀ D : Herm n, D.PosDef →
      (∀ η, (ellipsoidQuadratic D η : EReal) ≤ v η) → D.det.re ≤ A.det.re)
    (B : Herm n) (hB : B.PosDef)
    (hBv : ∀ η, (ellipsoidQuadratic B η : EReal) ≤ v η)
    (hmaxB : ∀ D : Herm n, D.PosDef →
      (∀ η, (ellipsoidQuadratic D η : EReal) ≤ v η) → D.det.re ≤ B.det.re) :
    B = A := by
  have hdet : B.det.re = A.det.re := le_antisymm (hmaxA B hB hBv) (hmaxB A hA hAv)
  have htr : (Matrix.trace (A⁻¹ * B)).re ≤ n :=
    trace_inv_mul_le_dim_of_minorant_max v A hA hAv hmaxA B hB hBv
  have hlo := E02Aux.trace_logdet_support B A⁻¹ hB hA.inv
  have hval : (n : ℝ) + Real.log B.det.re + Real.log (A⁻¹).det.re = n := by
    rw [hdet, logdet_inverse_posDef A hA]
    ring
  have heq : (n : ℝ) + Real.log B.det.re + Real.log (A⁻¹).det.re =
      (Matrix.trace (A⁻¹ * B)).re := by linarith
  have hBA := (E02Aux.trace_logdet_support_eq_iff B A⁻¹ hB hA.inv).mp heq
  exact hBA.trans (Matrix.nonsing_inv_nonsing_inv _ (hA.isUnit.map Matrix.detMonoidHom))

theorem existsUnique_positive_minorant_determinant_max
    (v : ComplexVector n → EReal) (C B₀ : Herm n)
    (hC : C.IsHermitian) (hB₀ : B₀.PosDef)
    (hupper : ∀ η, v η ≤ (ellipsoidQuadratic C η : EReal))
    (hlower : ∀ η, (ellipsoidQuadratic B₀ η : EReal) ≤ v η) :
    ∃! B : Herm n, B.PosDef ∧
      (∀ η, (ellipsoidQuadratic B η : EReal) ≤ v η) ∧
      ∀ D : Herm n, D.PosDef →
        (∀ η, (ellipsoidQuadratic D η : EReal) ≤ v η) → D.det.re ≤ B.det.re := by
  obtain ⟨B, hB, hBv, hm⟩ := exists_positive_minorant_determinant_max v C B₀ hC hB₀ hupper hlower
  have hmax : ∀ D : Herm n, D.PosDef →
      (∀ η, (ellipsoidQuadratic D η : EReal) ≤ v η) → D.det.re ≤ B.det.re :=
    fun D hD hDv => hm D hD.posSemidef hDv
  exact ⟨B, ⟨hB, hBv, hmax⟩, fun D hD =>
    positive_minorant_max_unique v B hB hBv hmax D hD.1 hD.2.1 hD.2.2⟩

end Yau.NodeProofs.E01Aux
