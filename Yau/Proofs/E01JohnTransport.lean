import Yau.Proofs.E01JohnContacts
import Yau.Proofs.E01NormalizeMax
import Yau.Proofs.E01FiberMap
import Yau.Proofs.E01ContactTransport

/-! Finite John contacts for an actual maximizer, with the whitening witness made explicit. -/

noncomputable section
open scoped Matrix ComplexOrder

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint

variable {n : ℕ}

theorem small_contacts_of_whitening
    (v : ComplexVector n → EReal) (hv : LowerSemicontinuous v)
    (hhom : ∀ r : ℝ, 0 < r → ∀ η : ComplexVector n,
      v ((r : ℂ) • η) = ((r ^ 2 : ℝ) : EReal) * v η)
    (B : Herm n) (hBv : ∀ η, (ellipsoidQuadratic B η : EReal) ≤ v η)
    (hmax : ∀ D : Herm n, D.PosDef →
      (∀ η, (ellipsoidQuadratic D η : EReal) ≤ v η) → D.det.re ≤ B.det.re)
    (S : Herm n) (hS : S.IsHermitian) (hu : IsUnit S)
    (hSS : S * S = B⁻¹) (hSBS : S * B * S = 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (m : ℕ) (η : Fin m → ComplexVector n) (α : Fin m → ℝ),
      (∀ i, 0 < α i ∧ α i ≤ ε ∧ v (η i) = 1 ∧ ellipsoidQuadratic B (η i) = 1) ∧
      (∑ i, (α i : ℂ) • contactRankOne (η i)) = B⁻¹ ∧ ∑ i, α i = n := by
  let w : ComplexVector n → EReal := fun η => v (matrixFiberMap S η)
  have hw : LowerSemicontinuous w := lowerSemicontinuous_comp_matrixFiberMap v hv S
  have hwhom : ∀ r : ℝ, 0 < r → ∀ η : ComplexVector n,
      w ((r : ℂ) • η) = ((r ^ 2 : ℝ) : EReal) * w η := by
    intro r hr η
    change v (matrixFiberMap S ((r : ℂ) • η)) = _
    rw [matrixFiberMap_complex_smul, hhom r hr]
  have hI : ∀ η, (ellipsoidQuadratic (1 : Herm n) η : EReal) ≤ w η := by
    intro η
    have hq : ellipsoidQuadratic B (matrixFiberMap S η) =
        ellipsoidQuadratic (1 : Herm n) η := by
      rw [ellipsoidQuadratic_matrixFiberMap, hS.eq, hSBS]
    simpa only [hq] using hBv (matrixFiberMap S η)
  have hm : ∀ D : Herm n, D.PosDef →
      (∀ η, (ellipsoidQuadratic D η : EReal) ≤ w η) → D.det.re ≤ 1 :=
    normalized_minorant_max v B S hu (by simpa only [hS.eq] using hSBS) hmax
  obtain ⟨m, η, α, hη, hmatrix, hsum⟩ :=
    small_unit_contacts_of_homogeneous_max w hwhom (hw.lowerSemicontinuousOn _) hI hm ε hε
  obtain ⟨ξ, hξ, hξmatrix, hξsum⟩ :=
    finite_contacts_transport v B S hS hSBS hSS η α ε hη hmatrix hsum
  exact ⟨m, ξ, α, hξ, hξmatrix, hξsum⟩

end Yau.NodeProofs.E01Aux
