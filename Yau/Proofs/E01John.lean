import Yau.Proofs.E01JohnTransport
import Yau.Proofs.G04Whitening

/-! Finite contacts of every positive determinant maximizer, without a caller whitening premise.
This source awaits the genuine canonical G04 SOURCE consumer before compilation. -/

noncomputable section
open scoped Matrix ComplexOrder

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint

variable {n : ℕ}

theorem small_contacts_of_positive_max
    (v : ComplexVector n → EReal) (hv : LowerSemicontinuous v)
    (hhom : ∀ r : ℝ, 0 < r → ∀ η : ComplexVector n,
      v ((r : ℂ) • η) = ((r ^ 2 : ℝ) : EReal) * v η)
    (B : Herm n) (hB : B.PosDef)
    (hBv : ∀ η, (ellipsoidQuadratic B η : EReal) ≤ v η)
    (hmax : ∀ D : Herm n, D.PosDef →
      (∀ η, (ellipsoidQuadratic D η : EReal) ≤ v η) → D.det.re ≤ B.det.re)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (m : ℕ) (η : Fin m → ComplexVector n) (α : Fin m → ℝ),
      (∀ i, 0 < α i ∧ α i ≤ ε ∧ v (η i) = 1 ∧ ellipsoidQuadratic B (η i) = 1) ∧
      (∑ i, (α i : ℂ) • contactRankOne (η i)) = B⁻¹ ∧ ∑ i, α i = n := by
  obtain ⟨S, hS, hu, hSS, hSBS⟩ := G04Aux.exists_hermitian_whitening B hB
  exact small_contacts_of_whitening v hv hhom B hBv hmax S hS hu hSS hSBS ε hε

end Yau.NodeProofs.E01Aux
