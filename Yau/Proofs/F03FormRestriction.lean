import Yau.Proofs.F03ScalarL2

/-! Restriction of the actual prequotient one-form L² condition. -/

noncomputable section
open MeasureTheory

namespace Yau.Proofs.F03Aux
open Yau

variable {n k : ℕ} {M : ComplexManifold n}

theorem l2RealForm_mono_measure (g : HermitianField M)
    {μ ν : Measure M.Carrier} (hνμ : ν ≤ μ) {A : RealForm M k}
    (hA : L2RealForm g μ A) : L2RealForm g ν A := by
  refine ⟨fun x I => (hA.1 x I).mono_measure (Measure.restrict_mono_measure hνμ _), ?_⟩
  exact (lintegral_mono' hνμ (fun _ => le_rfl)).trans_lt hA.2

theorem l2RealForm_restrict (g : HermitianField M)
    (μ : Measure M.Carrier) (O : Set M.Carrier) {A : RealForm M k}
    (hA : L2RealForm g μ A) : L2RealForm g (μ.restrict O) A :=
  l2RealForm_mono_measure g Measure.restrict_le_self hA

end Yau.Proofs.F03Aux
