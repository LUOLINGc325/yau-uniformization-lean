import Yau.Proofs.E01OptimizerExistence
import Yau.Proofs.E01ValueLsc

/-! The supremum used by the original contract is an attained, lower semicontinuous log value. -/

noncomputable section
open scoped Matrix ComplexOrder Topology

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint

variable {n : ℕ}

theorem logdet_minorant_le_of_max
    (v : ComplexVector n → EReal) (A : Herm n) (hA : A.PosDef)
    (hmax : ∀ D : Herm n, D.PosDef →
      (∀ η, (ellipsoidQuadratic D η : EReal) ≤ v η) → D.det.re ≤ A.det.re)
    (D : Herm n) (hD : D.PosDef)
    (hDv : ∀ η, (ellipsoidQuadratic D η : EReal) ≤ v η) :
    Real.log D.det.re ≤ Real.log A.det.re :=
  Real.log_le_log (Complex.pos_iff.mp hD.det_pos).1 (hmax D hD hDv)

theorem lowerSemicontinuous_log_sup_minorant_determinants
    {P : Type*} [TopologicalSpace P]
    (v : P × ComplexVector n → EReal) (hv : LowerSemicontinuous v)
    (hhom : ∀ p (r : ℝ), 0 < r → ∀ η : ComplexVector n,
      v (p, (r : ℂ) • η) = ((r ^ 2 : ℝ) : EReal) * v (p, η))
    (hclip : ∀ p, ∃ C B₀ : Herm n, C.IsHermitian ∧ B₀.PosDef ∧
      (∀ η, v (p, η) ≤ (ellipsoidQuadratic C η : EReal)) ∧
      (∀ η, (ellipsoidQuadratic B₀ η : EReal) ≤ v (p, η))) :
    LowerSemicontinuous (fun p => Real.log
      (sSup {d : ℝ | ∃ D : Herm n, D.PosDef ∧
        (∀ η, (ellipsoidQuadratic D η : EReal) ≤ v (p, η)) ∧ d = D.det.re})) := by
  let L : P → ℝ := fun p => Real.log
    (sSup {d : ℝ | ∃ D : Herm n, D.PosDef ∧
      (∀ η, (ellipsoidQuadratic D η : EReal) ≤ v (p, η)) ∧ d = D.det.re})
  have hmax : ∀ p, ∃ B : Herm n, B.PosDef ∧
      (∀ η, (ellipsoidQuadratic B η : EReal) ≤ v (p, η)) ∧
      (∀ D : Herm n, D.PosDef →
        (∀ η, (ellipsoidQuadratic D η : EReal) ≤ v (p, η)) → D.det.re ≤ B.det.re) := by
    intro p
    obtain ⟨C, B₀, hC, hB₀, hup, hlow⟩ := hclip p
    obtain ⟨B, hB, hBv, hm⟩ := exists_positive_minorant_determinant_max
      (fun η => v (p, η)) C B₀ hC hB₀ hup hlow
    exact ⟨B, hB, hBv, fun D hD hDv => hm D hD.posSemidef hDv⟩
  have hzero : ∀ p, (0 : EReal) ≤ v (p, 0) := by
    intro p
    obtain ⟨B, _, hBv, _⟩ := hmax p
    simpa only [ellipsoidQuadratic_zero_vector, EReal.coe_zero] using hBv 0
  apply lowerSemicontinuous_log_value_of_maximizers v hv hzero hhom L
  · intro p
    obtain ⟨B, hB, hBv, hm⟩ := hmax p
    refine ⟨B, hB, hBv, ?_⟩
    exact congrArg Real.log (sSup_minorant_determinants_eq_max
      (fun η => v (p, η)) B hB hBv hm)
  · intro p D hD hDv
    obtain ⟨B, hB, hBv, hm⟩ := hmax p
    have hL : L p = Real.log B.det.re := congrArg Real.log
      (sSup_minorant_determinants_eq_max (fun η => v (p, η)) B hB hBv hm)
    rw [hL]
    exact logdet_minorant_le_of_max (fun η => v (p, η)) B hB hm D hD hDv

end Yau.NodeProofs.E01Aux
