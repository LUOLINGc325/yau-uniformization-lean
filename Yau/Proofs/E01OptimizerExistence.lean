import Yau.Proofs.E01FeasibleCompact

/-! Existence of a genuine positive determinant maximizer, in every dimension. -/

noncomputable section
open scoped Matrix ComplexOrder

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint

variable {n : ℕ}

theorem exists_positive_minorant_determinant_max
    (v : ComplexVector n → EReal) (C B₀ : Herm n)
    (hC : C.IsHermitian) (hB₀ : B₀.PosDef)
    (hupper : ∀ η, v η ≤ (ellipsoidQuadratic C η : EReal))
    (hlower : ∀ η, (ellipsoidQuadratic B₀ η : EReal) ≤ v η) :
    ∃ B : Herm n, B.PosDef ∧
      (∀ η, (ellipsoidQuadratic B η : EReal) ≤ v η) ∧
      ∀ D : Herm n, D.PosSemidef →
        (∀ η, (ellipsoidQuadratic D η : EReal) ≤ v η) → D.det.re ≤ B.det.re := by
  let K : Set (Herm n) := {A | A.PosSemidef ∧ ∀ η,
    (ellipsoidQuadratic A η : EReal) ≤ v η}
  have hK : IsCompact K := isCompact_psd_minorants_of_upper v C hC hupper
  have hB₀K : B₀ ∈ K := ⟨hB₀.posSemidef, hlower⟩
  have hdet : Continuous (fun A : Herm n => A.det.re) := by fun_prop
  obtain ⟨B, hBK, hmax⟩ := hK.exists_isMaxOn ⟨B₀, hB₀K⟩ hdet.continuousOn
  have hdetB : 0 < B.det.re :=
    (Complex.pos_iff.mp hB₀.det_pos).1.trans_le (hmax hB₀K)
  have hB : B.PosDef := hBK.1.posDef_iff_det_ne_zero.mpr (by
    intro hz
    exact (ne_of_gt hdetB) (congrArg Complex.re hz))
  exact ⟨B, hB, hBK.2, fun D hD hDv => hmax ⟨hD, hDv⟩⟩

theorem sSup_minorant_determinants_eq_max
    (v : ComplexVector n → EReal) (B : Herm n) (hB : B.PosDef)
    (hBv : ∀ η, (ellipsoidQuadratic B η : EReal) ≤ v η)
    (hmax : ∀ D : Herm n, D.PosDef →
      (∀ η, (ellipsoidQuadratic D η : EReal) ≤ v η) → D.det.re ≤ B.det.re) :
    sSup {d : ℝ | ∃ D : Herm n, D.PosDef ∧
      (∀ η, (ellipsoidQuadratic D η : EReal) ≤ v η) ∧ d = D.det.re} = B.det.re := by
  let S : Set ℝ := {d | ∃ D : Herm n, D.PosDef ∧
    (∀ η, (ellipsoidQuadratic D η : EReal) ≤ v η) ∧ d = D.det.re}
  have hmem : B.det.re ∈ S := ⟨B, hB, hBv, rfl⟩
  have hbound : ∀ d ∈ S, d ≤ B.det.re := by
    rintro d ⟨D, hD, hDv, rfl⟩
    exact hmax D hD hDv
  exact le_antisymm (csSup_le ⟨B.det.re, hmem⟩ hbound)
    (le_csSup ⟨B.det.re, hbound⟩ hmem)

end Yau.NodeProofs.E01Aux
