import Yau.Proofs.G01RawAlgebra
import Yau.LeafProofs.L05ComplexRepresentation
import Yau.Proofs.F01ZeroExtensionSpaceJets
import Yau.Proofs.F01ClosedTimeSlices

/-! The transformed real Hessian of the actual zero-extended potential
is exactly the realification of its complex metric matrix. No bound for the
full real Hessian and no independent transformed field are assumed. -/
noncomputable section
open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem iota_add (A B : Matrix (Fin n) (Fin n) ℂ) : iota (A + B) = iota A + iota B := by
  change selfAdjointPart ℝ (G01Aux.rawReal (A + B)) = _
  rw [G01Aux.rawReal_add, map_add]
  rfl

theorem iota_sub (A B : Matrix (Fin n) (Fin n) ℂ) : iota (A - B) = iota A - iota B := by
  change selfAdjointPart ℝ (G01Aux.rawReal (A - B)) = _
  rw [G01Aux.rawReal_sub, map_sub]
  rfl

theorem iota_real_smul (c : ℝ) (A : Matrix (Fin n) (Fin n) ℂ) :
    iota ((c : ℂ) • A) = c • iota A := by
  change selfAdjointPart ℝ (G01Aux.rawReal ((c : ℂ) • A)) = _
  rw [G01Aux.rawReal_real_smul, map_smul]
  rfl

theorem complexHessianMap_spaceTime {F : Point n → ℝ} {z : Space n} {t : ℝ}
    (hF : ContDiffAt ℝ 2 (fun w => F (w, t)) z) :
    complexHessianMap (hessian F (z, t)) = iota (leviC (fun w => F (w, t)) z) :=
  Yau.LeafProofs.L05Aux.complexHessianRepresentation n (fun w => F (w, t)) z hF

theorem clamped_transformed_matrix_identity
    (A : Space n → Matrix (Fin n) (Fin n) ℂ) {F : Point n → ℝ}
    {S : Set (Space n)} {T : ℝ} (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ F (S ×ˢ Icc 0 T))
    {p : Point n} (hp : p.1 ∈ S) (ht : p.2 ≤ T) :
    clampedBackground A p + complexHessianMap (hessian (forwardZeroSpaceTime F) p) =
      if p.2 ≤ 0 then iota (A p.1) else
        iota (A p.1 - (p.2 : ℂ) • backgroundRicci A p.1 +
          leviC (fun w => F (w, p.2)) p.1) := by
  have hdd := congrFun (spatialDD_forwardZeroSpaceTime F) p
  by_cases hnonpos : p.2 ≤ 0
  · rw [if_pos hnonpos]
    simp only [forwardZeroSpaceTime, forwardZeroExtension, if_pos hnonpos] at hdd
    have hhess : hessian (forwardZeroSpaceTime F) p = 0 := by
      simp only [hessian, hdd, ContinuousLinearMap.zero_apply, sym]
      change selfAdjointPart ℝ (0 : Mat n) = 0
      exact map_zero _
    rw [hhess]
    simp [clampedBackground, max_eq_right hnonpos, complexHessianMap, sym]
  · rw [if_neg hnonpos]
    simp only [forwardZeroSpaceTime, forwardZeroExtension, if_neg hnonpos] at hdd
    have hhess : hessian (forwardZeroSpaceTime F) p = hessian F p := by
      unfold hessian
      rw [hdd]
    rw [hhess, complexHessianMap_spaceTime
      ((closed_slab_slice_jets hF hS hp ⟨le_of_not_ge hnonpos, ht⟩).1)]
    unfold clampedBackground
    rw [max_eq_left (le_of_not_ge hnonpos), iota_add]

end Yau.NodeProofs.F01Aux
