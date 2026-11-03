import Yau.Proofs.Y05QuadraticSubstitution

noncomputable section

namespace Yau.Proofs.Y05Aux

open Yau MvPolynomial Yau.Proofs.Y02Aux Yau.Proofs.Y01Aux

variable {n : ℕ}

def inversePicard (A : PolyMap n) : ℕ → PolyMap n
  | 0 => PolyMap.id
  | m + 1 => PolyMap.id - (A - PolyMap.id).comp (inversePicard A m)

theorem inversePicard_fixesZero {A : PolyMap n} (hA : tangentId A) (m : ℕ) :
    (inversePicard A m).FixesZero := by
  have hid : (PolyMap.id : PolyMap n).FixesZero := by intro i; simp [PolyMap.id, coeff_X]
  have hR : (A - PolyMap.id).FixesZero := by
    intro i; simp [Pi.sub_apply, coeff_sub, hA.1 i, hid i]
  induction m with
  | zero => exact hid
  | succ m ih =>
    have hcomp := comp_fixesZero hR ih
    intro i
    simp only [inversePicard, Pi.sub_apply, coeff_sub, hid i, hcomp i, sub_self]

theorem inversePicard_difference_order {A : PolyMap n} (hA : tangentId A) (m : ℕ) :
    mapOrderAtLeast (m + 2) (inversePicard A (m + 1) - inversePicard A m) := by
  have hR : mapOrderAtLeast 2 (A - PolyMap.id) := (tangentId_iff_order A).mp hA
  induction m with
  | zero =>
    intro i
    have heq : (inversePicard A 1 - inversePicard A 0) i = -((A - PolyMap.id : PolyMap n) i) := by
      simp [inversePicard, comp_id]
    rw [heq]
    exact scalarOrderAtLeast_neg (hR i)
  | succ m ih =>
    intro i
    have H := quadratic_bind_sub_order (hR i)
      (inversePicard_fixesZero hA (m + 1)) (inversePicard_fixesZero hA m) ih
    have heq : (inversePicard A (m + 1 + 1) - inversePicard A (m + 1)) i =
        -(bind₁ (inversePicard A (m + 1)) ((A - PolyMap.id : PolyMap n) i) -
          bind₁ (inversePicard A m) ((A - PolyMap.id : PolyMap n) i)) := by
      simp only [inversePicard, Pi.sub_apply, PolyMap.comp]
      ring
    rw [heq]
    exact scalarOrderAtLeast_neg H

theorem inversePicard_right_jet {A : PolyMap n} (hA : tangentId A) (d : ℕ) :
    PolyMap.JetEq (A.comp (inversePicard A d)) PolyMap.id d := by
  apply (jetEq_iff_order _ _ _).mpr
  intro i
  have H := inversePicard_difference_order hA d i
  have heq : (A.comp (inversePicard A d) - PolyMap.id : PolyMap n) i =
      -(inversePicard A (d + 1) - inversePicard A d) i := by
    simp only [inversePicard, PolyMap.comp, Pi.sub_apply, map_sub, bind₁_X_right, PolyMap.id]
    ring
  rw [heq]
  exact scalarOrderAtLeast_mono (scalarOrderAtLeast_neg H) (by omega)

def finiteInverseJet (A : PolyMap n) (d : ℕ) : PolyMap n := truncate d (inversePicard A d)

/-- Every genuine tangent-to-identity polynomial has a two-sided finite
inverse jet. It is constructed by finitely many polynomial substitutions. -/
theorem finiteInverseJet_spec {A : PolyMap n} (hA : tangentId A) (d : ℕ) :
    (finiteInverseJet A d).degree ≤ d ∧ (finiteInverseJet A d).FixesZero ∧
      PolyMap.JetEq (A.comp (finiteInverseJet A d)) PolyMap.id d ∧
      PolyMap.JetEq ((finiteInverseJet A d).comp A) PolyMap.id d := by
  have hzero := truncate_fixesZero (d := d) (inversePicard_fixesZero hA d)
  have hright : PolyMap.JetEq (A.comp (finiteInverseJet A d)) PolyMap.id d :=
    jetEq_trans (Yau.Proofs.Y01Aux.jetEq_comp_left A (truncate_jetEq d _))
      (inversePicard_right_jet hA d)
  refine ⟨truncate_degree_le _ _, hzero, hright, ?_⟩
  have hrightA := Yau.Proofs.Y01Aux.jetEq_comp_right hright hA.1
  have heq : PolyMap.JetEq (A.comp ((finiteInverseJet A d).comp A))
      (A.comp PolyMap.id) d := by
    simpa only [comp_assoc, id_comp, comp_id] using hrightA
  exact tangentId_comp_left_cancel hA (comp_fixesZero hzero hA.1)
    (by intro i; simp [PolyMap.id, coeff_X]) heq

end Yau.Proofs.Y05Aux
