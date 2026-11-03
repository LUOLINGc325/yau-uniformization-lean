import Yau.Proofs.Y01ChangeBounds
import Yau.Proofs.Y01PolynomialComposition

/-! The primary coordinate derivative and the regular jump come from the
same chosen aligned changes. -/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Yau.Proofs.Y01Aux

open Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux MvPolynomial

variable {n : ℕ}

theorem unitary_isUnit {U : Herm n} (hU : Unitary U) : IsUnit U :=
  ⟨⟨U, U.conjTranspose, hU.2, hU.1⟩, rfl⟩

theorem unitary_conjTranspose {U : Herm n} (hU : Unitary U) : Unitary U.conjTranspose := by
  simpa only [Unitary, Matrix.conjTranspose_conjTranspose] using And.intro hU.2 hU.1

theorem primaryDerivative_isUnit
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk : ℕ → ℝ} {E : Frames n}
    (hE : SingularFrames F tk E) {reg : ℕ → Prop} {w : ℕ → Fin n → ℝ}
    {J : ℕ → ℕ} {S : ℕ → ℝ} {C c : ℝ} {L : Changes n}
    (hL : ∀ k, reg k → ChangeAt (diagonal F tk E) w J S C c L k) (k : ℕ) :
    IsUnit (primaryDerivative reg E L k) := by
  classical
  unfold primaryDerivative
  split_ifs with hk hprev
  · exact (minus_change_isUnit hE (hL k hk)).mul
      (unitary_isUnit (unitary_conjTranspose (hE k).2.2.1))
  · exact (plus_change_isUnit (hL (k - 1) hprev.2)).mul
      (unitary_isUnit (unitary_conjTranspose (hE (k - 1)).2.2.2.1))
  · exact isUnit_one

theorem primary_next_factor
    {E : Frames n} {L : Changes n} {reg : ℕ → Prop} {k : ℕ}
    (hk : reg k) (hfinish : Unitary (E.finish k)) (hplus : IsUnit (L.plus k)) :
    primaryDerivative reg E L (k + 1) =
      (if reg (k + 1) then alignedJump E L k else 1) *
        (L.plus k * (E.finish k).conjTranspose) := by
  classical
  by_cases hk' : reg (k + 1)
  · simp only [primaryDerivative, hk', ite_true, alignedJump, jump]
    have hinv : (L.plus k)⁻¹ * L.plus k = 1 :=
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hplus)
    calc
      L.minus (k + 1) * (E.start (k + 1)).conjTranspose =
          L.minus (k + 1) * (E.start (k + 1)).conjTranspose *
            (E.finish k * ((L.plus k)⁻¹ * L.plus k) * (E.finish k).conjTranspose) := by
              rw [hinv, Matrix.mul_one, hfinish.2, Matrix.mul_one]
      _ = _ := by noncomm_ring
  · simp only [primaryDerivative, hk', ite_false, Nat.succ_pos, Nat.add_sub_cancel,
      hk, and_self, ite_true, Matrix.one_mul]

theorem linearPolynomial_eq_linearPoly (A : Herm n) : linearPolynomial A = linearPoly A := rfl

theorem isConstantVolumeJet_linearPolynomial (A : Herm n) {d : ℕ}
    (hd : 1 ≤ d) (hA : A.det ≠ 0) : IsConstantVolumeJet (linearPolynomial A) d := by
  rw [linearPolynomial_eq_linearPoly]
  refine ⟨linearPoly_fixesZero A, (linearPoly_degree_le A).trans hd, ?_, ?_⟩
  · simpa only [linearPoly_linearPart] using hA
  · intro a ha had
    rw [linearPoly_jacDet, coeff_C, ite_eq_right]
    intro heq
    have : a = 0 := heq.symm
    subst a
    simp at ha

end Yau.Proofs.Y01Aux
