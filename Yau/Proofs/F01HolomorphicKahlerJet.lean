import Yau.Proofs.F01VariableFrameWirtinger
import Yau.Proofs.F01HolomorphicJacobianJets
import Yau.Proofs.F01WirtingerLinear

/-! Actual Kähler first-jet symmetry is preserved by any C2 holomorphic
coordinate change and its actual differential, including the Jacobian jet. -/
noncomputable section
open scoped ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ}

theorem holomorphic_congruence_wirt_symmetry
    (H : ComplexVector n → Matrix (Fin n) (Fin n) ℂ)
    (T : ComplexVector n → ComplexVector n) (z : ComplexVector n)
    (hT : ContDiffAt ℂ 2 T z)
    (hH : ∀ p q, DifferentiableAt ℝ (fun y => H y p q) (T z))
    (hsym : ∀ p q l, wirt (fun y => H y p q) (T z) (stdVec l) =
      wirt (fun y => H y p l) (T z) (stdVec q)) (i j k : Fin n) :
    wirt (fun w => ((linearMatrix (fderiv ℂ T w))ᴴ * H (T w) *
      linearMatrix (fderiv ℂ T w)) i j) z (stdVec k) =
    wirt (fun w => ((linearMatrix (fderiv ℂ T w))ᴴ * H (T w) *
      linearMatrix (fderiv ℂ T w)) i k) z (stdVec j) := by
  let J := fun w => linearMatrix (fderiv ℂ T w)
  let G := fun w => H (T w)
  have hTd : DifferentiableAt ℂ T z := hT.differentiableAt (by norm_num)
  have hJ (p q : Fin n) : DifferentiableAt ℂ (fun w => J w p q) z :=
    holomorphic_jacobian_entry_differentiableAt hT p q
  have hG (p q : Fin n) : DifferentiableAt ℝ (fun w => G w p q) z :=
    (hH p q).comp z (hTd.restrictScalars ℝ)
  have hjet (p q b : Fin n) :
      wirt (fun w => G w p q) z (stdVec b) =
        ∑ l, wirt (fun y => H y p q) (T z) (stdVec l) * J z l b := by
    rw [wirt_comp_complex_differentiable T (fun y => H y p q) z (stdVec b) hTd (hH p q),
      wirt_eq_coordinate_contraction]
    rfl
  have hfirst :
      (∑ q, ∑ p, star (J z p i) * wirt (fun w => G w p q) z (stdVec k) * J z q j) =
      ∑ q, ∑ p, star (J z p i) * wirt (fun w => G w p q) z (stdVec j) * J z q k := by
    simp_rw [hjet]
    simp only [Finset.mul_sum, Finset.sum_mul]
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro l hl
    rw [hsym p l q]
    ring
  have hsecond :
      (∑ q, ∑ p, star (J z p i) * G z p q * wirt (fun w => J w q j) z (stdVec k)) =
      ∑ q, ∑ p, star (J z p i) * G z p q * wirt (fun w => J w q k) z (stdVec j) := by
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro p hp
    rw [holomorphic_jacobian_wirt_symm hT q j k]
  change wirt (fun w => ((J w)ᴴ * G w * J w) i j) z (stdVec k) =
    wirt (fun w => ((J w)ᴴ * G w * J w) i k) z (stdVec j)
  rw [wirt_variable_congruence_entry J G z (stdVec k) hJ hG,
    wirt_variable_congruence_entry J G z (stdVec j) hJ hG]
  simp only [Finset.sum_add_distrib]
  exact congrArg₂ (· + ·) hfirst hsecond

end Yau.NodeProofs.F01Aux
