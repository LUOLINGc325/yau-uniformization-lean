import Yau.LeafProofs.L17ScalarHessianProduct
import Yau.LeafProofs.L17FrozenCoefficientHolder

open Set
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux

open Yau.Parabolic

def scalarFrozenResidual {n : ℕ} (a d : Point n → Mat n) (φ : Space n → ℝ)
    (v : Point n → ℝ) (q : Point n) : ℝ :=
  φ q.1 * realHessianContraction (d q) (fun z => v (z,q.2)) q.1 -
    v q * realHessianContraction (a q) φ q.1 - gradientCrossContraction (a q) φ (fun z => v (z,q.2)) q.1

theorem scalarFrozenResidual_eq_sum {n : ℕ} (a d : Point n → Mat n) (φ : Space n → ℝ)
    (v : Point n → ℝ) (q : Point n) :
    scalarFrozenResidual a d φ v q = ∑ i : RIdx n, ∑ j : RIdx n,
      ((φ q.1 * d q i j) * spatialDD v q (realVec i) (realVec j) -
        a q i j * (fderiv ℝ φ q.1 (realVec i) * spatialD v q (realVec j) +
          spatialD v q (realVec i) * fderiv ℝ φ q.1 (realVec j) +
          v q * fderiv ℝ (fderiv ℝ φ) q.1 (realVec i) (realVec j))) := by
  simp only [scalarFrozenResidual,realHessianContraction,gradientCrossContraction,
    spatialD,spatialDD,Finset.mul_sum,Finset.sum_sub_distrib,mul_add,Finset.sum_add_distrib]
  simp only [mul_assoc,mul_left_comm,mul_comm]
  ring

theorem scalarFrozenResidual_holderBound {n : ℕ} {γ M D E0 E1 E2 J C : ℝ}
    {Q : Set (Point n)} {a d : Point n → Mat n} {φ : Space n → ℝ} {v : Point n → ℝ}
    (ha : ∀ i j, HolderBound γ Q (fun q => a q i j) M)
    (hd : ∀ i j, HolderBound γ Q (fun q => d q i j) D)
    (hφ0 : HolderBound γ Q (fun q => φ q.1) E0)
    (hφ1 : HolderBound γ Q (fun q => fderiv ℝ φ q.1) E1)
    (hφ2 : HolderBound γ Q (fun q => fderiv ℝ (fderiv ℝ φ) q.1) E2)
    (hJet : HolderBound γ Q (fun q => (v q,spatialD v q)) J)
    (hHess : HolderBound γ Q (spatialDD v) C) :
    HolderBound γ Q (scalarFrozenResidual a d φ v)
      ((Fintype.card (RIdx n) : ℝ)^2 * (4*E0*D*C+8*M*E1*J+4*M*E2*J)) := by
  have hV := L16Aux.holderBound_fst hJet
  have hDv (i : RIdx n) := L16Aux.holderBound_gradient_component (L16Aux.holderBound_snd hJet) i
  have hDφ (i : RIdx n) := L16Aux.holderBound_gradient_component hφ1 i
  have hDDφ (i j : RIdx n) := L16Aux.holderBound_hessian_component hφ2 i j
  have hDDv (i j : RIdx n) := L16Aux.holderBound_hessian_component hHess i j
  have hEach (i j : RIdx n) : HolderBound γ Q
      (fun q => (φ q.1*d q i j)*spatialDD v q (realVec i) (realVec j) -
        a q i j*(fderiv ℝ φ q.1 (realVec i)*spatialD v q (realVec j)+
          spatialD v q (realVec i)*fderiv ℝ φ q.1 (realVec j)+
          v q*fderiv ℝ (fderiv ℝ φ) q.1 (realVec i) (realVec j)))
      (4*E0*D*C+8*M*E1*J+4*M*E2*J) := by
    have hPrincipal := L16Aux.holderBound_mul (L16Aux.holderBound_mul hφ0 (hd i j)) (hDDv i j)
    have hLower := L16Aux.holderBound_mul (ha i j) (L16Aux.holderBound_add
      (L16Aux.holderBound_add (L16Aux.holderBound_mul (hDφ i) (hDv j))
        (L16Aux.holderBound_mul (hDv i) (hDφ j))) (L16Aux.holderBound_mul hV (hDDφ i j)))
    have h := L16Aux.holderBound_sub hPrincipal hLower
    have hConst : 2*(2*E0*D)*C+2*M*((2*E1*J+2*J*E1)+2*J*E2) =
        4*E0*D*C+8*M*E1*J+4*M*E2*J := by ring
    simpa only [hConst] using h
  have hRow (i : RIdx n) := L16Aux.holderBound_finset_sum Finset.univ (fun j _ => hEach i j)
  have hSum := L16Aux.holderBound_finset_sum Finset.univ (fun i _ => hRow i)
  change HolderBound γ Q (fun q => scalarFrozenResidual a d φ v q) _
  simp_rw [scalarFrozenResidual_eq_sum]
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,pow_two,mul_assoc] using hSum

end Yau.LeafProofs.L17Aux
