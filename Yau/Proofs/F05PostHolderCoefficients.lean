import Yau.LeafProofs.L16Normalization
import Yau.LeafProofs.L16ResidualEstimates

/-! The value-level boundary estimate controls the actual nonlinear
coefficient and reaction source without any derivative of the candidate. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_nonnegative_exp_inverse_holder {α C : ℝ} {Q : Set (Point n)}
    {w : Point n → ℝ} (hw : HolderBound α Q (fun p => Real.exp (w p)) C)
    (hNonneg : ∀ p ∈ Q, 0 ≤ w p) :
    HolderBound α Q (fun p => Real.exp (-w p)) (4+16*C) := by
  have hLower : ∀ p ∈ Q, (1/4 : ℝ) ≤ Real.exp (w p) := by
    intro p hp
    have hh := Real.one_le_exp_iff.mpr (hNonneg p hp)
    linarith
  simpa only [Real.exp_neg] using holderBound_inverse_of_lower_quarter hw hLower

theorem F05_nonnegative_exp_reaction_holder {α C B : ℝ} {Q : Set (Point n)}
    {w R : Point n → ℝ} (hw : HolderBound α Q (fun p => Real.exp (w p)) C)
    (hNonneg : ∀ p ∈ Q, 0 ≤ w p) (hR : HolderBound α Q R B) :
    HolderBound α Q (fun p => (1-Real.exp (-w p))*R p) (2*(1+(4+16*C))*B) := by
  have hOne : HolderBound α Q (fun _ => (1 : ℝ)) 1 := by
    simpa only [norm_one] using holderBound_const α Q (1 : ℝ)
  exact holderBound_mul (holderBound_sub hOne (F05_nonnegative_exp_inverse_holder hw hNonneg)) hR

end Yau.Proofs.F05Aux
