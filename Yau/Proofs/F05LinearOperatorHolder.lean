import Yau.Proofs.F05CanonicalLowerHolder
import Yau.Proofs.F05UniformCoefficients

/-! The actual differential operator has a genuine Holder budget in terms
of the separate raw Schauder and lower Holder bounds. -/

open Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux

theorem F05_linearOp_holder {n : ℕ} {α B P L : ℝ} {Q : Set (Point n)}
    {a : Point n → Mat n} {b : Point n → RIdx n → ℝ} {v : Point n → ℝ}
    (ha : HolderBound α Q a B) (hb : ∀ j, HolderBound α Q (fun p => b p j) B)
    (hv : SchauderBound α Q v P)
    (hLow : HolderBound α Q (fun p => (v p,spatialD v p)) L) :
    HolderBound α Q (linearOp Q a b v)
      (P+2*(Fintype.card (RIdx n) : ℝ)^2*B*P+2*(Fintype.card (RIdx n) : ℝ)*B*L) := by
  have hPrincipal := hessian_contraction_holderBound ha.1 hv.2.1
    (fun i j => holderBound_matrix_entry ha i j)
    (fun i j p hp => (frobenius_entry_abs_le (a p) i j).trans (ha.2.1 p hp))
    hv.2.2.2.1 hv.2.2.2.1.2.1
  have hDrift := holderBound_finset_sum Finset.univ (fun i _ =>
    holderBound_mul (hb i) (holderBound_gradient_component (holderBound_snd hLow) i))
  have h := holderBound_sub (holderBound_sub hv.2.2.2.2 hPrincipal) hDrift
  convert h using 1
  · rfl
  · simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    ring

end Yau.Proofs.F05Aux
