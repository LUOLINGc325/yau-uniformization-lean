import Yau.Proofs.F05BootstrapGoodDirections

/-! Actual one-variable product and exponential rules for good derivatives.
These rules require only the displayed first good derivatives. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_good_partial_add {T : ℝ} {d : Option (RIdx n)} {Q : Set (Point n)}
    {u v : Point n → ℝ} (hu : F05GoodDiffOn T d u Q) (hv : F05GoodDiffOn T d v Q)
    {z : Point n} (hz : z ∈ Q) :
    F05GoodPartial T d (fun p => u p+v p) z = F05GoodPartial T d u z+F05GoodPartial T d v z := by
  cases d with
  | none => exact derivWithin_fun_add (hu z hz) (hv z hz)
  | some j => exact deriv_fun_add (hu z hz) (hv z hz)

theorem F05_good_partial_mul {T : ℝ} {d : Option (RIdx n)} {Q : Set (Point n)}
    {u v : Point n → ℝ} (hu : F05GoodDiffOn T d u Q) (hv : F05GoodDiffOn T d v Q)
    {z : Point n} (hz : z ∈ Q) :
    F05GoodPartial T d (fun p => u p*v p) z =
      F05GoodPartial T d u z*v z+u z*F05GoodPartial T d v z := by
  cases d with
  | none => exact derivWithin_fun_mul (hu z hz) (hv z hz)
  | some j => simpa only [F05GoodPartial,zero_smul,add_zero] using deriv_fun_mul (hu z hz) (hv z hz)

theorem F05_good_diff_mul {T : ℝ} {d : Option (RIdx n)} {Q : Set (Point n)}
    {u v : Point n → ℝ} (hu : F05GoodDiffOn T d u Q) (hv : F05GoodDiffOn T d v Q) :
    F05GoodDiffOn T d (fun p => u p*v p) Q := by
  intro z hz
  cases d with
  | none => exact (hu z hz).mul (hv z hz)
  | some j => exact (hu z hz).mul (hv z hz)

theorem F05_good_diff_exp_neg {T : ℝ} {d : Option (RIdx n)} {Q : Set (Point n)}
    {u : Point n → ℝ} (hu : F05GoodDiffOn T d u Q) :
    F05GoodDiffOn T d (fun p => Real.exp (-u p)) Q := by
  intro z hz
  cases d with
  | none => exact (hu z hz).neg.exp
  | some j => exact (hu z hz).neg.exp

theorem F05_good_partial_exp_neg {T : ℝ} {d : Option (RIdx n)} {Q : Set (Point n)}
    {u : Point n → ℝ} (hu : F05GoodDiffOn T d u Q)
    {z : Point n} (hz : z ∈ Q) (ht : z.2 ∈ Ioc 0 T) :
    F05GoodPartial T d (fun p => Real.exp (-u p)) z =
      -Real.exp (-u z)*F05GoodPartial T d u z := by
  cases d with
  | none =>
    have h := (hu z hz).hasDerivWithinAt.neg.exp
    have hDeriv := h.derivWithin (uniqueDiffOn_Ioc 0 T z.2 ht)
    simpa only [F05GoodPartial,Pi.neg_apply,Prod.eta,mul_neg,neg_mul] using hDeriv
  | some j =>
    have h := (hu z hz).hasDerivAt.neg.exp
    simpa only [F05GoodPartial,Pi.neg_apply,zero_smul,add_zero,Prod.eta,mul_neg,neg_mul] using h.deriv

end Yau.Proofs.F05Aux
