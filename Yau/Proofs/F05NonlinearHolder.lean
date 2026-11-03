import Yau.Proofs.F05ExponentialHolder
import Yau.LeafProofs.L16ResidualEstimates

/-! The scalar nonlinear correction has the required small Lipschitz factor
in its lower jet. Every highest derivative difference keeps this factor. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux

def F05ScalarCorrection {n : ℕ} (a b R F z lz : Point n → ℝ) (p : Point n) : ℝ :=
  a p*(Real.exp (-z p)-1)*(b p+lz p)+(1-a p*Real.exp (-z p))*R p-F p

theorem F05_scalar_correction_lipschitz {n : ℕ} (B K r : ℝ)
    (hB : 0 < B) (hK : 0 < K) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α s D : ℝ) (Q : Set (Point n))
      (a b R F z w lz lw : Point n → ℝ), 0 ≤ s → s ≤ 1 → 0 ≤ D →
      HolderBound α Q a B → HolderBound α Q b B → HolderBound α Q R B →
      HolderBound α Q z (s*r) → HolderBound α Q w (s*r) →
      HolderBound α Q (fun p => z p-w p) (s*D) →
      HolderBound α Q lz (K*r) → HolderBound α Q lw (K*r) →
      HolderBound α Q (fun p => lz p-lw p) (K*D) →
      HolderBound α Q (fun p => F05ScalarCorrection a b R F z lz p-
        F05ScalarCorrection a b R F w lw p) (C*s*D) := by
  let A := 2*Real.exp r*(1+r)*Real.exp (2*r)
  let C := 4*B*A*(2*B+K*r)+4*B*Real.exp r*r*K
  have hA : 0 < A := by dsimp only [A]; positivity
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro α s D Q a b R F z w lz lw hs hs1 hD ha hb hR hz hw hDiff hlz hlw hlDiff
  have hsr : s*r ≤ r := mul_le_of_le_one_left hr.le hs1
  have hzR := holderBound_mono_const hz hsr
  have hwR := holderBound_mono_const hw hsr
  have hNegDiff : HolderBound α Q (fun p => -z p-(-w p)) (s*D) := by
    convert holderBound_neg hDiff using 1
    funext p
    ring
  have hExpDiff := F05_holder_exp_difference (holderBound_neg hzR) (holderBound_neg hwR) hNegDiff
  have hRange (p : Point n) (hp : p ∈ Q) : -w p ≤ r := by
    have hh : |w p| ≤ r := hwR.2.1 p hp
    linarith [neg_abs_le (w p)]
  have hEW := F05_holder_exp_sub_one (holderBound_neg hw) hr.le hRange
  have hFirst := holderBound_mul (holderBound_mul ha hExpDiff) (holderBound_add hb hlz)
  have hSecond := holderBound_mul (holderBound_mul ha hEW) hlDiff
  have hThird := holderBound_mul (holderBound_mul ha hExpDiff) hR
  have hSum := holderBound_sub (holderBound_add hFirst hSecond) hThird
  have hEq (p : Point n) :
      (a p*(Real.exp (-z p)-Real.exp (-w p)))*(b p+lz p)+
        (a p*(Real.exp (-w p)-1))*(lz p-lw p)-
          (a p*(Real.exp (-z p)-Real.exp (-w p)))*R p =
            F05ScalarCorrection a b R F z lz p-F05ScalarCorrection a b R F w lw p := by
    unfold F05ScalarCorrection
    ring
  convert holderBound_congr_on hSum (fun p _ => hEq p) using 1
  dsimp only [C,A]
  ring

end Yau.Proofs.F05Aux
