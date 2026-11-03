import Yau.LeafProofs.L16

/-! Actual exponential composition estimates in the native parabolic Holder
norm. The difference bound is linear in the Holder norm of the difference. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux

theorem F05_exp_lipschitz_upper {B x y : ℝ} (hx : x ≤ B) (hy : y ≤ B) :
    |Real.exp x-Real.exp y| ≤ Real.exp B*|x-y| := by
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := Real.exp) (s := Iic B) (𝕜 := ℝ)
    (fun z _ => Real.differentiableAt_exp)
    (fun z hz => by rw [Real.deriv_exp,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.mpr hz)
    (convex_Iic B) hy hx
  exact hh

theorem F05_holder_exp_sub_one {n : ℕ} {α F B : ℝ} {Q : Set (Point n)} {f : Point n → ℝ}
    (hf : HolderBound α Q f F) (hB : 0 ≤ B) (hRange : ∀ p ∈ Q, f p ≤ B) :
    HolderBound α Q (fun p => Real.exp (f p)-1) (Real.exp B*F) := by
  refine ⟨mul_nonneg (Real.exp_pos _).le hf.1,?_,?_⟩
  · intro p hp
    have hh := F05_exp_lipschitz_upper (hRange p hp) hB
    simp only [Real.exp_zero,sub_zero] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (hf.2.1 p hp) (Real.exp_pos _).le)
  · intro p hp q hq
    have hh := F05_exp_lipschitz_upper (hRange p hp) (hRange q hq)
    rw [sub_sub_sub_cancel_right]
    exact hh.trans ((mul_le_mul_of_nonneg_left (hf.2.2 p hp q hq) (Real.exp_pos _).le).trans_eq (by ring))

theorem F05_holder_exp {n : ℕ} {α F B : ℝ} {Q : Set (Point n)} {f : Point n → ℝ}
    (hf : HolderBound α Q f F) (hRange : ∀ p ∈ Q, f p ≤ B) :
    HolderBound α Q (fun p => Real.exp (f p)) (Real.exp B*(1+F)) := by
  have hE : 0 < Real.exp B := Real.exp_pos _
  refine ⟨mul_nonneg hE.le (by linarith [hf.1]),?_,?_⟩
  · intro p hp
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact (Real.exp_le_exp.mpr (hRange p hp)).trans (by nlinarith [hf.1])
  · intro p hp q hq
    have hh := (F05_exp_lipschitz_upper (hRange p hp) (hRange q hq)).trans
      (mul_le_mul_of_nonneg_left (hf.2.2 p hp q hq) hE.le)
    exact hh.trans (by
      have hWeight : 0 ≤ holderWeight α p q := add_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
        (Real.rpow_nonneg (abs_nonneg _) _)
      nlinarith)

theorem F05_holder_exp_difference {n : ℕ} {α R D : ℝ} {Q : Set (Point n)}
    {f g : Point n → ℝ} (hf : HolderBound α Q f R) (hg : HolderBound α Q g R)
    (hDiff : HolderBound α Q (fun p => f p-g p) D) :
    HolderBound α Q (fun p => Real.exp (f p)-Real.exp (g p))
      ((2*Real.exp R*(1+R)*Real.exp (2*R))*D) := by
  have hRangeF (p : Point n) (hp : p ∈ Q) : f p ≤ R := (le_abs_self _).trans (hf.2.1 p hp)
  have hRangeG (p : Point n) (hp : p ∈ Q) : g p ≤ R := (le_abs_self _).trans (hg.2.1 p hp)
  have hRangeD (p : Point n) (hp : p ∈ Q) : f p-g p ≤ 2*R := by
    have hAbs : |g p| ≤ R := hg.2.1 p hp
    have hNeg := neg_abs_le (g p)
    linarith [hRangeF p hp]
  have hExpG := F05_holder_exp hg hRangeG
  have hExpD := F05_holder_exp_sub_one hDiff (by linarith [hf.1] : 0 ≤ 2*R) hRangeD
  have hProduct := holderBound_mul hExpG hExpD
  have hEq (p : Point n) : Real.exp (g p)*(Real.exp (f p-g p)-1) = Real.exp (f p)-Real.exp (g p) := by
    rw [mul_sub,mul_one,← Real.exp_add]
    congr 2
    ring
  convert holderBound_congr_on hProduct (fun p _ => hEq p) using 1
  ring

end Yau.Proofs.F05Aux
