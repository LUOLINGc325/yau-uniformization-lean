import Yau.Proofs.F05BootstrapGoodSegments

/-! A uniform good difference quotient approximates its actual computed
good derivative. Time quotients use only the preceding closed interval. -/

open Set
open scoped Topology
noncomputable section
set_option maxHeartbeats 1800000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def F05GoodExponent {n : ℕ} (d : Option (RIdx n)) (α : ℝ) : ℝ :=
  match d with | none => α/2 | some _ => α

def F05GoodQuotient (d : Option (RIdx n)) (h : ℝ) (u : Point n → V) (p : Point n) : V :=
  h⁻¹ • (u (F05GoodSegment d h p 1)-u (F05GoodSegment d h p 0))

theorem F05_good_segment_weight_to_base (d : Option (RIdx n)) {h α : ℝ}
    (hh : 0 ≤ h) (hα : 0 < α) (p : Point n) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) :
    holderWeight α (F05GoodSegment d h p θ) p ≤ h^(F05GoodExponent d α) := by
  have hθh : 0 ≤ θ*h := mul_nonneg hθ.1 hh
  have hθhh : θ*h ≤ h := mul_le_of_le_one_left hh hθ.2
  cases d with
  | none =>
    have hDiff : p.2-h+θ*h-p.2 = θ*h-h := by ring
    have hAbs : |θ*h-h| ≤ h := (abs_le).mpr ⟨by linarith,by linarith⟩
    simpa only [F05GoodSegment,F05GoodExponent,holderWeight,Prod.fst,Prod.snd,sub_self,norm_zero,
      Real.zero_rpow hα.ne',zero_add,hDiff] using
      Real.rpow_le_rpow (abs_nonneg (θ*h-h)) hAbs (show 0 ≤ α/2 by positivity)
  | some j =>
    have hDist : ‖(p.1+(θ*h) • realVec j)-p.1‖ ≤ h := by
      simpa only [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg hθh,realVec_norm,mul_one] using hθhh
    simpa only [F05GoodSegment,F05GoodExponent,holderWeight,Prod.fst,Prod.snd,sub_self,abs_zero,
      Real.zero_rpow (show α/2 ≠ 0 by positivity),add_zero] using
      Real.rpow_le_rpow (norm_nonneg _) hDist hα.le

theorem F05_segment_quotient_remainder_at {h E : ℝ} (hh : 0 < h) {g D : ℝ → V} (w : V)
    (hDeriv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt g (h • D t) (Icc 0 1) t)
    (hBound : ∀ t ∈ Ico (0 : ℝ) 1, ‖D t-w‖ ≤ E) :
    ‖h⁻¹ • (g 1-g 0)-w‖ ≤ E := by
  have hDerivative : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun a => g a-a • (h • w)) (h • (D t-w)) (Icc 0 1) t := by
    intro t ht
    have hLinear := ((hasDerivAt_id t).smul_const (h • w)).hasDerivWithinAt (s := Icc 0 1)
    have hRaw := (hDeriv t ht).sub hLinear
    simp only [one_smul] at hRaw
    change HasDerivWithinAt (fun a => g a-a • (h • w)) (h • D t-h • w) (Icc 0 1) t at hRaw
    rwa [← smul_sub] at hRaw
  have hEstimate := F05_segment_quotient_norm hh hDerivative hBound
  have hEq : h⁻¹ • ((g 1-(1 : ℝ) • (h • w))-(g 0-(0 : ℝ) • (h • w))) =
      h⁻¹ • (g 1-g 0)-w := by
    simp only [one_smul,zero_smul,sub_zero,smul_sub,smul_smul,one_mul,zero_mul,smul_zero,
      inv_mul_cancel₀ hh.ne',one_smul]
    abel
  exact hEq ▸ hEstimate

theorem F05_good_quotient_uniform_error {ν d : Option (RIdx n)} {T h α C : ℝ}
    (hh : 0 < h) (hα : 0 < α) {u : Point n → V} {Q K : Set (Point n)}
    (hGood : F05GoodDiffOn T d u (F05PosPatch ν T))
    (hSegment : ∀ p ∈ Q, ∀ θ ∈ Icc (0 : ℝ) 1, F05GoodSegment d h p θ ∈ F05PosPatch ν T)
    (hIn : ∀ p ∈ Q, ∀ θ ∈ Icc (0 : ℝ) 1, F05GoodSegment d h p θ ∈ K)
    (hHolder : HolderBound α K (F05GoodPartial T d u) C) :
    ∀ p ∈ Q, ‖F05GoodQuotient d h u p-F05GoodPartial T d u p‖ ≤ C*h^(F05GoodExponent d α) := by
  intro p hp
  have hpK : p ∈ K := by
    cases d with
    | none => simpa only [F05GoodSegment,one_mul,sub_add_cancel,Prod.eta] using hIn p hp 1 (by norm_num)
    | some j => simpa only [F05GoodSegment,zero_mul,zero_smul,add_zero,Prod.eta] using hIn p hp 0 (by norm_num)
  apply F05_segment_quotient_remainder_at hh (F05GoodPartial T d u p)
    (F05_good_segment_derivative hGood hSegment p hp)
  intro θ hθ
  exact (hHolder.2.2 _ (hIn p hp θ ⟨hθ.1,hθ.2.le⟩) p hpK).trans
    (mul_le_mul_of_nonneg_left (F05_good_segment_weight_to_base d hh.le hα p ⟨hθ.1,hθ.2.le⟩) hHolder.1)

end Yau.Proofs.F05Aux
