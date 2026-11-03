import Yau.Proofs.F05FutureReflectionJets

/-! The terminal reflection preserves the genuine homogeneous initial
value/time jet and physical lateral trace, so its actual derivatives lie
in the existing zero-data FTC space. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux Yau.LeafProofs.L16BoundaryTimeAux
variable {n : ℕ}

theorem F05_future_reflection_zero_initial {X : Set (Space n)} {τ T : ℝ}
    (hτ : 0 < τ) (hτT : τ < T) (hBack : 0 ≤ 3*τ-2*T)
    {u : Point n → ℝ} (hu : C2 (cylinder X 0 τ) u)
    (h0 : ∀ x ∈ X, u (x,0) = 0)
    (hJ0 : ∀ x ∈ X, timeD (cylinder X 0 τ) u (x,0) = 0) :
    ∀ x ∈ X, F05FutureReflection τ u (x,0) = 0 ∧
      timeD (cylinder X 0 T) (F05FutureReflection τ u) (x,0) = 0 := by
  have hTailC2 := (F05_future_tail_jets hτT hBack hu).1
  have hTrace : ∀ x : Space n, u (x,τ) = F05FutureTail τ u (x,τ) :=
    fun x => (F05_future_tail_trace τ u x).symm
  intro x hx
  refine ⟨?_,?_⟩
  · simp only [F05FutureReflection,timePaste,hτ.le,ite_true,h0 x hx]
  · change timeD (cylinder X 0 T) (timePaste τ u (F05FutureTail τ u)) (x,0) = 0
    rw [timeD_timePaste_space hτ hτT hu hTailC2 (fun x _ => hTrace x)
      (fun x hx => (F05_future_tail_time_trace hτT hBack hu hx).symm)
      (show (x,0) ∈ cylinder X 0 T from ⟨hx,le_rfl,(hτ.trans hτT).le⟩)]
    simp only [timePaste,hτ.le,ite_true,hJ0 x hx]

theorem F05_future_reflection_zero_lateral {B : Set (Space n)} {τ T : ℝ}
    (hτT : τ ≤ T) (hBack : 0 ≤ 3*τ-2*T) {u : Point n → ℝ}
    (hZero : ∀ x ∈ B, ∀ t ∈ Icc 0 τ, u (x,t) = 0) :
    ∀ x ∈ B, ∀ t ∈ Icc 0 T, F05FutureReflection τ u (x,t) = 0 := by
  obtain ⟨hMap1,hMap2⟩ := F05_future_reflection_time_maps hτT hBack
  intro x hx t ht
  by_cases htτ : t ≤ τ
  · simpa only [F05FutureReflection,timePaste,htτ,ite_true] using hZero x hx t ⟨ht.1,htτ⟩
  · have htRight : t ∈ Icc τ T := ⟨(not_le.mp htτ).le,ht.2⟩
    simp only [F05FutureReflection,timePaste,htτ,ite_false,F05FutureTail,F05TimeAffine,F05TimeAffinePoint,
      hZero x hx _ (hMap1 htRight),hZero x hx _ (hMap2 htRight),mul_zero,sub_self]

end Yau.Proofs.F05Aux
