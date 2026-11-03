import Yau.Proofs.F05BootstrapGoodDirections
import Yau.Proofs.F05BootstrapQuotientBounds

/-! Forward tangent segments and backward time segments carry actual
one-variable derivatives. The closed parameter interval never requires
values at a time after the terminal face. -/

open Set
open scoped ContDiff
noncomputable section
set_option maxHeartbeats 1600000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def F05GoodSegment (d : Option (RIdx n)) (h : ℝ) (p : Point n) (θ : ℝ) : Point n :=
  match d with
  | none => (p.1,p.2-h+θ*h)
  | some j => (p.1+(θ*h) • realVec j,p.2)

theorem F05_good_segment_derivative {ν d : Option (RIdx n)} {T h : ℝ}
    {u : Point n → V} {Q : Set (Point n)}
    (hGood : F05GoodDiffOn T d u (F05PosPatch ν T))
    (hSegment : ∀ p ∈ Q, ∀ θ ∈ Icc (0 : ℝ) 1, F05GoodSegment d h p θ ∈ F05PosPatch ν T) :
    ∀ p ∈ Q, ∀ θ ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun s => u (F05GoodSegment d h p s))
        (h • F05GoodPartial T d u (F05GoodSegment d h p θ)) (Icc 0 1) θ := by
  intro p hp θ hθ
  cases d with
  | none =>
    have hDiff := hGood (F05GoodSegment none h p θ) (hSegment p hp θ hθ)
    have hAffine : HasDerivAt (fun s : ℝ => p.2-h+s*h) h θ := by
      simpa only [one_mul,id_eq] using ((hasDerivAt_id θ).mul_const h).const_add (p.2-h)
    have hMap : MapsTo (fun s : ℝ => p.2-h+s*h) (Icc 0 1) (Ioc 0 T) := by
      intro s hs
      exact (hSegment p hp s hs).2
    exact hDiff.hasDerivWithinAt.scomp θ hAffine.hasDerivWithinAt hMap
  | some j =>
    have hDiff := hGood (F05GoodSegment (some j) h p θ) (hSegment p hp θ hθ)
    have hAffine : HasDerivAt (fun s : ℝ => h*(s-θ)) h θ := by
      simpa only [mul_one,id_eq] using ((hasDerivAt_id θ).sub_const θ).const_mul h
    have hComp := hDiff.hasDerivAt.scomp_of_eq θ hAffine (by simp)
    have hPoint (s : ℝ) : (p.1+(θ*h) • realVec j)+(h*(s-θ)) • realVec j =
        p.1+(s*h) • realVec j := by
      rw [add_assoc,← add_smul]
      congr 2
      ring
    simpa only [Function.comp_def,F05GoodSegment,F05GoodPartial,hPoint] using hComp.hasDerivWithinAt

theorem F05_good_segment_holderWeight (d : Option (RIdx n)) (h θ α : ℝ) (p q : Point n) :
    holderWeight α (F05GoodSegment d h p θ) (F05GoodSegment d h q θ) = holderWeight α p q := by
  cases d with
  | none =>
    have hTime : (p.2-h+θ*h)-(q.2-h+θ*h) = p.2-q.2 := by ring
    simp only [F05GoodSegment,holderWeight,Prod.fst,Prod.snd,hTime]
  | some j => simp only [F05GoodSegment,holderWeight,Prod.fst,Prod.snd,add_sub_add_right_eq_sub]

theorem F05_good_segment_quotient_holder {ν d : Option (RIdx n)} {T h α C : ℝ}
    (hh : 0 < h) {u : Point n → V} {Q K : Set (Point n)}
    (hGood : F05GoodDiffOn T d u (F05PosPatch ν T))
    (hSegment : ∀ p ∈ Q, ∀ θ ∈ Icc (0 : ℝ) 1, F05GoodSegment d h p θ ∈ F05PosPatch ν T)
    (hIn : ∀ p ∈ Q, ∀ θ ∈ Icc (0 : ℝ) 1, F05GoodSegment d h p θ ∈ K)
    (hHolder : HolderBound α K (F05GoodPartial T d u) C) :
    HolderBound α Q (fun p => h⁻¹ • (u (F05GoodSegment d h p 1)-u (F05GoodSegment d h p 0))) C := by
  apply F05_segment_quotient_holder hh hHolder.1 (F05_good_segment_derivative hGood hSegment)
  · intro p hp θ hθ
    exact hHolder.2.1 _ (hIn p hp θ ⟨hθ.1,hθ.2.le⟩)
  · intro p hp q hq θ hθ
    have h := hHolder.2.2 _ (hIn p hp θ ⟨hθ.1,hθ.2.le⟩) _ (hIn q hq θ ⟨hθ.1,hθ.2.le⟩)
    rwa [F05_good_segment_holderWeight] at h

end Yau.Proofs.F05Aux
