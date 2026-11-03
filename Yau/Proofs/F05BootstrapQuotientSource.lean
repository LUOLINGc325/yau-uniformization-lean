import Yau.Proofs.F05BootstrapGoodQuotient
import Yau.Proofs.F05BootstrapSpatialQuotientEquation
import Yau.Proofs.F05BootstrapTemporalQuotientEquation
import Yau.LeafProofs.L16LinearizedSource

/-! The actual full source of a good quotient retains every principal
and drift correction, with an explicit common Holder budget. -/

open Set
open scoped Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1600000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

def F05GoodShift (d : Option (RIdx n)) (h : ℝ) (z : Point n) : Point n :=
  match d with
  | none => timeTranslatePoint (-h) z
  | some j => spatialTranslatePoint (h • realVec j) z

def F05GoodQuotientSource (d : Option (RIdx n)) (h : ℝ) (X : Set (Space n))
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ) (f u : Point n → ℝ) (z : Point n) : ℝ :=
  F05GoodQuotient d h f z+
    (∑ j,∑ k,F05GoodQuotient d h a z j k*
      F05RelDD X u (F05GoodShift d h z) (realVec j) (realVec k))+
    ∑ j,F05GoodQuotient d h (fun p => b p j) z*F05RelD X u (F05GoodShift d h z) (realVec j)

theorem F05_good_shift_holderWeight (d : Option (RIdx n)) (h α : ℝ) (p q : Point n) :
    holderWeight α (F05GoodShift d h p) (F05GoodShift d h q) = holderWeight α p q := by
  cases d <;> simp only [F05GoodShift,timeTranslatePoint,spatialTranslatePoint,holderWeight,
    add_sub_add_right_eq_sub]

theorem F05_good_shift_holder {V : Type*} [NormedAddCommGroup V]
    {d : Option (RIdx n)} {h α C : ℝ} {Q K : Set (Point n)} {f : Point n → V}
    (hf : HolderBound α K f C) (hMap : MapsTo (F05GoodShift d h) Q K) :
    HolderBound α Q (fun z => f (F05GoodShift d h z)) C := by
  refine ⟨hf.1,fun z hz => hf.2.1 _ (hMap hz),?_⟩
  intro p hp q hq
  have hBound := hf.2.2 _ (hMap hp) _ (hMap hq)
  rwa [F05_good_shift_holderWeight] at hBound

theorem F05_relative_contraction_source_holder {α F M U : ℝ} {Q : Set (Point n)}
    {f : Point n → ℝ} {a : Point n → Mat n} {b : Point n → RIdx n → ℝ}
    {H : Point n → Space n →L[ℝ] Space n →L[ℝ] ℝ} {G : Point n → Space n →L[ℝ] ℝ}
    (hf : HolderBound α Q f F) (ha : HolderBound α Q a M)
    (hb : ∀ j, HolderBound α Q (fun z => b z j) M)
    (hH : HolderBound α Q H U) (hG : HolderBound α Q G U) :
    HolderBound α Q
      (fun z => f z+(∑ j,∑ k,a z j k*H z (realVec j) (realVec k))+
        ∑ j,b z j*G z (realVec j)) (linearizedSourceBudget n F M U) := by
  have hPrincipal := hessian_contraction_holderBound ha.1 hH.1
    (fun j k => holderBound_matrix_entry ha j k)
    (fun j k z hz => by simpa only [Real.norm_eq_abs] using (holderBound_matrix_entry ha j k).2.1 z hz)
    hH hH.2.1
  have hDrift := holderBound_finset_sum Finset.univ (fun j _ =>
    holderBound_mul (hb j) (holderBound_gradient_component hG j))
  have hResult := holderBound_add (holderBound_add hf hPrincipal) hDrift
  simpa only [linearizedSourceBudget,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using hResult

theorem F05_good_quotient_source_holder {α F M U h : ℝ} {d : Option (RIdx n)}
    {Q : Set (Point n)} (X : Set (Space n))
    {a : Point n → Mat n} {b : Point n → RIdx n → ℝ} {f u : Point n → ℝ}
    (hf : HolderBound α Q (F05GoodQuotient d h f) F)
    (ha : HolderBound α Q (F05GoodQuotient d h a) M)
    (hb : ∀ j, HolderBound α Q (F05GoodQuotient d h (fun z => b z j)) M)
    (hH : HolderBound α Q (fun z => F05RelDD X u (F05GoodShift d h z)) U)
    (hG : HolderBound α Q (fun z => F05RelD X u (F05GoodShift d h z)) U) :
    HolderBound α Q (F05GoodQuotientSource d h X a b f u) (linearizedSourceBudget n F M U) :=
  F05_relative_contraction_source_holder hf ha hb hH hG

end Yau.Proofs.F05Aux
