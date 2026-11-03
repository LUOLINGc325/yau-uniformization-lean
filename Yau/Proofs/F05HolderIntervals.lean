import Yau.LeafProofs.L16BoundaryPhysicalData
import Yau.LeafProofs.L16LocalTimeTransport

/-! The native zero-based spatial Hölder transport is used on actual
closed time slabs by exact translation, without changing its constants. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.ParabolicCandidates Yau.LeafProofs.L16Aux
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E]

theorem F05_holder_spatial_pullback_interval {α l r C L : ℝ}
    (hα : 0 ≤ α) (hL : 0 ≤ L) {S K : Set (Space n)}
    (ψ : Space n → Space n) (hMap : MapsTo ψ S K)
    (hLip : ∀ x ∈ S, ∀ y ∈ S, ‖ψ x-ψ y‖ ≤ L*‖x-y‖)
    {f : Point n → E} (hf : HolderBound α (cylinder K l r) f C) :
    HolderBound α (cylinder S l r) (fun p => f (ψ p.1,p.2)) (C*(1+L^α)) := by
  have hShift : HolderBound α (cylinder K 0 (r-l)) (timeTranslate l f) C := by
    apply holderBound_timeTranslate_on_space
    simpa only [zero_add,sub_add_cancel] using hf
  have hPull := holderBound_spatial_lipschitz_pullback hα hL ψ hMap hLip hShift
  have hBack := holderBound_timeTranslate_on_space (l := l) (r := r) (τ := -l)
    (show HolderBound α (cylinder S (l+-l) (r+-l))
      (fun p => timeTranslate l f (ψ p.1,p.2)) (C*(1+L^α)) by
        simpa only [add_neg_cancel,sub_eq_add_neg] using hPull)
  apply holderBound_congr_on hBack
  intro p hp
  simp only [timeTranslate,timeTranslatePoint,Prod.fst,Prod.snd,neg_add_cancel_right]

theorem F05_spatial_holder_interval {α l r C : ℝ} {K : Set (Space n)} {f : Space n → E}
    (hf : HolderBound α (cylinder K 0 (r-l)) (fun p => f p.1) C) :
    HolderBound α (cylinder K l r) (fun p => f p.1) C := by
  have hBack := holderBound_timeTranslate_on_space (l := l) (r := r) (τ := -l)
    (show HolderBound α (cylinder K (l+-l) (r+-l)) (fun p => f p.1) C by
      simpa only [add_neg_cancel,sub_eq_add_neg] using hf)
  exact hBack

end Yau.Proofs.F05Aux
