import Yau.Proofs.F05BootstrapGoodQuotient
import Yau.Proofs.F05BootstrapSegmentGeometry

/-! The actual quotient has zero trace on the receiving physical plane.
Only buffered endpoint values on the original true face are used. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem F05_good_quotient_zero_receiving_face {ν d : Option (RIdx n)} {r R s0 s T h : ℝ}
    (hd : F05GoodLetter ν d) (hh : 0 ≤ h) (hSpace : h ≤ R-r) (hTime : h ≤ s-s0)
    (hs0 : 0 < s0) (hR : R < 2) {u : Point n → V} (hZero : F05ZeroFace ν T u) :
    ∀ j, ν = some j → ∀ x ∈ region ν r, realCoord x j = 0 →
      ∀ t ∈ Icc s T, F05GoodQuotient d h u (x,t) = 0 := by
  intro j hν x hx hx0 t ht
  subst ν
  have hSegment (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) :=
    (F05_good_segment_buffered hd hh hSpace hTime hs0 hR (p := (x,t)) ⟨hx,ht⟩ hθ).2
  have hCoord (θ : ℝ) : realCoord (F05GoodSegment d h (x,t) θ).1 j = 0 := by
    cases d with
    | none => exact hx0
    | some k =>
      have hkj : k ≠ j := hd
      have hVec : realCoord (realVec k) j = 0 := by
        rw [← real_inner_realVec,realVec_inner,ite_eq_right hkj]
      change realCoord (x+(θ*h) • realVec k) j = 0
      rw [← realCoordLinear_apply,map_add,map_smul]
      simp only [realCoordLinear_apply,smul_eq_mul,hVec,hx0,mul_zero,add_zero]
  have hValue (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : u (F05GoodSegment d h (x,t) θ) = 0 :=
    hZero _ (hSegment θ hθ).1.2 (hCoord θ) _ (hSegment θ hθ).2
  simp only [F05GoodQuotient,hValue 1 (by norm_num),hValue 0 (by norm_num),sub_self,smul_zero]

end Yau.Proofs.F05Aux
