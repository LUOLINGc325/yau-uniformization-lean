import Yau.Proofs.F05BootstrapQuotientSource
import Yau.Proofs.F05BootstrapQuotientIdentity
import Yau.Proofs.F05BootstrapSegmentGeometry

/-! One exact quotient equation covers all good tangent directions and
backward time. Its jets are actual within derivatives on the receiving cap. -/

open Set
noncomputable section
set_option maxHeartbeats 2200000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_relative_good_quotient_equation {ν d : Option (RIdx n)} {r R s0 s T h : ℝ}
    (hd : F05GoodLetter ν d) (hr : 0 < r) (hrR : r < R) (hR : R < 2)
    (hs0 : 0 < s0) (hs0s : s0 < s) (hsT : s < T)
    (hh : 0 < h) (hSpace : h ≤ R-r) (hTime : h ≤ s-s0)
    {u f : Point n → ℝ} (hu : F05RelC2 (region ν R) (Icc s0 T) u)
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ)
    (hPDE : ∀ z ∈ region ν R ×ˢ Icc s0 T,
      F05RelOp (region ν R) (Icc s0 T) a b u z = f z) :
    F05RelC2 (region ν r) (Icc s T) (F05GoodQuotient d h u) ∧
      ∀ z ∈ region ν r ×ˢ Icc s T,
        F05RelOp (region ν r) (Icc s T) a b (F05GoodQuotient d h u) z =
          F05GoodQuotientSource d h (region ν R) a b f u z := by
  have hX := F05_region_uniqueDiffOn ν hr
  have hY := F05_region_uniqueDiffOn ν (hr.trans hrR)
  have hTI := uniqueDiffOn_Icc hsT
  have hTOriginal := uniqueDiffOn_Icc (hs0s.trans hsT)
  have hXY : region ν r ⊆ region ν R := F05_region_mono hrR.le
  have hI : Icc s T ⊆ Icc s0 T := fun t ht => ⟨hs0s.le.trans ht.1,ht.2⟩
  cases d with
  | some j =>
    have hMap : MapsTo (fun x => x+h • realVec j) (region ν r) (region ν R) := by
      intro x hx
      have hSegment := F05_good_segment_buffered hd hh.le hSpace hTime hs0 hR
        (p := (x,s)) ⟨hx,le_rfl,hsT.le⟩ (θ := 1) (by norm_num)
      simpa only [F05GoodSegment,one_mul] using hSegment.1.1
    have huTime := F05_relative_c2_restrict hY hY hTI Subset.rfl hI hu
    have hEqTime : ∀ z ∈ region ν R ×ˢ Icc s T,
        F05RelOp (region ν R) (Icc s T) a b u z = f z := by
      intro z hz
      have hJets := F05_relative_restriction_jets hY hY hTI Subset.rfl hI hu hz
      simpa only [F05RelOp,hJets.1,hJets.2.1,hJets.2.2] using hPDE z ⟨hz.1,hI hz.2⟩
    have hResult := F05_relative_spatial_quotient_equation hX hY hTI hXY (realVec j) h hMap huTime a b hEqTime
    constructor
    · rw [F05_good_quotient_spatial]
      exact hResult.1
    · intro z hz
      rw [F05_good_quotient_spatial]
      simpa only [F05GoodQuotientSource,F05GoodQuotient,F05GoodSegment,F05GoodShift,
        spatialDifferenceQuotient,spatialTranslatePoint,one_mul,zero_mul,zero_smul,add_zero,
        Matrix.smul_apply,Matrix.sub_apply,smul_eq_mul,Prod.eta] using hResult.2 z hz
  | none =>
    have huX := F05_relative_c2_restrict hY hX hTOriginal hXY Subset.rfl hu
    have hEqX : ∀ z ∈ region ν r ×ˢ Icc s0 T,
        F05RelOp (region ν r) (Icc s0 T) a b u z = f z := by
      intro z hz
      have hJets := F05_relative_restriction_jets hY hX hTOriginal hXY Subset.rfl hu hz
      simpa only [F05RelOp,hJets.1,hJets.2.1,hJets.2.2] using hPDE z ⟨hXY hz.1,hz.2⟩
    have hResult := F05_relative_backward_time_quotient_equation hX hsT hh.le
      (by linarith) huX a b hEqX
    constructor
    · rw [F05_good_quotient_temporal]
      exact hResult.1
    · intro z hz
      let q := timeTranslatePoint (-h) z
      have hq : q ∈ region ν r ×ˢ Icc s0 T := by
        refine ⟨hz.1,?_,?_⟩ <;> dsimp only [q,timeTranslatePoint] <;> linarith [hz.2.1,hz.2.2]
      have hJets := F05_relative_restriction_jets hY hX hTOriginal hXY Subset.rfl hu hq
      have hEquation := hResult.2 z hz
      dsimp only at hEquation
      rw [hJets.1,hJets.2.1] at hEquation
      rw [F05_good_quotient_temporal]
      simpa only [F05GoodQuotientSource,F05GoodQuotient,F05GoodSegment,F05GoodShift,
        F05BackwardTimeQuotient,timeTranslate,timeTranslatePoint,one_mul,zero_mul,add_zero,sub_add_cancel,
        Matrix.smul_apply,Matrix.sub_apply,Matrix.add_apply,Matrix.neg_apply,smul_eq_mul,Prod.eta,sub_eq_add_neg,
        neg_add_cancel_right,q] using hEquation

end Yau.Proofs.F05Aux
