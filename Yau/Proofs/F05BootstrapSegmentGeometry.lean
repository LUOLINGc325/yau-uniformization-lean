import Yau.Proofs.F05BootstrapGoodSegments
import Yau.Proofs.F05BootstrapFlatGeometry

/-! Buffered good segments stay inside the original physical cap and
positive-time slab, including a backward segment ending at terminal time. -/

open Set
noncomputable section
set_option maxHeartbeats 1400000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_good_segment_buffered {ν d : Option (RIdx n)} {h r R s0 s T : ℝ}
    (hd : F05GoodLetter ν d) (hh : 0 ≤ h) (hMargin : h ≤ R-r)
    (hTime : h ≤ s-s0) (hs0 : 0 < s0) (hR : R < 2)
    {p : Point n} (hp : p ∈ region ν r ×ˢ Icc s T) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) :
    F05GoodSegment d h p θ ∈ region ν R ×ˢ Icc s0 T ∧
      F05GoodSegment d h p θ ∈ F05PosPatch ν T := by
  have hθh : 0 ≤ θ*h := mul_nonneg hθ.1 hh
  have hθhh : θ*h ≤ h := mul_le_of_le_one_left hh hθ.2
  have hSegment : F05GoodSegment d h p θ ∈ region ν R ×ˢ Icc s0 T := by
    cases d with
    | none =>
      refine ⟨F05_region_mono (by linarith) hp.1,?_,?_⟩
      · change s0 ≤ p.2-h+θ*h
        linarith [hp.2.1]
      · change p.2-h+θ*h ≤ T
        linarith [hp.2.2]
    | some k =>
      refine ⟨⟨?_,?_⟩,by change s0 ≤ p.2; linarith [hp.2.1],hp.2.2⟩
      · change ‖p.1+(θ*h) • realVec k‖ ≤ R
        calc
          _ ≤ ‖p.1‖+‖(θ*h) • realVec k‖ := norm_add_le _ _
          _ = ‖p.1‖+θ*h := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hθh,realVec_norm,mul_one]
          _ ≤ R := by linarith [hp.1.1]
      · cases ν with
        | none => trivial
        | some j =>
          have hkj : k ≠ j := hd
          have hVec : realCoord (realVec k) j = 0 := by
            rw [← real_inner_realVec,realVec_inner,if_neg hkj]
          change realCoord (p.1+(θ*h) • realVec k) j ≤ 0
          rw [← realCoordLinear_apply,map_add,map_smul]
          simpa only [realCoordLinear_apply,smul_eq_mul,hVec,mul_zero,add_zero] using hp.1.2
  refine ⟨hSegment,⟨⟨F05_region_mem_flat hSegment.1,?_⟩,hs0.trans_le hSegment.2.1,hSegment.2.2⟩⟩
  simpa only [Metric.mem_ball,dist_zero_right] using hSegment.1.1.trans_lt hR

end Yau.Proofs.F05Aux
