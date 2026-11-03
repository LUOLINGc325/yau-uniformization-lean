import Yau.Proofs.F05BootstrapGoodDirections

/-! The current relative Schauder regularity supplies the actual next good
derivative and its Hölder value bound. It asserts no higher jet of that next
word, so the finite nonlinear induction does not assume its own conclusion. -/

open Set Filter
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1600000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_good_time_eq_relative {X : Set (Space n)} {s T : ℝ}
    {v : Point n → ℝ} (hv : F05RelC2 X (Icc s T) v) {z : Point n}
    (hz : z ∈ X ×ˢ Icc s T) (hsz : s < z.2) (hz0 : 0 < z.2) :
    F05GoodPartial T none v z = F05RelT (Icc s T) v z ∧
      DifferentiableWithinAt ℝ (fun t => v (z.1,t)) (Ioc 0 T) z.2 := by
  have hNear : Icc s T ∈ 𝓝[Ioc 0 T] z.2 := by
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hsz)] with t ht hst
    exact ⟨hst.le,ht.2⟩
  have hDiff := hv.2.2.2.2.2 z hz
  exact ⟨derivWithin_of_mem_nhdsWithin hNear (uniqueDiffOn_Ioc (0 : ℝ) T z.2 ⟨hz0,hz.2.2⟩) hDiff,
    hDiff.mono_of_mem_nhdsWithin hNear⟩

theorem F05_posSpace_mem_region {ν : Option (RIdx n)} {x : Space n} {r : ℝ}
    (hx : x ∈ F05PosSpace ν) (hxr : ‖x‖ ≤ r) : x ∈ region ν r := by
  refine ⟨hxr,?_⟩
  have hFace := hx.1
  cases ν <;> simpa only [F05FlatOpen_closure,mem_ofPred_eq] using hFace

theorem F05_local_schauder_good_diff {ν d : Option (RIdx n)} {T α : ℝ}
    (hd : F05GoodLetter ν d) {v : Point n → ℝ} (hv : F05LocalSchauder α ν T v) :
    F05GoodDiffOn T d v (F05PosPatch ν T) := by
  intro z hz
  have hn : ‖z.1‖ < 2 := by
    simpa only [Metric.mem_ball,dist_zero_right] using hz.1.2
  let r : ℝ := (‖z.1‖+2)/2
  let s : ℝ := z.2/2
  have hr : 0 < r := by dsimp [r]; linarith [norm_nonneg z.1]
  have hr2 : r < 2 := by dsimp [r]; linarith
  have hs : 0 < s := by dsimp [s]; linarith [hz.2.1]
  have hsT : s < T := by dsimp [s]; linarith [hz.2.1,hz.2.2]
  obtain ⟨C,hC,hSch⟩ := hv r hr hr2 s hs hsT
  have hxR : z.1 ∈ region ν r := F05_posSpace_mem_region hz.1 (by dsimp [r]; linarith)
  have htI : z.2 ∈ Icc s T := ⟨by dsimp [s]; linarith [hz.2.1],hz.2.2⟩
  cases d with
  | none => exact (F05_good_time_eq_relative hSch.1 ⟨hxR,htI⟩
      (by dsimp [s]; linarith [hz.2.1]) hz.2.1).2
  | some k =>
    exact F05_good_spatial_diff (T := T) k
      ((hSch.1.2.2.2.2.1 z.2 htI z.1 hxR).differentiableWithinAt (by norm_num))
      (F05_good_line_mem_region hd hxR (by dsimp [r]; linarith))

theorem F05_local_schauder_good_holder {ν d : Option (RIdx n)} {T α : ℝ}
    (hd : F05GoodLetter ν d) {v : Point n → ℝ} (hv : F05LocalSchauder α ν T v) :
    F05LocalHolder α ν T (F05GoodPartial T d v) := by
  intro r hr hr2 s hs hsT
  let R : ℝ := (r+2)/2
  let S : ℝ := s/2
  have hR : 0 < R := by dsimp [R]; linarith
  have hR2 : R < 2 := by dsimp [R]; linarith
  have hSr : 0 < S := by dsimp [S]; linarith
  have hST : S < T := by dsimp [S]; linarith
  obtain ⟨C,hC,hSch⟩ := hv R hR hR2 S hSr hST
  have hrR : r < R := by dsimp [R]; linarith
  have hSub : region ν r ×ˢ Icc s T ⊆ region ν R ×ˢ Icc S T := by
    intro z hz
    exact ⟨F05_region_mono hrR.le hz.1,by dsimp [S]; linarith [hz.2.1],hz.2.2⟩
  refine ⟨C,hC,?_⟩
  cases d with
  | none =>
    apply holderBound_congr_on (holderBound_mono hSch.2.2.2 hSub)
    intro z hz
    exact (F05_good_time_eq_relative hSch.1 (hSub hz)
      (by dsimp [S]; linarith [hz.2.1]) (hs.trans_le hz.2.1)).1.symm
  | some k =>
    apply holderBound_congr_on (holderBound_mono
      (holderBound_gradient_component (holderBound_snd hSch.2.1) k) hSub)
    intro z hz
    have hzR := hSub hz
    have hLine := F05_good_line_mem_region hd hzR.1 (lt_of_le_of_lt hz.1.1 hrR)
    exact (F05_good_spatial_partial_eq_relD k
      ((hSch.1.2.2.2.2.1 z.2 hzR.2 z.1 hzR.1).differentiableWithinAt (by norm_num)) hLine).symm

end Yau.Proofs.F05Aux
