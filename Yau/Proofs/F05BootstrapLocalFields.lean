import Yau.Proofs.F05BootstrapGoodValue
import Yau.Proofs.F05BootstrapFlatGeometry
import Yau.Proofs.F05BootstrapLocalJets

/-! Local Schauder fields determine the actual computed relative C2 field
on the whole positive-time physical patch. This is local calculus and
gluing of the already supplied jets, with no mixed-joint derivative claim. -/

open Set Filter
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_posSpace_uniqueDiffOn (ν : Option (RIdx n)) : UniqueDiffOn ℝ (F05PosSpace ν) :=
  (F05_flat_closure_uniqueDiffOn ν).inter Metric.isOpen_ball

theorem F05_pos_cap_jets {ν : Option (RIdx n)} {R s T : ℝ}
    (hR : 0 < R) {v : Point n → ℝ} (hv : F05RelC2 (region ν R) (Icc s T) v)
    {z : Point n} (hz : z ∈ F05PosPatch ν T) (hxR : ‖z.1‖ < R) (hst : s < z.2) :
    F05RelD (F05PosSpace ν) v z = F05RelD (region ν R) v z ∧
      F05RelDD (F05PosSpace ν) v z = F05RelDD (region ν R) v z ∧
      F05RelT (Ioc 0 T) v z = F05RelT (Icc s T) v z := by
  have hzR : z ∈ region ν R ×ˢ Icc s T :=
    ⟨F05_posSpace_mem_region hz.1 hxR.le,hst.le,hz.2.2⟩
  have hJets := F05_relative_local_domain_jets (F05_posSpace_uniqueDiffOn ν)
    (F05_region_uniqueDiffOn ν hR) Metric.isOpen_ball (V := Metric.ball 0 R)
    (fun x hx => F05_posSpace_mem_region hx.1 (by simpa only [dist_zero_right] using (Metric.mem_ball.mp hx.2).le))
    hv (z := z) ⟨⟨hz.1,by simpa only [Metric.mem_ball,dist_zero_right] using hxR⟩,hzR.2⟩
  exact ⟨hJets.1,hJets.2,(F05_good_time_eq_relative hv hzR hst hz.2.1).1⟩

theorem F05_continuousOn_posPatch_of_caps {E : Type*} [TopologicalSpace E]
    {ν : Option (RIdx n)} {T : ℝ} {f : Point n → E}
    (hf : ∀ r : ℝ, 0 < r → r < 2 → ∀ s : ℝ, 0 < s → s < T →
      ContinuousOn f (region ν r ×ˢ Icc s T)) : ContinuousOn f (F05PosPatch ν T) := by
  intro z hz
  have hn : ‖z.1‖ < 2 := by simpa only [Metric.mem_ball,dist_zero_right] using hz.1.2
  let R := (‖z.1‖+2)/2
  let s := z.2/2
  have hR : 0 < R := by dsimp only [R]; linarith [norm_nonneg z.1]
  have hR2 : R < 2 := by dsimp only [R]; linarith
  have hs : 0 < s := by dsimp only [s]; linarith [hz.2.1]
  have hsT : s < T := by dsimp only [s]; linarith [hz.2.1,hz.2.2]
  have hxR : ‖z.1‖ < R := by dsimp only [R]; linarith
  have hst : s < z.2 := by dsimp only [s]; linarith [hz.2.1]
  let U : Set (Point n) := {p | ‖p.1‖ < R ∧ s < p.2}
  have hU : IsOpen U := (isOpen_lt continuous_fst.norm continuous_const).inter
    (isOpen_lt continuous_const continuous_snd)
  have hzU : z ∈ U := ⟨hxR,hst⟩
  have hNear : region ν R ×ˢ Icc s T ∈ 𝓝[F05PosPatch ν T] z := by
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hzU)] with p hp hpU
    exact ⟨F05_posSpace_mem_region hp.1 hpU.1.le,hpU.2.le,hp.2.2⟩
  exact ((hf R hR hR2 s hs hsT) z
    ⟨F05_posSpace_mem_region hz.1 hxR.le,hst.le,hz.2.2⟩).mono_of_mem_nhdsWithin hNear

theorem F05_local_schauder_to_relative {ν : Option (RIdx n)} {T α : ℝ}
    {v : Point n → ℝ} (hv : F05LocalSchauder α ν T v) :
    F05RelC2 (F05PosSpace ν) (Ioc 0 T) v := by
  have hContinuous (r : ℝ) (hr : 0 < r) (hr2 : r < 2)
      (s : ℝ) (hs : 0 < s) (hsT : s < T) :
      ContinuousOn v (region ν r ×ˢ Icc s T) ∧
      ContinuousOn (F05RelD (F05PosSpace ν) v) (region ν r ×ˢ Icc s T) ∧
      ContinuousOn (F05RelDD (F05PosSpace ν) v) (region ν r ×ˢ Icc s T) ∧
      ContinuousOn (F05RelT (Ioc 0 T) v) (region ν r ×ˢ Icc s T) := by
    let R := (r+2)/2
    let S := s/2
    have hR : 0 < R := by dsimp only [R]; linarith
    have hR2 : R < 2 := by dsimp only [R]; linarith
    have hrR : r < R := by dsimp only [R]; linarith
    have hS : 0 < S := by dsimp only [S]; linarith
    have hST : S < T := by dsimp only [S]; linarith
    obtain ⟨C,hC,hSch⟩ := hv R hR hR2 S hS hST
    have hSub : region ν r ×ˢ Icc s T ⊆ region ν R ×ˢ Icc S T :=
      fun z hz => ⟨F05_region_mono hrR.le hz.1,by dsimp only [S]; linarith [hz.2.1],hz.2.2⟩
    have hPos (z : Point n) (hz : z ∈ region ν r ×ˢ Icc s T) : z ∈ F05PosPatch ν T :=
      ⟨⟨F05_region_mem_flat hz.1,by simpa only [Metric.mem_ball,dist_zero_right] using hz.1.1.trans_lt hr2⟩,
        hs.trans_le hz.2.1,hz.2.2⟩
    have hJets (z : Point n) (hz : z ∈ region ν r ×ˢ Icc s T) :=
      F05_pos_cap_jets hR hSch.1 (hPos z hz) (hz.1.1.trans_lt hrR)
        (show S < z.2 by dsimp only [S]; linarith [hz.2.1])
    exact ⟨hSch.1.1.mono hSub,(hSch.1.2.1.mono hSub).congr (fun z hz => (hJets z hz).1),
      (hSch.1.2.2.1.mono hSub).congr (fun z hz => (hJets z hz).2.1),
      (hSch.1.2.2.2.1.mono hSub).congr (fun z hz => (hJets z hz).2.2)⟩
  refine ⟨F05_continuousOn_posPatch_of_caps (fun r hr hr2 s hs hsT => (hContinuous r hr hr2 s hs hsT).1),
    F05_continuousOn_posPatch_of_caps (fun r hr hr2 s hs hsT => (hContinuous r hr hr2 s hs hsT).2.1),
    F05_continuousOn_posPatch_of_caps (fun r hr hr2 s hs hsT => (hContinuous r hr hr2 s hs hsT).2.2.1),
    F05_continuousOn_posPatch_of_caps (fun r hr hr2 s hs hsT => (hContinuous r hr hr2 s hs hsT).2.2.2),?_,?_⟩
  · intro t ht x hx
    have hn : ‖x‖ < 2 := by simpa only [Metric.mem_ball,dist_zero_right] using hx.2
    let R := (‖x‖+2)/2
    let s := t/2
    have hR : 0 < R := by dsimp only [R]; linarith [norm_nonneg x]
    have hR2 : R < 2 := by dsimp only [R]; linarith
    have hs : 0 < s := by dsimp only [s]; linarith [ht.1]
    have hsT : s < T := by dsimp only [s]; linarith [ht.1,ht.2]
    have hxR : ‖x‖ < R := by dsimp only [R]; linarith
    obtain ⟨C,hC,hSch⟩ := hv R hR hR2 s hs hsT
    have hNear : region ν R ∈ 𝓝[F05PosSpace ν] x := by
      filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds
        (Metric.isOpen_ball.mem_nhds (show x ∈ Metric.ball 0 R by simpa only [Metric.mem_ball,dist_zero_right] using hxR))] with y hy hyR
      exact F05_posSpace_mem_region hy (by simpa only [dist_zero_right] using (Metric.mem_ball.mp hyR).le)
    exact ((hSch.1.2.2.2.2.1 t ⟨by dsimp only [s]; linarith [ht.1],ht.2⟩) x
      (F05_posSpace_mem_region hx hxR.le)).mono_of_mem_nhdsWithin hNear
  · exact F05_local_schauder_good_diff (d := none) (by cases ν <;> trivial) hv

end Yau.Proofs.F05Aux
