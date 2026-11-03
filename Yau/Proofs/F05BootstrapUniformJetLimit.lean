import Yau.Proofs.F05BootstrapClosedTimeDerivative
import Yau.Proofs.F05BootstrapHolderLimit
import Yau.Proofs.F05BootstrapRegions

/-! Uniform convergence of the actual closed spatial and one-sided time jets
identifies the computed derivatives of the value limit. This is the calculus
part of the compact tuple limit; no convergence in a Hölder norm is assumed. -/

open Set Filter
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1600000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_relative_schauder_uniform_jets (ν : Option (RIdx n)) {r s T α C : ℝ}
    (hr : 0 < r) (hsT : s < T) {v : ℕ → Point n → ℝ} {vLim : Point n → ℝ}
    {G : Point n → Space n →L[ℝ] ℝ}
    {H : Point n → Space n →L[ℝ] Space n →L[ℝ] ℝ} {J : Point n → ℝ}
    (hv : ∀ k, F05RelSchauder α (region ν r) (Icc s T) (v k) C)
    (hLim : TendstoUniformlyOn v vLim atTop (region ν r ×ˢ Icc s T))
    (hGLim : TendstoUniformlyOn (fun k => F05RelD (region ν r) (v k)) G atTop
      (region ν r ×ˢ Icc s T))
    (hHLim : TendstoUniformlyOn (fun k => F05RelDD (region ν r) (v k)) H atTop
      (region ν r ×ˢ Icc s T))
    (hJLim : TendstoUniformlyOn (fun k => F05RelT (Icc s T) (v k)) J atTop
      (region ν r ×ˢ Icc s T)) :
    F05RelSchauder α (region ν r) (Icc s T) vLim C := by
  let X := region ν r
  let I := Icc s T
  have hX : UniqueDiffOn ℝ X := F05_region_uniqueDiffOn ν hr
  have hClosure : closure (interior X) = X := F05_region_closure_interior ν hr
  have hVC : ContinuousOn vLim (X ×ˢ I) :=
    hLim.continuousOn (Frequently.of_forall (fun k => (hv k).1.1))
  have hGC : ContinuousOn G (X ×ˢ I) :=
    hGLim.continuousOn (Frequently.of_forall (fun k => (hv k).1.2.1))
  have hHC : ContinuousOn H (X ×ˢ I) :=
    hHLim.continuousOn (Frequently.of_forall (fun k => (hv k).1.2.2.1))
  have hJC : ContinuousOn J (X ×ˢ I) :=
    hJLim.continuousOn (Frequently.of_forall (fun k => (hv k).1.2.2.2.1))
  have hFirst (t : ℝ) (ht : t ∈ I) (x : Space n) (hx : x ∈ X) :
      HasFDerivWithinAt (fun y => vLim (y,t)) (G (x,t)) X x := by
    apply F05_uniform_derivative_closed_convex (F05_region_convex ν r) hClosure
      (fun k => (hv k).1.2.2.2.2.1 t ht |>.continuousOn)
      (fun k => (hv k).1.2.1.comp
        (continuous_id.prodMk continuous_const).continuousOn (fun y hy => ⟨hy,ht⟩))
      (fun k y hy => ((hv k).1.2.2.2.2.1 t ht y hy).differentiableWithinAt
        (by norm_num) |>.hasFDerivWithinAt)
      ((hLim.comp (fun y => (y,t))).mono (fun y hy => ⟨hy,ht⟩))
      ((hGLim.comp (fun y => (y,t))).mono (fun y hy => ⟨hy,ht⟩)) hx
  have hSecond (t : ℝ) (ht : t ∈ I) (x : Space n) (hx : x ∈ X) :
      HasFDerivWithinAt (fun y => G (y,t)) (H (x,t)) X x := by
    apply F05_uniform_derivative_closed_convex (F05_region_convex ν r) hClosure
      (fun k => (hv k).1.2.1.comp
        (continuous_id.prodMk continuous_const).continuousOn (fun y hy => ⟨hy,ht⟩))
      (fun k => (hv k).1.2.2.1.comp
        (continuous_id.prodMk continuous_const).continuousOn (fun y hy => ⟨hy,ht⟩))
      (fun k y hy => ((((hv k).1.2.2.2.2.1 t ht).fderivWithin hX (m := 1)
        (by norm_num)).differentiableOn (by norm_num) y hy).hasFDerivWithinAt)
      ((hGLim.comp (fun y => (y,t))).mono (fun y hy => ⟨hy,ht⟩))
      ((hHLim.comp (fun y => (y,t))).mono (fun y hy => ⟨hy,ht⟩)) hx
  have hTime (x : Space n) (hx : x ∈ X) (t : ℝ) (ht : t ∈ I) :
      HasDerivWithinAt (fun a => vLim (x,a)) (J (x,t)) I t := by
    apply F05_uniform_deriv_closed_interval hsT
      (fun k => (hv k).1.1.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun a ha => ⟨hx,ha⟩))
      (fun k => (hv k).1.2.2.2.1.comp
        (continuous_const.prodMk continuous_id).continuousOn (fun a ha => ⟨hx,ha⟩))
      (fun k a ha => ((hv k).1.2.2.2.2.2 (x,a) ⟨hx,ha⟩).hasDerivWithinAt)
      ((hLim.comp (fun a => (x,a))).mono (fun a ha => ⟨hx,ha⟩))
      ((hJLim.comp (fun a => (x,a))).mono (fun a ha => ⟨hx,ha⟩)) ht
  have hD (z : Point n) (hz : z ∈ X ×ˢ I) : F05RelD X vLim z = G z :=
    (hFirst z.2 hz.2 z.1 hz.1).fderivWithin (hX z.1 hz.1)
  have hDD (z : Point n) (hz : z ∈ X ×ˢ I) : F05RelDD X vLim z = H z := by
    rw [F05RelDD,fderivWithin_congr (fun x hx => hD (x,z.2) ⟨hx,hz.2⟩) (hD z hz)]
    exact (hSecond z.2 hz.2 z.1 hz.1).fderivWithin (hX z.1 hz.1)
  have hDt (z : Point n) (hz : z ∈ X ×ˢ I) : F05RelT I vLim z = J z :=
    (hTime z.1 hz.1 z.2 hz.2).derivWithin (uniqueDiffOn_Icc hsT z.2 hz.2)
  have hSpatial (t : ℝ) (ht : t ∈ I) : ContDiffOn ℝ 2 (fun x => vLim (x,t)) X := by
    have hGOne : ContDiffOn ℝ 1 (fun x => G (x,t)) X := by
      apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (n := 0) hX).mpr
      refine ⟨by simp,fun x => H (x,t),?_,hSecond t ht⟩
      exact contDiffOn_zero.mpr (hHC.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun x hx => ⟨hx,ht⟩))
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (n := 1) hX).mpr
    exact ⟨by simp,fun x => G (x,t),hGOne,hFirst t ht⟩
  refine ⟨⟨hVC,hGC.congr hD,hHC.congr hDD,hJC.congr hDt,hSpatial,
    fun z hz => (hTime z.1 hz.1 z.2 hz.2).differentiableWithinAt⟩,?_,?_,?_⟩
  · have hLow := F05_holderBound_pointwise_limit (fun k => (hv k).2.1)
      (fun z hz => (hLim.tendsto_at hz).prodMk_nhds (hGLim.tendsto_at hz))
    apply holderBound_congr_on hLow
    intro z hz
    change (vLim z,G z) = (vLim z,F05RelD X vLim z)
    rw [hD z hz]
  · exact holderBound_congr_on
      (F05_holderBound_pointwise_limit (fun k => (hv k).2.2.1) (fun z hz => hHLim.tendsto_at hz))
      (fun z hz => (hDD z hz).symm)
  · exact holderBound_congr_on
      (F05_holderBound_pointwise_limit (fun k => (hv k).2.2.2) (fun z hz => hJLim.tendsto_at hz))
      (fun z hz => (hDt z hz).symm)

end Yau.Proofs.F05Aux
