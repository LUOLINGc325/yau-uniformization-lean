import Yau.Proofs.F05HolderInitialBarrier
import Yau.Proofs.F05HolderFaceJets

/-! A physical-face modulus with an amplitude correction on the artificial
sphere. All constants precede the moving endpoint and coefficient fields. -/

open Set
noncomputable section
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
open Yau.LeafProofs.L16ExpBoundaryAux
variable {n : ℕ}
local instance f05_faceBarrierHessianGroup :
    NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance f05_faceBarrierHessianSpace :
    NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

theorem F05_buffered_face_error (j : RIdx n)
    {A₀ b₀ H W₀ ν upper : ℝ} (hν : 0 < ν) (hA₀ : 0 ≤ A₀) (hb₀ : 0 ≤ b₀)
    (hH : 0 < H) (hW₀ : 0 < W₀) :
    ∃ Kb : ℝ, 0 < Kb ∧ ∀ (T : ℝ), 0 < T →
      ∀ (a : Point n → Mat n) (b : Point n → RIdx n → ℝ) (u : Point n → ℝ),
      ContinuousOn u (cylinder (region (some j) 2) 0 T) →
      (∀ z ∈ F05CapOpen (some j) 2 ×ˢ Ioo 0 T,
        ContDiffAt ℝ 2 (fun x => u (x,z.2)) z.1) →
      (∀ z ∈ F05CapOpen (some j) 2 ×ˢ Ioo 0 T,
        DifferentiableAt ℝ (fun t => u (z.1,t)) z.2) →
      Elliptic (F05CapOpen (some j) 2 ×ˢ Ioo 0 T) a ν upper →
      (∀ z ∈ F05CapOpen (some j) 2 ×ˢ Ioo 0 T, ∀ i l, |a z i l| ≤ A₀) →
      (∀ z ∈ F05CapOpen (some j) 2 ×ˢ Ioo 0 T, ∀ i, |b z i| ≤ b₀) →
      (∀ x ∈ region (some j) 2, u (x,0) = 0) →
      (∀ x ∈ frontier (F05FlatOpen (some j)) ∩ Metric.ball 0 2,
        ∀ t ∈ Icc 0 T, u (x,t) = 0) →
      (∀ z ∈ cylinder (region (some j) 2) 0 T, |u z| ≤ W₀) →
      (∀ z ∈ F05CapOpen (some j) 2 ×ˢ Ioo 0 T,
        |linearOp (cylinder (region (some j) 2) 0 T) a b u z| ≤ H) →
      ∀ x ∈ region (some j) (7/4), ∀ t ∈ Icc 0 T,
        |u (x,t)| ≤ Kb*F05FaceGauge (some j) x := by
  classical
  let s := F05FaceGauge (some j)
  let r : ℝ := 1/8
  have hr : 0 < r := by norm_num [r]
  let Lρ : ℝ := (∑ _i : RIdx n, ∑ _l : RIdx n, A₀*0)+
    ∑ _i : RIdx n, b₀*1
  have hLρ : 0 ≤ Lρ := by dsimp [Lρ]; positivity
  obtain ⟨κ,μ,hκ,hμ,hgap,hμeq⟩ :=
    exists_definingBarrier_constants (S₀ := r) hν zero_lt_one hLρ
  let c := W₀/r^2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  let C : ℝ := (∑ _i : RIdx n, ∑ _l : RIdx n, A₀*2)+
    ∑ _i : RIdx n, b₀*(2*r)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let K₀ := (H+c*C+1)/μ
  have hK₀ : 0 < K₀ := by dsimp [K₀]; positivity
  have hConst : H+c*C ≤ K₀*μ := by
    have hEq : K₀*μ = H+c*C+1 := by dsimp [K₀]; field_simp
    linarith
  let Kb := 1+K₀*κ+W₀/r
  have hKb : 0 < Kb := by dsimp [Kb]; positivity
  refine ⟨Kb,hKb,?_⟩
  intro T hT a b u hu hs ht he hA hb hi hl hsup hop x hx t htm
  have hx2 : x ∈ region (some j) 2 := F05_region_mono (by norm_num) hx
  have hxcl : x ∈ closure (F05FlatOpen (some j)) := by
    rw [F05FlatOpen_closure]
    exact hx.2
  have hsx : 0 ≤ s x := F05FaceGauge_nonneg hxcl
  by_cases hfar : r ≤ s x
  · have hAmp := hsup (x,t) ⟨hx2,htm⟩
    have hRatio := mul_le_mul_of_nonneg_left hfar (show 0 ≤ W₀/r by positivity)
    have hCancel : W₀/r*r = W₀ := div_mul_cancel₀ W₀ hr.ne'
    rw [hCancel] at hRatio
    have hCoeff : W₀/r ≤ Kb := by dsimp [Kb]; linarith [mul_pos hK₀ hκ]
    exact hAmp.trans (hRatio.trans (mul_le_mul_of_nonneg_right hCoeff hsx))
  let y := F05FaceProjection j x
  have hyNorm : ‖y‖ ≤ (7/4 : ℝ) := (F05FaceProjection_norm j x).trans hx.1
  have hsy : s y = 0 := by
    exact neg_eq_zero.mpr (F05FaceProjection_coordinate j x)
  have hxy : ‖x-y‖ = s x := F05FaceProjection_distance j x hx.2
  have hxr : ‖x-y‖ < r := by rw [hxy]; exact lt_of_not_ge hfar
  let D := F05FlatOpen (some j) ∩ Metric.ball y r
  let W := combinedBarrier s κ K₀ c y
  have hD : IsOpen D := (F05FlatOpen_isOpen (some j)).inter Metric.isOpen_ball
  have hcl : closure D ⊆ region (some j) 2 := F05_cap_closure_subset_two (some j) hyNorm
  have hDsmall : D ⊆ F05CapOpen (some j) 2 := by
    intro z hz
    have hzy : ‖z-y‖ < r := by simpa only [Metric.mem_ball,dist_eq_norm] using hz.2
    have hn := norm_add_le (z-y) y
    rw [sub_add_cancel] at hn
    refine ⟨hz.1,?_⟩
    rw [Metric.mem_ball,dist_zero_right]
    dsimp only [r] at hzy
    linarith
  have hSub : D ×ˢ Ioo 0 T ⊆ F05CapOpen (some j) 2 ×ˢ Ioo 0 T :=
    fun _ hz => ⟨hDsmall hz.1,hz.2⟩
  have hsmooth (z : Space n) : ContDiffAt ℝ 2 s z :=
    (F05FaceGauge_contDiff (some j)).contDiffAt.of_le (by simp)
  have hsnonneg (z : Space n) (hz : z ∈ closure D) : 0 ≤ s z :=
    F05FaceGauge_nonneg (closure_inter_ball_subset (F05FlatOpen (some j)) y r hz).1
  have hWnonneg (z : Space n) (hz : z ∈ closure D) : 0 ≤ W z :=
    combinedBarrier_nonneg hκ.le hK₀.le hc (hsnonneg z hz)
  have hWc : ContinuousOn W (closure D) :=
    fun z _ => (combinedBarrier_contDiffAt (hsmooth z)).continuousAt.continuousWithinAt
  have hWs : ∀ z ∈ D, ContDiffAt ℝ 2 W z := fun z _ =>
    combinedBarrier_contDiffAt (hsmooth z)
  have hbar : ∀ z ∈ D ×ˢ Ioo 0 T, H ≤ stationaryOp (a z) (b z) W z.1 := by
    intro z hz
    have hzy : ‖z.1-y‖ ≤ r :=
      (show ‖z.1-y‖ < r by simpa only [Metric.mem_ball,dist_eq_norm] using hz.1.2).le
    have hS : s z.1 ≤ r := (F05FaceGauge_le_dist j hsy).trans hzy
    have hGrad : ‖fderiv ℝ s z.1‖ = 1 := F05FaceGauge_fderiv_norm j z.1
    have hHess : ‖fderiv ℝ (fderiv ℝ s) z.1‖ ≤ 0 := by
      simp only [s,F05FaceGauge_secondFDeriv,norm_zero,le_refl]
    have hL : |(∑ i, ∑ l, a z i l*fderiv ℝ (fderiv ℝ s) z.1 (realVec i) (realVec l))+
        ∑ i, b z i*d s z.1 i| ≤ Lρ :=
      definingFunction_contraction_abs_bound hA₀ hb₀ hGrad.le hHess
        (hA z (hSub hz)) (hb z (hSub hz))
    have hJ : μ ≤ stationaryOp (a z) (b z) (definingBarrier s κ) z.1 := by
      rw [hμeq]
      exact definingBarrier_operator_lower_bound (hsmooth z.1) hκ hν zero_lt_one
        hgap hGrad.ge hS (fun v => ((he.2.2 z (hSub hz)).2 v).1) hL
    have hSphere : |stationaryOp (a z) (b z) (sphereBarrier y) z.1| ≤ C :=
      sphereBarrier_operator_abs_bound hA₀ hb₀ (hA z (hSub hz)) (hb z (hSub hz)) hzy
    exact combinedBarrier_operator_lower_bound (hsmooth z.1) hK₀.le hc hJ hSphere hConst
  have hbound := stationary_barrier_abs (O := D) (b := b) hD
    (F05_cap_closure_isCompact (some j) y r) hT
    (hu.mono (fun _ hz => ⟨hcl hz.1,hz.2⟩))
    (fun z hz => hs z (hSub hz)) (fun z hz => ht z (hSub hz))
    ⟨he.1,he.2.1,fun z hz => he.2.2 z (hSub hz)⟩ hWc hWs
    (by intro z hz; rw [hi z (hcl hz),abs_zero]; exact hWnonneg z hz)
    (by
      intro z hz v hv
      rcases F05_cap_frontier_cases hz with hface | hsphere
      · have hnorm : ‖z‖ < 2 := by
          have hzNorm := (F05_cap_closure_subset_region (some j) hyNorm) hz.1
          dsimp only [r] at hzNorm
          linarith [hzNorm.1]
        rw [hl z ⟨hface,by simpa only [Metric.mem_ball,dist_zero_right] using hnorm⟩ v hv,
          abs_zero]
        exact hWnonneg z hz.1
      · exact (hsup (z,v) ⟨hcl hz.1,hv⟩).trans
          (combinedBarrier_on_sphere hκ.le hK₀.le hr (hsnonneg z hz.1) hsphere.2))
    (by
      intro z hz
      rw [F05_linearOp_cylinder_space_eq a b u (subset_closure hz.1)
        (hcl (subset_closure hz.1)) ⟨hz.2.1.le,hz.2.2.le⟩]
      exact hop z (hSub hz)) hbar
  have hxD : x ∈ closure D := Metric.isOpen_ball.closure_inter
    ⟨hxcl,by simpa only [Metric.mem_ball,dist_eq_norm] using hxr⟩
  have hLinear := combinedBarrier_le_linear (M₁ := 1) hκ.le hK₀.le hW₀.le hr
    (by simpa only [one_mul] using F05FaceGauge_le_dist j hsy) hxr.le
  have hOut := (hbound (x,t) ⟨hxD,htm⟩).trans hLinear
  rw [hxy] at hOut
  apply hOut.trans
  dsimp only [Kb]
  nlinarith

end Yau.Proofs.F05Aux
