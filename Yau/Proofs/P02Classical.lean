import Yau.Proofs.P02MetricCoercivity
import Yau.Proofs.P02Quadratic
import Yau.Proofs.P02CircleSupports
import Yau.Proofs.P02CircleLimit
import Yau.Proofs.P02RayTail

noncomputable section
open Filter Metric
open scoped Topology ContDiff Manifold Matrix ComplexOrder NNReal

namespace Yau.NodeProofs.P02Aux
open Yau Yau.Blueprint Yau.LeafProofs L12Aux L23Aux L22Aux

theorem busemann_classicalStrictPsh {n : ℕ} (X : KahlerManifold n) (o : Pt X)
    (ray : ℝ≥0 → Pt X) (h0 : ray 0=o)
    (hdist : ∀ s t, distFrom X.metric.form (ray s) (ray t) = |(t : ℝ)-(s : ℝ)|)
    (b : Pt X → ℝ)
    (hlim : ∀ x, Tendsto (fun j : ℕ => signedDistanceSeq X o ray j x) atTop (𝓝 (b x)))
    (hlip : ∀ x y, |b x-b y| ≤ distFrom X.metric.form x y) :
    LeafCandidates.ClassicalStrictPsh b := by
  have hbc : Continuous b := busemann_continuous X b hlip
  refine ⟨hbc,?_⟩
  intro p
  obtain ⟨r,m,hr,hm,hrtarget,hmetric⟩ := exists_chart_metric_lower_ball X.metric p
  let O := ball (chartPt p p) r
  have hOtarget : O ⊆ chartTarget p := fun _ hz => hrtarget (ball_subset_closedBall hz)
  have hIc : ContinuousOn (chartInv p) (chartTarget p) := continuousOn_extChartAt_symm p
  let K : Set (Pt X) := chartInv p '' closedBall (chartPt p p) r
  have hK : IsCompact K := (isCompact_closedBall _ _).image_of_continuousOn (hIc.mono hrtarget)
  obtain ⟨R,hRabs⟩ := hK.exists_bound_of_continuousOn (continuous_distFrom X.metric o).continuousOn
  have hR : ∀ x ∈ K, inducedDistance X.metric.form o x ≤ R := by
    intro x hx
    simpa only [distFrom,lengthDist,Real.norm_eq_abs,
      abs_of_nonneg (X.metric.induced_distance_nonneg o x)] using hRabs x hx
  obtain ⟨ε,L,hε,hL,hsupport⟩ := exists_uniform_distance_lower_support X o R
  obtain ⟨N,hN⟩ := exists_common_ray_tail X o ray h0 hdist K R L hR
  let a := ε*m/2
  have ha : 0 < a := by dsimp [a]; positivity
  let τ : ComplexVector n → ℝ := fun z => a*‖z‖^2
  have hτ : ContDiff ℝ ∞ τ := contDiff_const.mul (contDiff_norm_sq ℝ)
  let F : ℕ → ComplexVector n → ℝ := fun j z =>
    inChart p (signedDistanceSeq X o ray j) z-τ z
  let B : ComplexVector n → ℝ := fun z => inChart p b z-τ z
  have hseqc (j : ℕ) : Continuous (signedDistanceSeq X o ray j) :=
    busemann_continuous X _ (signedDistanceSeq_lipschitz X o ray j)
  have hFc (j : ℕ) : ContinuousOn (F j) O :=
    ((hseqc j).comp_continuousOn (hIc.mono hOtarget)).sub hτ.continuous.continuousOn
  have hBc : ContinuousOn B O :=
    (hbc.comp_continuousOn (hIc.mono hOtarget)).sub hτ.continuous.continuousOn
  have hpsh : ∀ᶠ j in atTop, LeafCandidates.ComplexLinePshOn O (F j) := by
    filter_upwards [eventually_ge_atTop N] with j hj
    apply complexLinePshOn_of_lower_supports O (F j) (hFc j)
    intro z hz
    have hzcl : z ∈ closedBall (chartPt p p) r := ball_subset_closedBall hz
    let x := chartInv p z
    have hxK : x ∈ K := ⟨z,hzcl,rfl⟩
    obtain ⟨s,hsc,hs0,hsbelow,hslevi⟩ := hsupport x (hR x hxK) (ray j) (hN j hj x hxK)
    have HS := inChart_support_transport X.metric.form p x (hrtarget hzcl) rfl s ε hsc hslevi
    let C := inducedDistance X.metric.form o (ray j)
    let t : ComplexVector n → ℝ := fun u => (C+inChart p s u)+(-a)*‖u‖^2
    have htc : ContDiffAt ℝ 2 t z :=
      (contDiffAt_const.add HS.1).add (contDiffAt_const.mul (contDiff_norm_sq ℝ).contDiffAt)
    have hInv : Tendsto (chartInv p) (𝓝 z) (𝓝 x) :=
      (continuousAt_extChartAt_symm'' (hrtarget hzcl)).tendsto
    refine ⟨t,htc,?_,?_,?_⟩
    · change (C+s x)+(-a)*‖z‖^2 =
        (inducedDistance X.metric.form o (ray j)-inducedDistance X.metric.form x (ray j))-a*‖z‖^2
      rw [hs0,X.metric.induced_distance_symm (ray j) x]
      dsimp only [C]
      ring
    · filter_upwards [hInv.eventually hsbelow] with u hu
      change (C+s (chartInv p u))+(-a)*‖u‖^2 ≤
        (inducedDistance X.metric.form o (ray j)-
          inducedDistance X.metric.form (chartInv p u) (ray j))-a*‖u‖^2
      rw [X.metric.induced_distance_symm (chartInv p u) (ray j)]
      dsimp only [C]
      linarith
    · intro v
      change 0 ≤ complexLeviQuadratic
        (fun u => (C+inChart p s u)+(-a)*‖u‖^2) z v
      rw [complexLeviQuadratic_add (contDiffAt_const.add HS.1)
        (contDiffAt_const.mul (contDiff_norm_sq ℝ).contDiffAt),
        complexLeviQuadratic_add contDiffAt_const HS.1,
        complexLeviQuadratic_const_mul (contDiff_norm_sq ℝ).contDiffAt,
        complexLeviQuadratic_norm_sq]
      have hconst : complexLeviQuadratic (fun _ : ComplexVector n => C) z v = 0 := by
        simp [complexLeviQuadratic]
      rw [hconst,zero_add]
      have HH := HS.2 v
      have HM := mul_le_mul_of_nonneg_left (hmetric z hzcl v) hε.le
      dsimp only [a]
      nlinarith [mul_nonneg (mul_nonneg hε.le hm.le) (sq_nonneg ‖v‖)]
  have hunif : ∀ J : Set (ComplexVector n), IsCompact J → J ⊆ O →
      TendstoUniformlyOn F B atTop J := by
    intro J hJ hJO
    let KJ := chartInv p '' J
    have hKJ : IsCompact KJ := hJ.image_of_continuousOn
      (hIc.mono (fun z hz => hOtarget (hJO hz)))
    have H := (busemann_uniformOn_compact X o ray b hlim hlip KJ hKJ).comp (chartInv p)
    have HJ := H.mono (fun z hz => (⟨z,hz,rfl⟩ : chartInv p z ∈ KJ))
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro η hη
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp HJ) η hη] with j hj
    intro z hz
    have HH := hj z hz
    simpa only [F,B,inChart,Real.dist_eq,Function.comp_def,sub_sub_sub_cancel_right] using HH
  refine ⟨O,isOpen_ball,mem_ball_self hr,hOtarget,τ,hτ.contDiffOn,
    quadratic_levi_posDef a ha (chartPt p p),?_⟩
  exact complexLinePshOn_uniformLimit O F B hBc hpsh hunif

end Yau.NodeProofs.P02Aux
