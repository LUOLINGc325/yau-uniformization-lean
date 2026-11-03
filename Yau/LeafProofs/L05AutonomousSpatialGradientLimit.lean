import Yau.LeafProofs.L05AutonomousSpatialGradientUniform
import Mathlib.Analysis.Calculus.Deriv.AffineMap

open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Interval
noncomputable section
set_option maxHeartbeats 2200000
namespace Yau.LeafProofs.L05AutonomousAux

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A slightly larger collar gives the original function its ambient spatial derivative. -/
theorem spatialGradient_limit_hasFDerivAt {r s a b : ℝ} (hrs : r < s)
    (f : ℕ → V × ℝ → ℝ) (u : V × ℝ → ℝ) (G : V × ℝ → (V →L[ℝ] ℝ))
    (hf : ∀ j, ∀ t ∈ Icc a b, ContDiff ℝ ∞ (fun x => f j (x, t)))
    (hu : TendstoUniformlyOn f u atTop (spatialGradientCylinder V s a b))
    (hG : TendstoUniformlyOn (fun j => spatialGradientOf (f j)) G atTop (spatialGradientCylinder V s a b)) :
    ∀ t ∈ Icc a b, ∀ x ∈ closedBall (0 : V) r,
      HasFDerivAt (fun y => u (y, t)) (G (x, t)) x := by
  intro t ht x hx
  have hmap : ball (0 : V) s ⊆ (fun y : V => (y,t)) ⁻¹' spatialGradientCylinder V s a b :=
    fun y hy => ⟨ball_subset_closedBall hy, ht⟩
  have hdu : TendstoUniformlyOn (fun j y => spatialGradientOf (f j) (y,t))
      (fun y => G (y,t)) atTop (ball (0 : V) s) := (hG.comp (fun y => (y,t))).mono hmap
  have hx' : x ∈ ball (0 : V) s := by
    have hxN : ‖x‖ ≤ r := by simpa using hx
    simpa using hxN.trans_lt hrs
  exact hasFDerivAt_of_tendstoUniformlyOn isOpen_ball hdu
    (fun j y _ => (hf j t ht).differentiable (by simp) y |>.hasFDerivAt)
    (fun y hy => hu.tendsto_at ⟨ball_subset_closedBall hy, ht⟩) hx'

/-- Lipschitz control of the actual gradient is preserved by its genuine pointwise limits. -/
theorem spatialGradient_limit_lipschitz {r R a b B : ℝ} (hrR : r ≤ R)
    (f : ℕ → V × ℝ → ℝ) (G : V × ℝ → (V →L[ℝ] ℝ))
    (hf : ∀ j, ∀ t ∈ Icc a b, ContDiff ℝ ∞ (fun x => f j (x, t)))
    (hH : ∀ j, ∀ p ∈ spatialGradientCylinder V R a b,
      ‖fderiv ℝ (fderiv ℝ (fun x => f j (x, p.2))) p.1‖ ≤ B)
    (hG : TendstoUniformlyOn (fun j => spatialGradientOf (f j)) G atTop (spatialGradientCylinder V r a b)) :
    ∀ t ∈ Icc a b, ∀ x ∈ closedBall (0 : V) r, ∀ y ∈ closedBall (0 : V) r,
      ‖G (x,t) - G (y,t)‖ ≤ B * ‖x-y‖ := by
  intro t ht x hx y hy
  have hlim := ((hG.tendsto_at (x := (y,t)) ⟨hy,ht⟩).sub (hG.tendsto_at (x := (x,t)) ⟨hx,ht⟩)).norm
  have hb : ∀ j, ‖spatialGradientOf (f j) (y,t) - spatialGradientOf (f j) (x,t)‖ ≤ B * ‖y-x‖ := by
    intro j
    exact spatialGradient_smooth_lipschitz (hf j t ht)
      (fun z hz => hH j (z,t) ⟨hz,ht⟩)
      (closedBall_subset_closedBall hrR hx) (closedBall_subset_closedBall hrR hy)
  simpa only [norm_sub_rev] using le_of_tendsto' hlim hb

/-- The actual quadratic remainder passes to the original function and actual gradient. -/
theorem spatialGradient_limit_remainder {r R a b B : ℝ} (hrR : r ≤ R) (hB : 0 ≤ B)
    (f : ℕ → V × ℝ → ℝ) (u : V × ℝ → ℝ) (G : V × ℝ → (V →L[ℝ] ℝ))
    (hf : ∀ j, ∀ t ∈ Icc a b, ContDiff ℝ ∞ (fun x => f j (x, t)))
    (hH : ∀ j, ∀ p ∈ spatialGradientCylinder V R a b,
      ‖fderiv ℝ (fderiv ℝ (fun x => f j (x, p.2))) p.1‖ ≤ B)
    (hu : TendstoUniformlyOn f u atTop (spatialGradientCylinder V R a b))
    (hG : TendstoUniformlyOn (fun j => spatialGradientOf (f j)) G atTop (spatialGradientCylinder V r a b)) :
    ∀ t ∈ Icc a b, ∀ x ∈ closedBall (0 : V) r, ∀ y ∈ closedBall (0 : V) r,
      |u (y,t)-u (x,t)-G (x,t) (y-x)| ≤ B*‖y-x‖^2 := by
  intro t ht x hx y hy
  have hxR := closedBall_subset_closedBall hrR hx
  have hyR := closedBall_subset_closedBall hrR hy
  have hDx : Tendsto (fun j => spatialGradientOf (f j) (x,t) (y-x)) atTop (𝓝 (G (x,t) (y-x))) :=
    ((ContinuousLinearMap.apply ℝ ℝ (y-x)).continuous.tendsto _).comp (hG.tendsto_at ⟨hx,ht⟩)
  have hlim := (((hu.tendsto_at (x := (y,t)) ⟨hyR,ht⟩).sub (hu.tendsto_at (x := (x,t)) ⟨hxR,ht⟩)).sub hDx).norm
  have hb : ∀ j, ‖f j (y,t)-f j (x,t)-spatialGradientOf (f j) (x,t) (y-x)‖ ≤ B*‖y-x‖^2 := by
    intro j
    simpa only [Real.norm_eq_abs, spatialGradientOf] using spatialGradient_smooth_remainder (hf j t ht) hB
      (fun z hz => hH j (z,t) ⟨hz,ht⟩) hxR hyR
  simpa only [Real.norm_eq_abs] using le_of_tendsto' hlim hb

/-- The scalar segment FTC follows from the actual native spatial derivative just identified. -/
theorem spatialGradient_actual_segment_FTC {r a b : ℝ} (u : V × ℝ → ℝ)
    (G : V × ℝ → (V →L[ℝ] ℝ)) (hG : ContinuousOn G (spatialGradientCylinder V r a b))
    (hD : ∀ t ∈ Icc a b, ∀ x ∈ closedBall (0 : V) r,
      HasFDerivAt (fun y => u (y,t)) (G (x,t)) x) :
    ∀ t ∈ Icc a b, ∀ x ∈ closedBall (0 : V) r, ∀ y ∈ closedBall (0 : V) r,
      u (y,t)-u (x,t) = ∫ s in (0 : ℝ)..1, G (x+s • (y-x),t) (y-x) := by
  intro t ht x hx y hy
  have hpath : MapsTo (AffineMap.lineMap x y : ℝ → V) (Icc 0 1) (closedBall (0 : V) r) :=
    (convex_closedBall (0 : V) r).mapsTo_lineMap hx hy
  have hpcont : Continuous (fun s : ℝ => (AffineMap.lineMap x y s,t)) := by
    simp only [AffineMap.lineMap_apply_module]
    fun_prop
  have hcont : ContinuousOn (fun s : ℝ => G (AffineMap.lineMap x y s,t) (y-x)) (Icc 0 1) :=
    (hG.comp hpcont.continuousOn (fun s hs => ⟨hpath hs, ht⟩)).clm_apply continuousOn_const
  have hint : IntervalIntegrable (fun s : ℝ => G (AffineMap.lineMap x y s,t) (y-x)) volume 0 1 :=
    hcont.intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun z => u (AffineMap.lineMap x y z,t))
        (G (AffineMap.lineMap x y s,t) (y-x)) s := by
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using hs
    exact (hD t ht _ (hpath hs')).comp_hasDerivAt s AffineMap.hasDerivAt_lineMap
  have he := (intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint).symm
  have hline (s : ℝ) : AffineMap.lineMap x y s = x+s • (y-x) := by
    rw [AffineMap.lineMap_apply_module']
    exact add_comm _ _
  simp only [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] at he
  simpa only [hline] using he

/-- The same buffered interpolation gives a uniform gradient budget before taking limits. -/
theorem spatialGradient_limit_sup {s R a b B M step : ℝ}
    (hstep : 0 < step) (hbuffer : s + step ≤ R) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (f : ℕ → V × ℝ → ℝ) (G : V × ℝ → (V →L[ℝ] ℝ))
    (hf : ∀ j, ∀ t ∈ Icc a b, ContDiff ℝ ∞ (fun x => f j (x,t)))
    (hH : ∀ j, ∀ p ∈ spatialGradientCylinder V R a b,
      ‖fderiv ℝ (fderiv ℝ (fun x => f j (x,p.2))) p.1‖ ≤ B)
    (hval : ∀ j, ∀ p ∈ spatialGradientCylinder V R a b, |f j p| ≤ M)
    (hG : TendstoUniformlyOn (fun j => spatialGradientOf (f j)) G atTop (spatialGradientCylinder V s a b)) :
    ∀ p ∈ spatialGradientCylinder V s a b, ‖G p‖ ≤ 2*M/step+2*B*step := by
  intro p hp
  have hlim := (hG.tendsto_at hp).norm
  apply le_of_tendsto' hlim
  intro j
  have hzero : ContDiff ℝ ∞ (fun _ : V => (0 : ℝ)) := contDiff_const
  have hb := spatialGradient_interpolation (hf j p.2 hp.2) hzero hstep hbuffer hB hM
    (fun z hz => hH j (z,p.2) ⟨hz,hp.2⟩)
    (fun z _ => by
      have hz : fderiv ℝ (fun _ : V => (0 : ℝ)) = fun _ => 0 :=
        funext (fun x => fderiv_const_apply 0)
      rw [hz, fderiv_const_apply]
      change ‖(0 : V →L[ℝ] (V →L[ℝ] ℝ))‖ ≤ B
      simpa only [ContinuousLinearMap.opNorm_zero] using hB)
    (fun z hz => by simpa using hval j (z,p.2) ⟨hz,hp.2⟩) hp.1
  simpa only [spatialGradientOf, fderiv_const_apply, sub_zero] using hb

end Yau.LeafProofs.L05AutonomousAux
