import Yau.LeafProofs.L05AutonomousGradientFromMollifierBasic
import Yau.LeafProofs.L05AutonomousSpatialGradient
import Yau.LeafProofs.L05AutonomousTimeIncrements

noncomputable section
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius Interval BoundedContinuousFunction
set_option maxHeartbeats 2600000
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- Actual mollifier Hessian bounds give the original field its true spatial C1,1 gradient. -/
theorem auto_gradient_from_spatial_mollifiers (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ, 0 ≤ B → ∀ w : Point n →ᵇ ℝ,
      UniformContinuous (w : Point n → ℝ) → ‖w‖ ≤ 1 →
      (∀ (eps : ℝ) (heps : 0 < eps), eps < 1/256 →
        ∀ p ∈ autoClosed (0 : Space n) (45/64) 0,
          ‖secondFDerivMatrix (fun x => autoSpatialMollify eps heps w (x,p.2)) p.1‖ ≤ B) →
      ContinuousOn (spatialD w) (autoClosed (0 : Space n) (5/8) 0) ∧
      (∀ p ∈ autoClosed (0 : Space n) (5/8) 0, ‖spatialD w p‖ ≤ C*(1+B)) ∧
      (∀ t ∈ Icc (-(5/8 : ℝ)^2) 0, ∀ x ∈ closedBall (0 : Space n) (5/8),
        HasFDerivAt (fun y => w (y,t)) (spatialD w (x,t)) x) ∧
      (∀ t ∈ Icc (-(5/8 : ℝ)^2) 0, ∀ x ∈ closedBall (0 : Space n) (5/8),
        ∀ y ∈ closedBall (0 : Space n) (5/8),
          ‖spatialD w (x,t)-spatialD w (y,t)‖ ≤ C*B*‖x-y‖) ∧
      (∀ t ∈ Icc (-(5/8 : ℝ)^2) 0, ∀ x ∈ closedBall (0 : Space n) (5/8),
        ∀ y ∈ closedBall (0 : Space n) (5/8),
          |w (y,t)-w (x,t)-spatialD w (x,t) (y-x)| ≤ C*B*‖y-x‖^2) ∧
      (∀ t ∈ Icc (-(5/8 : ℝ)^2) 0, ∀ x ∈ closedBall (0 : Space n) (5/8),
        ∀ y ∈ closedBall (0 : Space n) (5/8),
          w (y,t)-w (x,t) = ∫ s in (0 : ℝ)..1, spatialD w (x+s • (y-x),t) (y-x)) ∧
      TendstoUniformlyOn (fun j => spatialD
        (autoSpatialMollify (autoDyadicStep (1/512) j)
          (auto_dyadicStep_pos (by norm_num) j) w))
        (spatialD w) atTop (autoClosed (0 : Space n) (5/8) 0) := by
  obtain ⟨C,hC,hGeneric⟩ := autonomous_spatial_gradient_limit n (5/8) (45/64)
    (-(5/8 : ℝ)^2) 0 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C,hC,?_⟩
  intro B hB w hw hw1 hHessian
  let eps : ℕ → ℝ := autoDyadicStep (1/512)
  let epsPos (j : ℕ) : 0 < eps j := auto_dyadicStep_pos (by norm_num) j
  let f (j : ℕ) : Point n → ℝ := autoSpatialMollify (eps j) (epsPos j) w
  let K : Set (Point n) := spatialGradientCylinder (Space n) (5/8) (-(5/8 : ℝ)^2) 0
  let Q : Set (Point n) := spatialGradientCylinder (Space n) (45/64) (-(5/8 : ℝ)^2) 0
  have hepsSmall (j : ℕ) : eps j < 1/256 :=
    (auto_dyadicStep_le (by norm_num : (0 : ℝ) ≤ 1/512) j).trans_lt (by norm_num)
  have hQ : ∀ p ∈ Q, p ∈ autoClosed (0 : Space n) (45/64) 0 := by
    intro p hp
    refine ⟨hp.1,?_,hp.2.2⟩
    have ht : -(5/8 : ℝ)^2 ≤ p.2 := hp.2.1
    change (0 : ℝ)-(45/64)^2 ≤ p.2
    linarith only [ht]
  have hFrob (j : ℕ) (p : Point n) (hp : p ∈ Q) :
      ‖secondFDerivMatrix (fun x => f j (x,p.2)) p.1‖ ≤ B :=
    hHessian (eps j) (epsPos j) (hepsSmall j) p (hQ p hp)
  have hGradC (j : ℕ) : ContinuousOn (spatialGradientOf (f j)) Q := by
    change ContinuousOn (spatialD (autoSpatialMollify (eps j) (epsPos j) w)) Q
    exact (autoSpatialMollify_spatialD_continuous (eps j) (epsPos j) w hw).continuousOn
  have hUniform : TendstoUniformlyOn f w atTop Q :=
    (autoSpatialMollify_uniform w hw eps epsPos (auto_dyadicStep_tendsto (1/512))).tendstoUniformlyOn
  obtain ⟨G,hCont,hGradUniform,hNorm,hNative,hLip,hRemainder,hFTC⟩ :=
    hGeneric 1 B (by norm_num) hB w w.continuous.continuousOn f
      (fun j => (autoSpatialMollify_continuous (eps j) (epsPos j) w hw).continuousOn)
      hGradC (fun j t _ => autoSpatialMollify_spatial_contDiff (eps j) (epsPos j) w hw t)
      (fun j p _ => (autoSpatialMollify_abs_le (eps j) (epsPos j) w hw p).trans hw1)
      hFrob hUniform
  have hEq : EqOn G (spatialD w) K := by
    intro p hp
    change G p = fderiv ℝ (fun x => w (x,p.2)) p.1
    exact (hNative p.2 hp.2 p.1 hp.1).fderiv.symm
  have hEqPoint (p : Point n) (hp : p ∈ K) : G p = spatialD w p := hEq hp
  have hActualCont : ContinuousOn (spatialD w) K := hCont.congr hEq.symm
  have hActualNorm : ∀ p ∈ K, ‖spatialD w p‖ ≤ C*(1+B) := by
    intro p hp
    rw [← hEqPoint p hp]
    exact hNorm p hp
  have hActualNative : ∀ t ∈ Icc (-(5/8 : ℝ)^2) 0,
      ∀ x ∈ closedBall (0 : Space n) (5/8),
        HasFDerivAt (fun y => w (y,t)) (spatialD w (x,t)) x := by
    intro t ht x hx
    rw [← hEqPoint (x,t) ⟨hx,ht⟩]
    exact hNative t ht x hx
  have hActualLip : ∀ t ∈ Icc (-(5/8 : ℝ)^2) 0,
      ∀ x ∈ closedBall (0 : Space n) (5/8), ∀ y ∈ closedBall (0 : Space n) (5/8),
        ‖spatialD w (x,t)-spatialD w (y,t)‖ ≤ C*B*‖x-y‖ := by
    intro t ht x hx y hy
    simpa only [hEqPoint (x,t) ⟨hx,ht⟩,hEqPoint (y,t) ⟨hy,ht⟩] using hLip t ht x hx y hy
  have hActualRemainder : ∀ t ∈ Icc (-(5/8 : ℝ)^2) 0,
      ∀ x ∈ closedBall (0 : Space n) (5/8), ∀ y ∈ closedBall (0 : Space n) (5/8),
        |w (y,t)-w (x,t)-spatialD w (x,t) (y-x)| ≤ C*B*‖y-x‖^2 := by
    intro t ht x hx y hy
    simpa only [hEqPoint (x,t) ⟨hx,ht⟩] using hRemainder t ht x hx y hy
  have hActualFTC := spatialGradient_actual_segment_FTC (w : Point n → ℝ) (spatialD w)
    hActualCont hActualNative
  have hActualUniform : TendstoUniformlyOn (fun j => spatialD (f j)) (spatialD w) atTop K :=
    hGradUniform.congr_right hEq
  have hK : K = autoClosed (0 : Space n) (5/8) 0 := by
    simp only [K,spatialGradientCylinder,autoClosed,zero_sub]
  refine ⟨?_,?_,hActualNative,hActualLip,hActualRemainder,hActualFTC,?_⟩
  · simpa only [hK] using hActualCont
  · simpa only [hK] using hActualNorm
  · simpa only [hK,f,eps,epsPos] using hActualUniform

end Yau.LeafProofs.L05AutonomousAux
