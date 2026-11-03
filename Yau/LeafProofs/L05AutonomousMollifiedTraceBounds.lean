import Yau.LeafProofs.L05AutonomousEllipsoidBounds
import Yau.LeafProofs.L05AutonomousMollifierEllipsoid
import Yau.LeafProofs.L05AutonomousEllipsoidTraceLimit

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius BoundedContinuousFunction
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- The original positive means control actual smooth Hessian traces uniformly in the smoothing scale. -/
theorem auto_uniform_mollified_trace :
    ∀ n : ℕ, 0 < n → ∀ ell L : ℝ, 0 < ell → ell ≤ L →
    ∃ C : ℝ, 0 < C ∧
      ∀ F : Sym n → ℝ, Continuous F → globalElliptic F ell L → ConcaveOn ℝ univ F → F 0=0 →
      ∃ A∈slopeSet n ell L,
        ∀ u : Point n → ℝ, ContinuousOn u (unitClosed n) → (∀ p∈unitClosed n, |u p|≤ 1) →
        viscositySolution (unitOpen n) (fun H _ => F H) (fun _ => 0) u →
        ∃ w : Point n →ᵇ ℝ, EqOn w u (unitClosed n) ∧ UniformContinuous (w : Point n → ℝ) ∧
          HasCompactSupport (w : Point n → ℝ) ∧ ‖w‖ ≤ 1 ∧
          ∀ (eps : ℝ) (heps : 0 < eps), eps < 1/64 → ∀ p∈autoClosed (0 : Space n) (3/4) 0,
            |Matrix.trace ((A : Mat n)*secondFDerivMatrix
              (fun x => autoSpatialMollify eps heps w (x,p.2)) p.1)| ≤ C := by
  intro n hn ell L hell hL
  obtain ⟨C₀,r₀,hC₀,hr₀,hForF⟩ := auto_uniform_ellipsoid_bounds n hn ell L hell hL
  let D : ℝ := 2*((2*n : ℝ)+2)
  have hD : 0 < D := by dsimp only [D];positivity
  refine ⟨C₀*D,mul_pos hC₀ hD,?_⟩
  intro F hF hE hConc h0
  obtain ⟨A,hA,S,hS,hSi,hST,hForU⟩ := hForF F hF hE hConc h0
  refine ⟨A,hA,?_⟩
  intro u hu hb hsol
  obtain ⟨w,hwu,hw,hcw,hwnorm⟩ := auto_compact_extension
    ((isCompact_closedBall _ _).prod isCompact_Icc : IsCompact (unitClosed n)) hu
  refine ⟨w,hwu,hw,hcw,hwnorm 1 (by norm_num) hb,?_⟩
  intro eps heps hepsSmall p hp
  let r0 := min r₀ (1/(64*(Real.sqrt L+1)))
  have hr0 : 0 < r0 := lt_min hr₀ (by positivity)
  apply auto_trace_bound_of_ellipsoid_second hn
    (autoSpatialMollify_spatial_contDiff eps heps w hw p.2) (A : Mat n) S hST hr0 p.1
  intro r hr hrr0
  let B := autoRadiusLinearEquiv S r hr
  have hRadius : Real.sqrt L*r ≤ 1/64 := by
    have hd : 0 < 64*(Real.sqrt L+1) := by positivity
    have hh : r*(64*(Real.sqrt L+1)) < 1 :=
      (lt_div_iff₀ hd).mp (hrr0.trans_le (min_le_right _ _))
    nlinarith only [hh,hr]
  have hB : ‖B.toContinuousLinearMap‖ ≤ 1/64 :=
    ((autoRadiusLinearEquiv_elliptic_bounds (hell.le.trans hL) S hS r hr).1.trans
      (by nlinarith only [hRadius]))
  let nu := autoMollifierMeasure n eps heps
  let : IsProbabilityMeasure nu := autoMollifierMeasure_isProbability n eps heps
  have hshift : ∀ y∈Metric.closedBall (0 : Space n) eps,
      |autoEllipsoidSecond B r w (p.1-y,p.2)| ≤ C₀ := by
    intro y hy
    have hx : ‖p.1‖ ≤ 3/4 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hp.1
    have hyNorm : ‖y‖ ≤ eps := by simpa only [Metric.mem_closedBall,dist_zero_right] using hy
    have hxy : ‖p.1-y‖ ≤ 49/64 := by
      have ht := norm_sub_le p.1 y
      linarith only [ht,hx,hyNorm,hepsSmall]
    have ht : -(3/4 : ℝ)^2 ≤ p.2 ∧ p.2 ≤ 0 := by simpa only [zero_sub,mem_Icc] using hp.2
    have hq : (p.1-y,p.2)∈autoClosed (0 : Space n) (49/64) 0 :=
      ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using hxy,
        by change (0 : ℝ)-(49/64)^2 ≤ p.2 ∧ p.2 ≤ 0;exact ⟨by linarith only [ht.1],ht.2⟩⟩
    have hqUnit : (p.1-y,p.2)∈unitClosed n :=
      ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using hxy.trans (by norm_num : (49/64 : ℝ) ≤ 1),
        by change (-1 : ℝ) ≤ p.2 ∧ p.2 ≤ 0;exact ⟨by linarith only [ht.1],ht.2⟩⟩
    have hbuffer (z : Space n) (hz : z∈Metric.closedBall (0 : Space n) (1/64)) :
        ((p.1-y)+z,p.2)∈unitClosed n := by
      have hzNorm : ‖z‖ ≤ 1/64 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
      refine ⟨?_,hqUnit.2⟩
      simp only [Metric.mem_closedBall,dist_zero_right]
      exact (norm_add_le _ _).trans ((add_le_add hxy hzNorm).trans (by norm_num))
    rw [auto_ellipsoid_second_congr hwu B hB r _ hqUnit hbuffer]
    exact hForU u hu hb hsol r hr (hrr0.trans_le (min_le_left _ _)) _ hq
  have hcomm := auto_mollify_ellipsoid_second B r eps heps w hw p
  have hNorm := norm_integral_le_of_norm_le_const (μ := nu)
    (f := fun y => autoEllipsoidSecond B r w (p.1-y,p.2)) (by
      filter_upwards [autoMollifierMeasure_closedBall_ae n eps heps] with y hy
      simpa only [Real.norm_eq_abs] using hshift y hy)
  have hBound : |autoEllipsoidSecond B r (autoSpatialMollify eps heps w) p| ≤ C₀ := by
    rw [hcomm.2]
    simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using hNorm
  exact hBound

end Yau.LeafProofs.L05AutonomousAux
