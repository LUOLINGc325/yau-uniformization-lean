import Yau.LeafProofs.L05AutonomousTimeDerivative
import Yau.LeafProofs.L05AutonomousMollifierSubtrace

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius BoundedContinuousFunction
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- The actual G theorem discharges every source FTC premise. The budget precedes F and u. -/
theorem auto_mollified_supporting_trace :
    ∀ n : ℕ, 0< n → ∀ ell L : ℝ, 0< ell → ell≤ L →
    ∃ C : ℝ, 0< C ∧ ∀ F : Sym n → ℝ, Continuous F → globalElliptic F ell L →
      ConcaveOn ℝ univ F → F 0=0 →
      ∃ A∈slopeSet n ell L, (∀ H, F H≤ tracePair A H) ∧
      ∀ u : Point n → ℝ, ContinuousOn u (unitClosed n) → (∀ p∈unitClosed n, |u p|≤ 1) →
      viscositySolution (unitOpen n) (fun H _ => F H) (fun _ => 0) u →
      ∃ w v : Point n →ᵇ ℝ,
        EqOn w u (unitClosed n) ∧ UniformContinuous (w : Point n → ℝ) ∧
        HasCompactSupport (w : Point n → ℝ) ∧ ‖w‖≤ 1 ∧
        UniformContinuous (v : Point n → ℝ) ∧ HasCompactSupport (v : Point n → ℝ) ∧ ‖v‖≤ C ∧
        (∀ eps : ℝ, 0< eps → eps< 1/32 →
          ∀ x∈Metric.closedBall (0 : Space n) (7/8), ∀ y∈Metric.closedBall (0 : Space n) eps,
          ∀ a∈Icc (-(7/8 : ℝ)^2) 0, ∀ b∈Icc (-(7/8 : ℝ)^2) 0,
            w (x-y,b)-w (x-y,a)=∫ t in a..b, v (x-y,t)) ∧
        (∀ (eps : ℝ) (heps : 0< eps), eps< 1/32 → ∀ p∈autoClosed (0 : Space n) (7/8) 0,
          -C≤ tracePair A (hessian (autoSpatialMollify eps heps w) p)) := by
  intro n hn ell L hell hL
  obtain ⟨delta,C,hd,hd1,hC,hG⟩ := auto_time_derivative n hn ell L hell hL
  refine ⟨C,hC,?_⟩
  intro F hF hE hConc h0
  obtain ⟨A,hA,hSupport⟩ := auto_supporting_slope hell hL hF hE hConc h0
  refine ⟨A,hA,hSupport,?_⟩
  intro u hu hbound hsol
  obtain ⟨V,hVc,hVbound,hVholder,hVPucci,hVFTC,hVtimeD⟩ := hG F hF hE h0 u hu hbound hsol
  have hUnitCompact : IsCompact (unitClosed n) := (isCompact_closedBall _ _).prod isCompact_Icc
  obtain ⟨w,hwu,hw,hcw,hwnorm⟩ := auto_compact_extension hUnitCompact hu
  obtain ⟨v,hvV,hv,hcv,hvnorm⟩ := auto_compact_extension (autoClosed_isCompact (0 : Space n) (15/16) 0) hVc
  have hw1 : ‖w‖≤ 1 := hwnorm 1 (by norm_num) hbound
  have hvC : ‖v‖≤ C := hvnorm C hC.le hVbound
  have hSourceFTC : ∀ eps : ℝ, 0< eps → eps< 1/32 →
      ∀ x∈Metric.closedBall (0 : Space n) (7/8), ∀ y∈Metric.closedBall (0 : Space n) eps,
      ∀ a∈Icc (-(7/8 : ℝ)^2) 0, ∀ b∈Icc (-(7/8 : ℝ)^2) 0,
        w (x-y,b)-w (x-y,a)=∫ t in a..b, v (x-y,t) := by
    intro eps heps hepsSmall x hx y hy a ha b hb
    have hxnorm : ‖x‖≤ 7/8 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hx
    have hynorm : ‖y‖≤ eps := by simpa only [Metric.mem_closedBall,dist_zero_right] using hy
    have hxynorm : ‖x-y‖≤ 15/16 := by
      have hh := norm_sub_le x y
      linarith only [hh,hxnorm,hynorm,hepsSmall]
    have hxy : x-y∈Metric.closedBall (0 : Space n) (15/16) := by
      simpa only [Metric.mem_closedBall,dist_zero_right] using hxynorm
    have hPointV (t : ℝ) (ht : t∈Icc (-(7/8 : ℝ)^2) 0) : (x-y,t)∈autoClosed (0 : Space n) (15/16) 0 :=
      ⟨hxy,by change (0 : ℝ)-(15/16)^2≤ t ∧ t≤ 0;exact ⟨by linarith only [ht.1],ht.2⟩⟩
    have hPointU (t : ℝ) (ht : t∈Icc (-(7/8 : ℝ)^2) 0) : (x-y,t)∈unitClosed n :=
      ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using hxynorm.trans (by norm_num : (15/16 : ℝ)≤ 1),
        by change (-1 : ℝ)≤ t ∧ t≤ 0;exact ⟨by linarith only [ht.1],ht.2⟩⟩
    rw [hwu (hPointU b hb),hwu (hPointU a ha)]
    rw [(hVFTC (x-y) hxy).2.2 a ⟨by linarith only [ha.1],ha.2⟩ b ⟨by linarith only [hb.1],hb.2⟩]
    apply intervalIntegral.integral_congr
    intro t ht
    have htJ : t∈Icc (-(7/8 : ℝ)^2) 0 :=
      ⟨(le_min ha.1 hb.1).trans ht.1,ht.2.trans (max_le ha.2 hb.2)⟩
    exact (hvV (hPointV t htJ)).symm
  refine ⟨w,v,hwu,hw,hcw,hw1,hv,hcv,hvC,hSourceFTC,?_⟩
  intro eps heps hepsSmall p hp
  have htrace := autoSpatialMollify_supporting_trace_lower hell hL hF hE hConc hu hsol.1 w v hw hv hwu
    (by norm_num : (0 : ℝ)< 7/8) heps (by linarith only [hepsSmall] : (7/8 : ℝ)+eps< 1)
    (hSourceFTC eps heps hepsSmall) A hSupport p hp
  exact (neg_le_neg hvC).trans htrace

end Yau.LeafProofs.L05AutonomousAux
