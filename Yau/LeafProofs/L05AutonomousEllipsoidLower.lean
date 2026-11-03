import Yau.LeafProofs.L05AutonomousBallMeanTransport
import Yau.LeafProofs.L05AutonomousMollifiedTraceLower
import Yau.LeafProofs.L05AutonomousEllipsoidScaling
import Yau.LeafProofs.L05AutonomousEllipsoidLimit
import Yau.LeafProofs.L05AutonomousCutoffEnergy

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius BoundedContinuousFunction
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- The original viscosity solution has uniformly bounded-below elliptic second means.
All constants and the radius threshold precede F and u, and the actual square root precedes u. -/
theorem auto_uniform_ellipsoid_lower :
    ∀ n : ℕ, 0< n → ∀ ell L : ℝ, 0< ell → ell≤ L →
    ∃ C r0 : ℝ, 0< C ∧ 0< r0 ∧
      ∀ F : Sym n → ℝ, Continuous F → globalElliptic F ell L → ConcaveOn ℝ univ F → F 0=0 →
      ∃ A∈slopeSet n ell L, ∃ S : Space n ≃L[ℝ] Space n,
        ‖S.toContinuousLinearMap‖≤ Real.sqrt L ∧ ‖S.symm.toContinuousLinearMap‖≤ (Real.sqrt ell)⁻¹ ∧
        (∀ H : Space n →L[ℝ] Space n →L[ℝ] ℝ,
          (∑ k : Yau.RIdx n, H (S (Yau.realVec k)) (S (Yau.realVec k)))=
            ∑ i, ∑ j, (A : Mat n) i j*H (Yau.realVec i) (Yau.realVec j)) ∧
        ∀ u : Point n → ℝ, ContinuousOn u (unitClosed n) → (∀ p∈unitClosed n, |u p|≤ 1) →
        viscositySolution (unitOpen n) (fun H _ => F H) (fun _ => 0) u →
        ∀ (r : ℝ) (hr : 0< r), r< r0 →
          ContinuousOn (autoEllipsoidSecond (autoRadiusLinearEquiv S r hr) r u) (autoClosed 0 (13/16) 0) ∧
          viscositySub (autoOpen 0 (13/16) 0) (fun H _ => pucciPlus ell L H) (fun _ => 0)
            (autoEllipsoidSecond (autoRadiusLinearEquiv S r hr) r u) ∧
          ∀ p∈autoClosed (0 : Space n) (13/16) 0, -C≤ autoEllipsoidSecond (autoRadiusLinearEquiv S r hr) r u p := by
  intro n hn ell L hell hL
  obtain ⟨C,hC,hTraceData⟩ := auto_mollified_supporting_trace n hn ell L hell hL
  let r0 : ℝ := 1/(64*(Real.sqrt L+1))
  have hr0 : 0< r0 := by dsimp only [r0];positivity
  refine ⟨C,r0,hC,hr0,?_⟩
  intro F hF hE hConc h0
  obtain ⟨A,hA,hSupport,hForU⟩ := hTraceData F hF hE hConc h0
  obtain ⟨S,hS,hSi,hST,hMean⟩ := auto_ball_mean_square_root_transport hn hell hL hA
  refine ⟨A,hA,S,hS,hSi,hST,?_⟩
  intro u hu hb hsol r hr hrr0
  obtain ⟨w,v,hwu,hw,hcw,hw1,hv,hcv,hvC,hSourceFTC,hTrace⟩ := hForU u hu hb hsol
  let B := autoRadiusLinearEquiv S r hr
  have hRadius : Real.sqrt L*r≤ 1/64 := by
    have hd : 0< 64*(Real.sqrt L+1) := by positivity
    have hh : r*(64*(Real.sqrt L+1))< 1 := (lt_div_iff₀ hd).mp hrr0
    nlinarith only [hh,hr]
  have hB : ‖B.toContinuousLinearMap‖≤ 1/32 :=
    ((autoRadiusLinearEquiv_elliptic_bounds (hell.le.trans hL) S hS r hr).1.trans
      (by nlinarith only [hRadius] : r*Real.sqrt L≤ 1/32))
  have hCQ : autoClosed (0 : Space n) (13/16) 0⊆unitClosed n := by
    simpa only [autoClosed,unitClosed,Yau.Parabolic.cylinder,zero_sub,one_pow] using
      autoClosed_subset (0 : Space n) (by norm_num : (0 : ℝ)≤ 13/16) (by norm_num : (13/16 : ℝ)≤ 1) 0
  have hbufC := auto_mollifier_closed_buffer (n := n) (by norm_num : (0 : ℝ)< 13/16)
    (by norm_num : (0 : ℝ)< 1/32) (by norm_num : (13/16 : ℝ)+1/32< 1)
  have hbufO := auto_mollifier_open_buffer (n := n) (by norm_num : (0 : ℝ)< 13/16)
    (by norm_num : (0 : ℝ)< 1/32) (by norm_num : (13/16 : ℝ)+1/32< 1)
  refine ⟨autoEllipsoidSecond_continuous hu hCQ B hB r hbufC,
    autoEllipsoidSecond_sub (autoOpen_isOpen 0 (13/16) 0)
      (autoOpen_subset_unitOpen (by norm_num : (0 : ℝ)< 13/16) (by norm_num : (13/16 : ℝ)< 1))
      hell hL hF hE hConc hu hsol B hB hr hbufO,?_⟩
  intro p hp
  let eps : ℕ → ℝ := autoDyadicStep (1/64)
  have heps (j : ℕ) : 0< eps j := auto_dyadicStep_pos (by norm_num) j
  have hepsSmall (j : ℕ) : eps j< 1/32 :=
    (auto_dyadicStep_le (by norm_num : (0 : ℝ)≤ 1/64) j).trans_lt (by norm_num)
  have hepsLim : Tendsto eps atTop (𝓝 0) := auto_dyadicStep_tendsto (1/64)
  have hbuffer : ∀ y∈Metric.closedBall (0 : Space n) (1/32), (p.1+y,p.2)∈unitClosed n := by
    intro y hy
    have hh := hbufC y hy p hp
    rcases p with ⟨x,t⟩
    simpa only [Prod.mk_add_mk,add_zero] using hh
  have hLim := (autoEllipsoidSecond_mollifier_tendsto_original B r w hw hwu hB eps heps hepsLim p (hCQ hp) hbuffer).2
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hLim
  apply Eventually.of_forall
  intro j
  let f : Space n → ℝ := fun x => autoSpatialMollify (eps j) (heps j) w (x,p.2)
  have hf : ContDiff ℝ ∞ f := autoSpatialMollify_spatial_contDiff (eps j) (heps j) w hw p.2
  have hPoint (z : Space n) (hz : z∈Metric.closedBall p.1 (1/32)) :
      (z,p.2)∈autoClosed (0 : Space n) (7/8) 0 := by
    have hx : ‖p.1‖≤ 13/16 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hp.1
    have hz' : ‖z-p.1‖≤ 1/32 := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
    have hn : ‖z‖≤ 7/8 := by
      have hh := norm_add_le (z-p.1) p.1
      rw [sub_add_cancel] at hh
      linarith only [hh,hx,hz']
    refine ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using hn,?_⟩
    have ht : -(13/16 : ℝ)^2≤ p.2 ∧ p.2≤ 0 := by simpa only [zero_sub,mem_Icc] using hp.2
    change (0 : ℝ)-(7/8)^2≤ p.2 ∧ p.2≤ 0
    exact ⟨by linarith only [ht.1],ht.2⟩
  have hLower : ∀ z∈Metric.ball p.1 (1/32), -C≤ ∑ i : Yau.RIdx n, ∑ k : Yau.RIdx n,
      (A : Mat n) i k*(fderiv ℝ (fderiv ℝ f) z) (Yau.realVec i) (Yau.realVec k) := by
    intro z hz
    have ht := hTrace (eps j) (heps j) (hepsSmall j) (z,p.2) (hPoint z (Metric.ball_subset_closedBall hz))
    change -C≤ Matrix.trace ((A : Mat n)*(hessian (autoSpatialMollify (eps j) (heps j) w) (z,p.2) : Mat n)) at ht
    have hh : (hessian (autoSpatialMollify (eps j) (heps j) w) (z,p.2) : Mat n)=secondFDerivMatrix f z :=
      hessian_space_eq_secondFDeriv (hf.contDiffAt.of_le (by simp))
    rw [hh,auto_energy_trace_eq hf] at ht
    exact ht
  have hmean := hMean f p.1 r (1/32) C hr hC.le (hRadius.trans (by norm_num))
    (fun z _ => hf.contDiffAt.of_le (by simp)) hLower
  have havg : autoEllipsoidMean B (autoSpatialMollify (eps j) (heps j) w) p=
      (∫ y in Metric.ball (0 : Space n) r, f (p.1+S y))/(volume : Measure (Space n)).real (Metric.ball 0 r) :=
    auto_radius_ellipsoid_average S hr f p.1
  rw [← havg] at hmean
  change -C≤ (autoEllipsoidMean B (autoSpatialMollify (eps j) (heps j) w) p-
    autoSpatialMollify (eps j) (heps j) w p)/r^2
  apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
  have hDen : 0< 2*((2*n : ℝ)+2) := by positivity
  have hDen1 : 1≤ 2*((2*n : ℝ)+2) := by nlinarith only [Nat.cast_nonneg (α := ℝ) n]
  have hstep : -C*r^2≤ -C*r^2/(2*((2*n : ℝ)+2)) := by
    apply (le_div_iff₀ hDen).mpr
    nlinarith only [mul_nonneg (mul_nonneg hC.le (sq_nonneg r)) (sub_nonneg.mpr hDen1)]
  exact hstep.trans hmean

end Yau.LeafProofs.L05AutonomousAux
