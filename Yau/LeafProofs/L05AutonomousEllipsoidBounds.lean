import Yau.LeafProofs.L05AutonomousEllipsoidLower
import Yau.LeafProofs.L05AutonomousEllipsoidCutoff
import Yau.LeafProofs.L05AutonomousCutoffPositivePart
import Yau.LeafProofs.L05AutonomousCylinderIntegral
import Yau.LeafProofs.L05AutonomousLocalMaximumCollar

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- The real positive mean, true cutoff pairing and proved local maximum give both uniform signs. -/
theorem auto_uniform_ellipsoid_bounds :
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
        ∀ (r : ℝ) (hr : 0< r), r< r0 → ∀ p∈autoClosed (0 : Space n) (49/64) 0,
          |autoEllipsoidSecond (autoRadiusLinearEquiv S r hr) r u p|≤ C := by
  intro n hn ell L hell hL
  obtain ⟨C₀,r₀,hC₀,hr₀,hLower⟩ := auto_uniform_ellipsoid_lower n hn ell L hell hL
  let chi : ContDiffBump (0 : Space n) := ⟨25/32,13/16,by norm_num,by norm_num⟩
  have hSupp : tsupport chi⊆Metric.closedBall (0 : Space n) (13/16) := by rw [chi.tsupport_eq]
  obtain ⟨Aχ,hAχ,hPairBudget⟩ := auto_original_ellipsoid_cutoff_bound
    (chi.contDiff : ContDiff ℝ 2 chi) chi.hasCompactSupport
    (by norm_num : (0 : ℝ)≤ 1/32) (by norm_num : (13/16 : ℝ)+1/32< 1) hSupp
  obtain ⟨K,hK,hMax⟩ := auto_local_maximum_collar n hn ell L hell hL 1 zero_lt_one
    (by norm_num : (0 : ℝ)< 49/64) (by norm_num : (49/64 : ℝ)< 25/32)
  let Bslice := Aχ*L+C₀*(∫ x, chi x)
  let Etotal := (25/32 : ℝ)^2*Bslice
  let C := 1+C₀+K*Etotal
  let r0 := min r₀ (1/(64*(Real.sqrt L+1)))
  have hL0 : 0≤ L := hell.le.trans hL
  have hSlice0 : 0≤ Bslice := add_nonneg (mul_nonneg hAχ.le hL0)
    (mul_nonneg hC₀.le (integral_nonneg fun x => chi.nonneg))
  have hEnergy0 : 0≤ Etotal := mul_nonneg (sq_nonneg _) hSlice0
  have hC : 0< C := by dsimp only [C];linarith only [hC₀,mul_nonneg hK.le hEnergy0]
  have hC₀C : C₀≤ C := by dsimp only [C];linarith only [mul_nonneg hK.le hEnergy0]
  have hUpperC : K*Etotal≤ C := by dsimp only [C];linarith only [hC₀]
  have hr0 : 0< r0 := lt_min hr₀ (by positivity)
  refine ⟨C,r0,hC,hr0,?_⟩
  intro F hF hE hConc h0
  obtain ⟨A,hA,S,hS,hSi,hST,hForU⟩ := hLower F hF hE hConc h0
  refine ⟨A,hA,S,hS,hSi,hST,?_⟩
  intro u hu hb hsol r hr hrr0
  let B := autoRadiusLinearEquiv S r hr
  let q := autoEllipsoidSecond B r u
  have hrrOld : r< r₀ := hrr0.trans_le (min_le_left _ _)
  have hrrSmall : r< 1/(64*(Real.sqrt L+1)) := hrr0.trans_le (min_le_right _ _)
  obtain ⟨hqc,hqs,hql⟩ := hForU u hu hb hsol r hr hrrOld
  have hRadius : Real.sqrt L*r≤ 1/64 := by
    have hd : 0< 64*(Real.sqrt L+1) := by positivity
    have hh : r*(64*(Real.sqrt L+1))< 1 := (lt_div_iff₀ hd).mp hrrSmall
    nlinarith only [hh,hr]
  have hNorm : ‖B.toContinuousLinearMap‖≤ 1/32 :=
    ((autoRadiusLinearEquiv_elliptic_bounds hL0 S hS r hr).1.trans
      (by nlinarith only [hRadius] : r*Real.sqrt L≤ 1/32))
  have hNormSq : ‖B.toContinuousLinearMap‖^2≤ r^2*L :=
    (autoRadiusLinearEquiv_elliptic_bounds hL0 S hS r hr).2
  have hSlice : ∀ t∈Icc (-(25/32 : ℝ)^2) 0,
      (∫ x in Metric.ball (0 : Space n) (25/32), max (q (x,t)) 0)≤ Bslice := by
    intro t ht
    have htOut : t∈Icc (-(13/16 : ℝ)^2) 0 := ⟨by linarith only [ht.1],ht.2⟩
    have htUnit : t∈Icc (-1 : ℝ) 0 := ⟨by linarith only [ht.1],ht.2⟩
    have hqSlice : ContinuousOn (fun x => q (x,t)) (Metric.closedBall (0 : Space n) (13/16)) :=
      hqc.comp (continuous_id.prodMk continuous_const).continuousOn (fun x hx =>
        ⟨hx,by simpa only [zero_sub] using htOut⟩)
    have hLowSlice (x : Space n) (hx : x∈Metric.closedBall (0 : Space n) (13/16)) : -C₀≤ q (x,t) :=
      hql (x,t) ⟨hx,by simpa only [zero_sub] using htOut⟩
    have hPair := hPairBudget B hr hL0 (by norm_num : (0 : ℝ)≤ 1) hNorm hNormSq u hu hb t htUnit
    have hPairBound : |∫ x, chi x*q (x,t)|≤ Aχ*L := by simpa only [mul_one] using hPair.2
    exact (auto_cutoff_positive_integral (by norm_num : (25/32 : ℝ)≤ 13/16) hC₀.le hqSlice
      chi.continuous chi.hasCompactSupport (fun x => chi.nonneg) hSupp
      (fun x hx => chi.one_of_mem_closedBall hx) hLowSlice hPair.1 hPairBound).2
  have hqcInner : ContinuousOn q (autoClosed (0 : Space n) (25/32) 0) :=
    hqc.mono (autoClosed_subset 0 (by norm_num) (by norm_num) 0)
  have hqsInner : viscositySub (autoOpen (0 : Space n) (25/32) 0)
      (fun H _ => pucciPlus ell L H) (fun _ => 0) q :=
    viscositySub_mono_domain hqs (autoOpen_subset 0 (by norm_num) (by norm_num) 0)
  have hCylinder := auto_positive_cylinder_integral (by norm_num : -(25/32 : ℝ)^2≤ 0)
    (by simpa only [autoClosed,zero_sub] using hqcInner) hSlice
  have hTotal : (∫ p in autoOpen (0 : Space n) (25/32) 0, max (q p) 0)≤ Etotal := by
    simpa only [autoOpen,zero_sub,neg_neg] using hCylinder.2
  intro p hp
  have hPoint := hMax q hqcInner hqsInner p hp
  simp only [one_div_one,Real.rpow_one] at hPoint
  have hUpper : q p≤ C :=
    (le_max_left _ _).trans ((hPoint.trans (mul_le_mul_of_nonneg_left hTotal hK.le)).trans hUpperC)
  have hLowerPoint : -C≤ q p :=
    (neg_le_neg hC₀C).trans (hql p (autoClosed_subset 0 (by norm_num) (by norm_num) 0 hp))
  exact abs_le.mpr ⟨hLowerPoint,hUpper⟩

end Yau.LeafProofs.L05AutonomousAux
