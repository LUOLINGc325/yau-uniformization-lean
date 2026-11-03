import Yau.LeafProofs.L05AutonomousTimeDerivativeLimit

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- A genuine bounded space-time Hölder time derivative, before any spatial
second derivatives are constructed. At the top the derivative is only within. -/
theorem auto_time_derivative :
    ∀ n : ℕ, 0<n → ∀ ell L : ℝ, 0<ell → ell≤L →
    ∃ delta C : ℝ, 0<delta ∧ delta<1 ∧ 0<C ∧
      ∀ F : Sym n → ℝ, Continuous F → globalElliptic F ell L → F 0=0 →
      ∀ u : Point n → ℝ, ContinuousOn u (unitClosed n) →
        (∀ z∈unitClosed n, |u z|≤1) →
        viscositySolution (unitOpen n) (fun H _ => F H) (fun _ => 0) u →
      ∃ V : Point n → ℝ,
        ContinuousOn V (autoClosed (0 : Space n) (15/16) 0) ∧
        (∀ z∈autoClosed 0 (15/16) 0, |V z|≤C) ∧
        HolderBound delta (autoClosed 0 (15/16) 0) V C ∧
        autoPucci ell L (autoOpen 0 (15/16) 0) V ∧
        (∀ x∈Metric.closedBall (0 : Space n) (15/16),
          (∀ t∈Ioo (-(15/16 : ℝ)^2) 0,
            HasDerivAt (fun s => u (x,s)) (V (x,t)) t) ∧
          (∀ t∈Icc (-(15/16 : ℝ)^2) 0,
            HasDerivWithinAt (fun s => u (x,s)) (V (x,t))
              (Icc (-(15/16 : ℝ)^2) 0) t) ∧
          (∀ a∈Icc (-(15/16 : ℝ)^2) 0,
           ∀ b∈Icc (-(15/16 : ℝ)^2) 0,
            u (x,b)-u (x,a)=∫ s in a..b, V (x,s))) ∧
        (∀ z∈backward (15/16), timeD (backward (15/16)) u z=V z) := by
  intro n hn ell L hell hL
  obtain ⟨delta,hd,hd1,hReg⟩ := auto_td_collar_holder n hn ell L hell hL
  obtain ⟨A,d,hA,hdwidth,hConstruct⟩ := auto_td_derivative_construction hell hL hd hd1 hReg
    (by norm_num : (0 : ℝ)<63/64) (by norm_num : (63/64 : ℝ)<1)
  obtain ⟨B,hB,hHolder⟩ := hReg (15/16) (31/32) (by norm_num) (by norm_num)
  let C := 1+A+B*A
  have hC : 0<C := by dsimp only [C]; positivity
  have hAC : A≤C := by
    dsimp only [C]
    have hp : 0≤B*A := by positivity
    linarith only [hp]
  have hBAC : B*A≤C := by dsimp only [C]; linarith only [hA]
  refine ⟨delta,C,hd,hd1,hC,?_⟩
  intro F _hF hE h0 u hu hb hsol
  obtain ⟨V,hVc,hV⟩ := hConstruct F hE h0 u hu hb hsol
  have hsmall : autoClosed (0 : Space n) (15/16) 0⊆autoClosed 0 (63/64) 0 :=
    autoClosed_subset 0 (by norm_num) (by norm_num) 0
  have hmid : autoClosed (0 : Space n) (31/32) 0⊆autoClosed 0 (63/64) 0 :=
    autoClosed_subset 0 (by norm_num) (by norm_num) 0
  have hbound : ∀ z∈autoClosed (0 : Space n) (63/64) 0, |V z|≤A := by
    intro z hz
    exact (hV z.1 hz.1).2.1 z.2 (by simpa only [zero_sub] using hz.2)
  have hPucci : autoPucci ell L (autoOpen (0 : Space n) (31/32) 0) V :=
    auto_td_derivative_pucci hell hL hd (by norm_num) (by norm_num) (by norm_num) hdwidth hE hu hsol
      (fun z hz h hh hhd => (hV z.1 hz.1).2.2.1 z.2 (by simpa only [zero_sub] using hz.2) h hh hhd)
  have hhld := hHolder V A hA.le (hVc.mono hmid) (fun z hz => hbound z (hmid hz)) hPucci
  have hPucciSmall : autoPucci ell L (autoOpen (0 : Space n) (15/16) 0) V :=
    ⟨viscositySub_mono_domain hPucci.1 (autoOpen_subset 0 (by norm_num) (by norm_num) 0),
      viscositySuper_mono_domain hPucci.2 (autoOpen_subset 0 (by norm_num) (by norm_num) 0)⟩
  refine ⟨V,hVc.mono hsmall,(fun z hz => (hbound z (hsmall hz)).trans hAC),?_,hPucciSmall,?_,?_⟩
  · refine ⟨hC.le,(fun z hz => (hhld.2.1 z hz).trans hBAC),?_⟩
    intro z hz q hq
    exact (hhld.2.2 z hz q hq).trans (mul_le_mul_of_nonneg_right hBAC
      (add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (abs_nonneg _) _)))
  · intro x hx
    have hxBig : x∈Metric.closedBall (0 : Space n) (63/64) := Metric.closedBall_subset_closedBall (by norm_num) hx
    have hJ : Icc (-(15/16 : ℝ)^2) 0⊆Icc (-(63/64 : ℝ)^2) 0 := by
      intro t ht
      exact ⟨by linarith only [ht.1],ht.2⟩
    obtain ⟨_hCont,_hBound,_hError,hFTC,hDeriv,hWithin⟩ := hV x hxBig
    refine ⟨?_,(fun t ht => (hWithin t (hJ ht)).mono hJ),?_⟩
    · intro t ht
      exact hDeriv t ⟨by linarith only [ht.1],ht.2⟩
    · intro a ha b hb'
      exact hFTC a (hJ ha) b (hJ hb')
  · exact auto_td_timeD_eq (by norm_num) (by norm_num)
      (fun x hx t ht => (hV x hx).2.2.2.2.2 t ht)

end Yau.LeafProofs.L05AutonomousAux
