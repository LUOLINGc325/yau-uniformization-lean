import Yau.LeafProofs.L05AutonomousTimeDerivativeBootstrap
import Yau.LeafProofs.L05AutonomousTimeIncrementsParametric

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- F4 constructs the actual jointly continuous derivative, with an all-h error.
The closed top is retained, with only a derivative within the time interval. -/
theorem auto_td_derivative_construction {n : ℕ} {ell L delta r : ℝ}
    (hell : 0<ell) (hL : ell≤L) (hd : 0<delta) (hd1 : delta<1)
    (hReg : autoTDCollarHolder n ell L delta) (hr : 0<r) (hr1 : r<1) :
    ∃ C d : ℝ, 0<C ∧ 0<d ∧ ∀ F : Sym n → ℝ,
      globalElliptic F ell L → F 0=0 → ∀ u : Point n → ℝ,
      ContinuousOn u (unitClosed n) → (∀ z∈unitClosed n, |u z|≤1) →
      viscositySolution (unitOpen n) (fun H _ => F H) (fun _ => 0) u →
      ∃ V : Point n → ℝ, ContinuousOn V (autoClosed 0 r 0) ∧
        ∀ x∈Metric.closedBall (0 : Space n) r,
          ContinuousOn (fun t => V (x,t)) (Icc (-r^2) 0) ∧
          (∀ t∈Icc (-r^2) 0, |V (x,t)|≤C) ∧
          (∀ t∈Icc (-r^2) 0, ∀ h : ℝ, 0<h → h≤d/2 →
            |autoTime u h (x,t)-V (x,t)|≤C*h^(delta/4)) ∧
          (∀ a∈Icc (-r^2) 0, ∀ b∈Icc (-r^2) 0,
            u (x,b)-u (x,a)=∫ s in a..b, V (x,s)) ∧
          (∀ t∈Ioo (-r^2) 0, HasDerivAt (fun s => u (x,s)) (V (x,t)) t) ∧
          (∀ t∈Icc (-r^2) 0, HasDerivWithinAt (fun s => u (x,s)) (V (x,t))
            (Icc (-r^2) 0) t) := by
  let R := (r+1)/2
  let S := (R+1)/2
  let d := R^2-r^2
  have hrR : r<R := by dsimp only [R]; linarith only [hr1]
  have hR1 : R<1 := by dsimp only [R]; linarith only [hr1]
  have hRS : R<S := by dsimp only [S]; linarith only [hR1]
  have hS1 : S<1 := by dsimp only [S]; linarith only [hR1]
  have hR : 0<R := hr.trans hrR
  have hS : 0<S := hR.trans hRS
  have hdwidth : 0<d := by dsimp only [d]; nlinarith only [hr,hrR]
  have hJ : -R^2+d=-r^2 := by dsimp only [d]; ring
  have hs := auto_td_final_exponent hd hd1
  obtain ⟨K,hK,hPrevious⟩ := auto_td_subcritical_time_holder hell hL hd hd1 hReg S hS hS1
  obtain ⟨A,hA,hSecond⟩ := auto_td_second_bound hell hL hd hReg hR hRS hS1 hK.le (zero_lt_one.trans hs.1)
    (le_refl ((1-delta/4)+delta/2))
  obtain ⟨B,hB,hF4⟩ := auto_second_derivative_parametric (a := -R^2) (b := 0) hdwidth
    (by rw [hJ]; nlinarith only [hr] : -R^2+d<0) hs.1 hs.2
  let C := 1+B*(1+A)
  have hC : 0<C := by dsimp only [C]; positivity
  have hBC : B*(1+A)≤C := by dsimp only [C]; linarith
  have hBAC : B*A≤C := by dsimp only [C]; nlinarith only [hB]
  refine ⟨C,d,hC,hdwidth,?_⟩
  intro F hE h0 u hu hb hsol
  have hOld := hPrevious F hE h0 u hu hb hsol
  have hsec := hSecond F hE u hu hb hsol hOld
  have htime (z : Point n) (hz : z∈Metric.closedBall (0 : Space n) r ×ˢ Icc (-R^2) 0) :
      z∈unitClosed n := by
    apply auto_td_closed_unit hR hR1
    exact ⟨Metric.closedBall_subset_closedBall hrR.le hz.1,by simpa only [zero_sub] using hz.2⟩
  obtain ⟨V,hVc,hV⟩ := hF4 1 A zero_le_one hA.le (Space n) (Metric.closedBall 0 r) u
    (hu.mono htime) (fun x hx t ht => hb (x,t) (htime (x,t) ⟨hx,ht⟩))
    (fun x hx => hsec x (Metric.closedBall_subset_closedBall hrR.le hx))
  rw [hJ] at hVc hV
  refine ⟨V,?_,?_⟩
  · simpa only [autoClosed,zero_sub] using hVc
  intro x hx
  obtain ⟨hCont,hBound,_hTimeHolder,hError,hFTC,hDeriv,hWithin⟩ := hV x hx
  refine ⟨hCont,(fun t ht => (hBound t ht).trans hBC),?_,hFTC,hDeriv,hWithin⟩
  intro t ht h hh hhd
  have he := hError t ht h hh hhd
  have hexponent : (1-delta/4)+delta/2-1=delta/4 := by ring
  rw [hexponent] at he
  exact he.trans (mul_le_mul_of_nonneg_right hBAC (Real.rpow_nonneg hh.le _))

end Yau.LeafProofs.L05AutonomousAux
