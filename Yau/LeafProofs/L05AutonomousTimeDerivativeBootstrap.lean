import Yau.LeafProofs.L05AutonomousTimeDerivativeIncrements
import Yau.LeafProofs.L05AutonomousTimeDerivativeExponents

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- Uniformity includes the operator: each collar constant precedes F and u. -/
def autoTDUniformTimeHolder (n : ℕ) (ell L beta : ℝ) : Prop :=
  ∀ r : ℝ, 0<r → r<1 → ∃ K : ℝ, 0<K ∧ ∀ F : Sym n → ℝ,
    globalElliptic F ell L → F 0=0 → ∀ u : Point n → ℝ,
    ContinuousOn u (unitClosed n) → (∀ z∈unitClosed n, |u z|≤1) →
    viscositySolution (unitOpen n) (fun H _ => F H) (fun _ => 0) u →
    autoTDTimeHolder beta r K u

theorem auto_td_initial_time_holder {n : ℕ} {ell L delta : ℝ}
    (hell : 0<ell) (hL : ell≤L) (hd : 0<delta)
    (hReg : autoTDCollarHolder n ell L delta) :
    autoTDUniformTimeHolder n ell L (delta/2) := by
  intro r hr hr1
  let R := (r+1)/2
  have hrR : r<R := by dsimp only [R]; linarith only [hr1]
  have hR1 : R<1 := by dsimp only [R]; linarith only [hr1]
  have hR : 0<R := hr.trans hrR
  obtain ⟨C,hC,hHolder⟩ := hReg r R hr hrR
  refine ⟨C,hC,?_⟩
  intro F hE h0 u hu hb hsol
  have hPucci := auto_solution_pucci hell hL (Metric.isOpen_ball.prod isOpen_Ioo) hE h0
    (hu.mono unitOpen_subset_unitClosed) hsol
  have hOpen := autoOpen_subset_unitOpen (n := n) hR hR1
  have hClass : autoPucci ell L (autoOpen (0 : Space n) R 0) u :=
    ⟨viscositySub_mono_domain hPucci.1 hOpen,viscositySuper_mono_domain hPucci.2 hOpen⟩
  have hh := hHolder u 1 zero_le_one (hu.mono (auto_td_closed_unit hR hR1))
    (fun z hz => hb z (auto_td_closed_unit hR hR1 hz)) hClass
  intro x hx t ht s hs
  have ht' : (x,t)∈autoClosed (0 : Space n) r 0 := ⟨hx,by simpa only [zero_sub] using ht⟩
  have hs' : (x,s)∈autoClosed (0 : Space n) r 0 := ⟨hx,by simpa only [zero_sub] using hs⟩
  simpa only [Real.norm_eq_abs,mul_one,holderWeight,sub_self,norm_zero,
    Real.zero_rpow hd.ne',zero_add] using hh.2.2 (x,t) ht' (x,s) hs'

/-- One genuine subcritical improvement, using F only at s strictly below one. -/
theorem auto_td_time_holder_step {n : ℕ} {ell L delta beta s : ℝ}
    (hell : 0<ell) (hL : ell≤L) (hd : 0<delta)
    (hReg : autoTDCollarHolder n ell L delta) (hs : 0<s) (hs1 : s<1)
    (hsraw : s≤beta+delta/2) (hPrev : autoTDUniformTimeHolder n ell L beta) :
    autoTDUniformTimeHolder n ell L s := by
  intro r hr hr1
  let R := (r+1)/2
  let S := (r+R)/2
  have hrR : r<R := by dsimp only [R]; linarith only [hr1]
  have hR1 : R<1 := by dsimp only [R]; linarith only [hr1]
  have hrS : r<S := by dsimp only [S]; linarith only [hrR]
  have hSR : S<R := by dsimp only [S]; linarith only [hrR]
  have hS : 0<S := hr.trans hrS
  have hS1 : S<1 := hSR.trans hR1
  have hR : 0<R := hr.trans hrR
  have hdwidth : 0<S^2-r^2 := by nlinarith only [hr,hrS]
  have hJ : -S^2+(S^2-r^2)=-r^2 := by ring
  obtain ⟨K,hK,hPrevious⟩ := hPrev R hR hR1
  obtain ⟨A,hA,hSecond⟩ := auto_td_second_bound hell hL hd hReg hS hSR hR1 hK.le hs hsraw
  obtain ⟨B,hB,hScalar⟩ := auto_second_first_holder (a := -S^2) (b := 0) hdwidth
    (by rw [hJ]; nlinarith only [hr] : -S^2+(S^2-r^2)<0) hs hs1
  refine ⟨B*(1+A),by positivity,?_⟩
  intro F hE h0 u hu hb hsol
  have hOld := hPrevious F hE h0 u hu hb hsol
  have hsec := hSecond F hE u hu hb hsol hOld
  intro x hx t ht s' hs'
  have hxS : x∈Metric.closedBall (0 : Space n) S := Metric.closedBall_subset_closedBall hrS.le hx
  have htime (tau : ℝ) (htau : tau∈Icc (-S^2) 0) : (x,tau)∈unitClosed n :=
    auto_td_closed_unit hS hS1 ⟨hxS,by simpa only [zero_sub] using htau⟩
  have hcont : ContinuousOn (fun tau => u (x,tau)) (Icc (-S^2) 0) :=
    hu.comp (continuous_const.prodMk continuous_id).continuousOn htime
  have hh := hScalar 1 A zero_le_one hA.le (fun tau => u (x,tau)) hcont
    (fun tau htau => hb _ (htime tau htau)) (hsec x hxS)
  rw [hJ] at hh
  exact hh t ht s' hs'

/-- The finite schedule never calls either scalar theorem at exponent one. -/
theorem auto_td_iterated_time_holder {n : ℕ} {ell L delta : ℝ}
    (hell : 0<ell) (hL : ell≤L) (hd : 0<delta) (hd1 : delta<1)
    (hReg : autoTDCollarHolder n ell L delta) (j : ℕ) :
    autoTDUniformTimeHolder n ell L (autoTDBeta delta j) := by
  induction j with
  | zero =>
    rw [auto_td_beta_zero hd hd1]
    exact auto_td_initial_time_holder hell hL hd hReg
  | succ j ih =>
    have hbeta := auto_td_beta_bounds hd hd1 (j+1)
    exact auto_td_time_holder_step hell hL hd hReg hbeta.1 hbeta.2 (auto_td_beta_step hd j) ih

theorem auto_td_subcritical_time_holder {n : ℕ} {ell L delta : ℝ}
    (hell : 0<ell) (hL : ell≤L) (hd : 0<delta) (hd1 : delta<1)
    (hReg : autoTDCollarHolder n ell L delta) :
    autoTDUniformTimeHolder n ell L (1-delta/4) := by
  obtain ⟨N,hN⟩ := auto_td_beta_eventually hd
  simpa only [hN] using auto_td_iterated_time_holder hell hL hd hd1 hReg N

end Yau.LeafProofs.L05AutonomousAux
