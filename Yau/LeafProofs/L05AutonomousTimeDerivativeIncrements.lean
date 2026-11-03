import Yau.LeafProofs.L05AutonomousTimeDerivativeCollar
import Yau.LeafProofs.L05AutonomousTimeIncrements
import Yau.LeafProofs.L05AutonomousAverageStability

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

def autoTDCollarHolder (n : ℕ) (ell L delta : ℝ) : Prop :=
  ∀ r R : ℝ, 0<r → r<R → ∃ C : ℝ, 0<C ∧
    ∀ (w : Point n → ℝ) (M : ℝ), 0≤M → ContinuousOn w (autoClosed 0 R 0) →
    (∀ z∈autoClosed 0 R 0, |w z|≤M) → autoPucci ell L (autoOpen 0 R 0) w →
    HolderBound delta (autoClosed 0 r 0) w (C*M)

def autoTDTimeHolder {n : ℕ} (beta R K : ℝ) (u : Point n → ℝ) : Prop :=
  ∀ x∈Metric.closedBall (0 : Space n) R, ∀ t∈Icc (-R^2) 0,
    ∀ s∈Icc (-R^2) 0, |u (x,t)-u (x,s)|≤K*|t-s|^beta

theorem auto_td_closed_unit {n : ℕ} {R : ℝ} (hR : 0<R) (hR1 : R<1) :
    autoClosed (0 : Space n) R 0⊆unitClosed n := by
  intro z hz
  have hx : dist z.1 0≤R := hz.1
  have ht : 0-R^2≤z.2 ∧ z.2≤0 := hz.2
  refine ⟨hx.trans hR1.le,?_,ht.2⟩
  change -1≤z.2
  nlinarith only [ht.1,hR,hR1]

theorem auto_td_shift_closed {n : ℕ} {R h : ℝ} (_hR : 0<R) (hR1 : R<1)
    (hh : 0≤h) (hbuf : R^2+h≤1) :
    ∀ z∈autoClosed (0 : Space n) R 0, (z.1,z.2-h)∈unitClosed n := by
  intro z hz
  refine ⟨(show dist z.1 0≤R from hz.1).trans hR1.le,?_,?_⟩
  · change -1≤z.2-h
    have ht : 0-R^2≤z.2 := hz.2.1
    linarith only [ht,hbuf]
  · have ht : z.2≤0 := hz.2.2
    linarith only [ht,hh]

theorem auto_td_pucci_scale {n : ℕ} {ell L a : ℝ} (hell : 0<ell) (hL : ell≤L)
    (ha : 0<a) {Q : Set (Point n)} {w : Point n → ℝ} (hw : autoPucci ell L Q w) :
    autoPucci ell L Q (fun z => a*w z) := by
  have hneg : viscositySub Q (fun H _ => pucciPlus ell L H) (fun _ => 0) (fun z => -w z) := by
    simpa only [neg_neg] using auto_super_iff_neg_sub.mp hw.2
  refine ⟨auto_pucci_sub_scale hell.le hL ha hw.1,?_⟩
  convert auto_pucci_super_neg (auto_pucci_sub_scale hell.le hL ha hneg) using 1
  funext z
  ring

/-- The estimate concerns the literal unnormalized increment, in both native signs. -/
theorem auto_td_increment_pucci {n : ℕ} {ell L R : ℝ} (hell : 0<ell) (hL : ell≤L)
    (hR : 0<R) (hR1 : R<1) {F : Sym n → ℝ} (hE : globalElliptic F ell L)
    {u : Point n → ℝ} (hu : ContinuousOn u (unitClosed n))
    (hsol : viscositySolution (unitOpen n) (fun H _ => F H) (fun _ => 0) u)
    {h : ℝ} (hh : 0<h) (hbuf : R^2+h<1) :
    autoPucci ell L (autoOpen 0 R 0) (fun z => u z-u (z.1,z.2-h)) := by
  convert auto_td_pucci_scale hell hL hh (auto_time_pucci hell hL hR hR1 hE hu hsol hh hbuf) using 1
  funext z
  dsimp only [autoTime]
  field_simp

/-- The small increment estimate and the bounded large increments give ALL legal h. -/
theorem auto_td_second_bound {n : ℕ} {ell L delta beta s r R K : ℝ}
    (hell : 0<ell) (hL : ell≤L) (hd : 0<delta)
    (hReg : autoTDCollarHolder n ell L delta)
    (hr : 0<r) (hrR : r<R) (hR1 : R<1) (hK : 0≤K)
    (hs : 0<s) (hsraw : s≤beta+delta/2) :
    ∃ A : ℝ, 0<A ∧ ∀ (F : Sym n → ℝ), globalElliptic F ell L →
      ∀ u : Point n → ℝ, ContinuousOn u (unitClosed n) →
      (∀ z∈unitClosed n, |u z|≤1) →
      viscositySolution (unitOpen n) (fun H _ => F H) (fun _ => 0) u →
      autoTDTimeHolder beta R K u →
      ∀ x∈Metric.closedBall (0 : Space n) r, ∀ t h : ℝ, 0<h → -r^2≤t-2*h → t≤0 →
        |autoRealSecond (fun tau => u (x,tau)) t h|≤A*h^s := by
  let S := (r+R)/2
  have hrS : r<S := by dsimp only [S]; linarith only [hrR]
  have hSR : S<R := by dsimp only [S]; linarith only [hrR]
  have hS : 0<S := hr.trans hrS
  have hS1 : S<1 := hSR.trans hR1
  have hR : 0<R := hr.trans hrR
  obtain ⟨B,hB,hHolder⟩ := hReg r S hr hrS
  let threshold := min ((R^2-S^2)/2) ((1-S^2)/2)
  have hthreshold : 0<threshold := by dsimp only [threshold]; apply lt_min <;> nlinarith only [hS,hSR,hS1,hR]
  have hthreshold1 : threshold<1 := (min_le_right _ _).trans_lt (by nlinarith only [sq_nonneg S])
  let A := 1+B*K+4/threshold^s
  have hA : 0<A := by dsimp only [A]; positivity
  refine ⟨A,hA,?_⟩
  intro F hE u hu hb hsol hOld x hx t h hh hbottom htop
  have ht : t∈Icc (-r^2) 0 := ⟨by linarith only [hbottom,hh],htop⟩
  have hth : t-h∈Icc (-r^2) 0 := ⟨by linarith only [hbottom,hh],by linarith only [htop,hh]⟩
  have ht2h : t-2*h∈Icc (-r^2) 0 := ⟨hbottom,by linarith only [htop,hh]⟩
  have hclosed (tau : ℝ) (htau : tau∈Icc (-r^2) 0) : (x,tau)∈autoClosed (0 : Space n) r 0 :=
    ⟨hx,by simpa only [zero_sub] using htau⟩
  by_cases hsmall : h≤threshold
  · have hsmallR : S^2+h<R^2 := by have hh' := min_le_left ((R^2-S^2)/2) ((1-S^2)/2); change threshold≤_ at hh'; nlinarith only [hh',hsmall,hS,hSR,hR]
    have hsmall1 : S^2+h<1 := by have hh' := min_le_right ((R^2-S^2)/2) ((1-S^2)/2); change threshold≤_ at hh'; nlinarith only [hh',hsmall,hS,hS1]
    let w : Point n → ℝ := fun z => u z-u (z.1,z.2-h)
    have hw : ContinuousOn w (autoClosed 0 S 0) :=
      (hu.mono (auto_td_closed_unit hS hS1)).sub
        (hu.comp (continuous_fst.prodMk (continuous_snd.sub continuous_const)).continuousOn
          (auto_td_shift_closed hS hS1 hh.le hsmall1.le))
    have hbound : ∀ z∈autoClosed (0 : Space n) S 0, |w z|≤K*h^beta := by
      intro z hz
      have hxR : z.1∈Metric.closedBall (0 : Space n) R := Metric.closedBall_subset_closedBall hSR.le hz.1
      have hztime : -S^2≤z.2 ∧ z.2≤0 := by simpa only [zero_sub,mem_Icc] using hz.2
      have htR : z.2∈Icc (-R^2) 0 := ⟨by nlinarith only [hztime.1,hS,hSR,hR],hztime.2⟩
      have htRh : z.2-h∈Icc (-R^2) 0 := ⟨by linarith only [hztime.1,hsmallR],by linarith only [hztime.2,hh]⟩
      simpa only [w,sub_sub_cancel,abs_of_pos hh] using hOld z.1 hxR z.2 htR (z.2-h) htRh
    have hPucci := auto_td_increment_pucci hell hL hS hS1 hE hu hsol hh hsmall1
    have hhld := (hHolder w (K*h^beta) (by positivity) hw hbound hPucci).2.2
      (x,t) (hclosed t ht) (x,t-h) (hclosed _ hth)
    have hweight : holderWeight delta (x,t) (x,t-h)=h^(delta/2) := by
      simp only [holderWeight,sub_self,norm_zero,Real.zero_rpow hd.ne',zero_add,sub_sub_cancel,abs_of_pos hh]
    rw [Real.norm_eq_abs,hweight] at hhld
    have heq : w (x,t)-w (x,t-h)=autoRealSecond (fun tau => u (x,tau)) t h := by
      dsimp only [w,autoRealSecond]
      rw [show t-h-h=t-2*h by ring]
      ring
    rw [heq,show B*(K*h^beta)*h^(delta/2)=B*K*h^(beta+delta/2) by rw [Real.rpow_add hh]; ring] at hhld
    have hp := Real.rpow_le_rpow_of_exponent_ge hh (hsmall.trans hthreshold1.le) hsraw
    have hcoef : B*K≤A := by
      dsimp only [A]
      have hp : 0≤4/threshold^s := by positivity
      linarith only [hp]
    exact hhld.trans ((mul_le_mul_of_nonneg_left hp (mul_nonneg hB.le hK)).trans
      (mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hh.le s)))
  · have hthree (tau : ℝ) (htau : tau∈Icc (-r^2) 0) : |u (x,tau)|≤1 :=
      hb _ (auto_td_closed_unit hr (hrR.trans hR1) (hclosed tau htau))
    have hbase : |autoRealSecond (fun tau => u (x,tau)) t h|≤4 := by
      have h1 := abs_le.mp (hthree t ht)
      have h2 := abs_le.mp (hthree (t-h) hth)
      have h3 := abs_le.mp (hthree (t-2*h) ht2h)
      dsimp only [autoRealSecond]
      exact abs_le.mpr ⟨by linarith only [h1.1,h2.2,h3.1],by linarith only [h1.2,h2.1,h3.2]⟩
    have hp := Real.rpow_le_rpow hthreshold.le (le_of_not_ge hsmall) hs.le
    have hpow : 0<threshold^s := Real.rpow_pos_of_pos hthreshold s
    have hfour : 4≤(4/threshold^s)*h^s := by
      calc
        4 = (4/threshold^s)*threshold^s := by field_simp
        _ ≤ (4/threshold^s)*h^s := mul_le_mul_of_nonneg_left hp (by positivity)
    have hcoef : 4/threshold^s≤A := by
      dsimp only [A]
      have hp : 0≤B*K := mul_nonneg hB.le hK
      linarith only [hp]
    exact hbase.trans (hfour.trans (mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hh.le s)))

end Yau.LeafProofs.L05AutonomousAux
