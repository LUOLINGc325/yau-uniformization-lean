import Yau.LeafProofs.L05AutonomousPucciHolder

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- A fixed spatial collar also buffers the entire closed time interval. -/
theorem auto_td_holder_buffer {n : ℕ} {r R : ℝ} (hr : 0<r) (hrR : r<R)
    {p q : Point n} (hp : p∈autoClosed 0 r 0) (hq : q∈autoClosed 0 r 0) :
    autoClosed p.1 ((R-r)/2) (max p.2 q.2)⊆autoClosed 0 R 0 ∧
    autoOpen p.1 ((R-r)/2) (max p.2 q.2)⊆autoOpen 0 R 0 := by
  have hR : 0<R := hr.trans hrR
  have hwidth : 0<(R-r)/2 := by linarith only [hrR]
  have hpx : ‖p.1‖≤r := by simpa only [Metric.mem_closedBall,dist_zero_right] using hp.1
  have hpt : -r^2≤p.2 ∧ p.2≤0 := by simpa only [zero_sub,mem_Icc] using hp.2
  have hqt : -r^2≤q.2 ∧ q.2≤0 := by simpa only [zero_sub,mem_Icc] using hq.2
  have htop : max p.2 q.2≤0 := max_le hpt.2 hqt.2
  have hbottom : r^2+((R-r)/2)^2<R^2 := by nlinarith only [hr,hrR]
  have hspace (x : Space n) (hx : dist x p.1≤(R-r)/2) : ‖x‖<R := by
    have hnorm := norm_add_le (x-p.1) p.1
    rw [sub_add_cancel] at hnorm
    rw [dist_eq_norm] at hx
    linarith only [hnorm,hx,hpx,hrR]
  constructor
  · intro z hz
    refine ⟨?_,?_,?_⟩
    · simpa only [Metric.mem_closedBall,dist_zero_right] using (hspace z.1 hz.1).le
    · have ht : max p.2 q.2-((R-r)/2)^2≤z.2 := hz.2.1
      have hm := le_max_left p.2 q.2
      simp only [zero_sub]
      change -R^2≤z.2
      linarith only [ht,hm,hpt.1,hbottom]
    · exact hz.2.2.trans htop
  · intro z hz
    refine ⟨?_,?_,?_⟩
    · simpa only [Metric.mem_ball,dist_zero_right] using hspace z.1 hz.1.le
    · have ht : max p.2 q.2-((R-r)/2)^2<z.2 := hz.2.1
      have hm := le_max_left p.2 q.2
      simp only [zero_sub]
      change -R^2<z.2
      linarith only [ht,hm,hpt.1,hbottom]
    · exact hz.2.2.trans_le htop

/-- One exponent works on every prescribed collar, including its bottom and top. -/
theorem auto_td_collar_holder (n : ℕ) (hn : 0<n) (ell L : ℝ) (hell : 0<ell) (hL : ell≤L) :
    ∃ delta : ℝ, 0<delta ∧ delta<1 ∧
      ∀ r R : ℝ, 0<r → r<R → ∃ C : ℝ, 0<C ∧
      ∀ (w : Point n → ℝ) (M : ℝ), 0≤M → ContinuousOn w (autoClosed 0 R 0) →
      (∀ z∈autoClosed 0 R 0, |w z|≤M) → autoPucci ell L (autoOpen 0 R 0) w →
      HolderBound delta (autoClosed 0 r 0) w (C*M) := by
  obtain ⟨delta,A,hd,hd1,hA,hOsc⟩ := auto_pucci_cylinder_oscillation hn hell hL
  refine ⟨delta,hd,hd1,?_⟩
  intro r R hr hrR
  let rho := (R-r)/2
  have hrho : 0<rho := by dsimp only [rho]; linarith only [hrR]
  let V := rho^delta
  let C := 1+2*(A+1)/V
  have hV : 0< V := Real.rpow_pos_of_pos (hrho) _
  have hC : 0< C := by dsimp only [C]; positivity
  have hC1 : 1≤ C := by
    dsimp only [C]
    exact le_add_of_nonneg_right (div_nonneg (by positivity) hV.le)
  refine ⟨C,hC,?_⟩
  intro w M hM hw hb hP
  have hback : autoClosed (0 : Space n) r 0⊆autoClosed 0 R 0 :=
    autoClosed_subset 0 hr.le hrR.le 0
  refine ⟨mul_nonneg hC.le hM,?_,?_⟩
  · intro z hz
    rw [Real.norm_eq_abs]
    exact (hb z (hback hz)).trans (by nlinarith only [mul_le_mul_of_nonneg_right hC1 hM])
  intro p hp q hq
  rw [Real.norm_eq_abs]
  let D := parabolicDistance p q
  have hD : 0≤ D := auto_parabolic_distance_nonneg p q
  have hweight := auto_parabolic_distance_weight hd.le hd1.le p q
  have hDp : 0≤ D^delta := Real.rpow_nonneg hD _
  have habs : |w p-w q|≤ 2*M := by
    have hpv := abs_le.mp (hb p (hback hp))
    have hqv := abs_le.mp (hb q (hback hq))
    exact abs_le.mpr ⟨by linarith only [hpv.1,hqv.2],by linarith only [hpv.2,hqv.1]⟩
  have hmain : |w p-w q|≤ C*M*D^delta := by
    by_cases hzero : D=0
    · have hpq := auto_parabolic_distance_zero hzero
      rw [hpq,sub_self,abs_zero]
      positivity
    have hDpos : 0< D := lt_of_le_of_ne hD (Ne.symm hzero)
    by_cases hnear : D≤ rho
    · have hbuf := auto_td_holder_buffer hr hrR hp hq
      have hcont := hw.mono hbuf.1
      have hclass : autoPucci ell L (autoOpen p.1 rho (max p.2 q.2)) w :=
        ⟨viscositySub_mono_domain hP.1 hbuf.2,viscositySuper_mono_domain hP.2 hbuf.2⟩
      have hrange : ∀ z∈autoClosed p.1 rho (max p.2 q.2), -M≤ w z ∧ w z≤ M :=
        fun z hz => abs_le.mp (hb z (hbuf.1 hz))
      have hpair := auto_pair_in_distance_cylinder p q
      have hh := hOsc p.1 rho (max p.2 q.2) hrho w (-M) M hcont hrange hclass
        D hDpos hnear p hpair.1 q hpair.2
      rw [Real.div_rpow hD hrho.le] at hh
      change |w p-w q|≤ A*(D^delta/V)*(M-(-M)) at hh
      have hcoef : 2*A≤ C*V := by
        dsimp only [C]
        rw [add_mul,one_mul,div_mul_cancel₀ _ hV.ne']
        linarith only [hV.le]
      have hbound := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hM) hDp
      have hscaled := mul_le_mul_of_nonneg_right hh hV.le
      have heq : (A*(D^delta/V)*(M-(-M)))*V=2*A*M*D^delta := by field_simp; ring
      rw [heq] at hscaled
      apply (mul_le_mul_iff_of_pos_right hV).mp
      nlinarith only [hscaled,hbound]
    · have hfar : rho≤ D := (lt_of_not_ge hnear).le
      have hpw : V≤ D^delta := Real.rpow_le_rpow hrho.le hfar hd.le
      have hcoef : 2≤ C*V := by
        dsimp only [C]
        rw [add_mul,one_mul,div_mul_cancel₀ _ hV.ne']
        linarith only [hV.le,hA.le]
      have hh := mul_le_mul_of_nonneg_left hpw (mul_nonneg hC.le hM)
      have htwo := mul_le_mul_of_nonneg_right hcoef hM
      nlinarith only [habs,hh,htwo]
  exact hmain.trans (mul_le_mul_of_nonneg_left hweight (mul_nonneg hC.le hM))

end Yau.LeafProofs.L05AutonomousAux
