import Yau.LeafProofs.L05AutonomousHarnackOscillation
import Mathlib.Analysis.MeanInequalitiesPow

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

theorem auto_parabolic_distance_nonneg {n : ℕ} (p q : Point n) : 0≤ parabolicDistance p q :=
  add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)

theorem auto_parabolic_distance_time {n : ℕ} (p q : Point n) :
    |p.2-q.2|≤ (parabolicDistance p q)^2 := by
  have hs : Real.sqrt |p.2-q.2|≤ parabolicDistance p q := le_add_of_nonneg_left (norm_nonneg _)
  nlinarith only [Real.sq_sqrt (abs_nonneg (p.2-q.2)),Real.sqrt_nonneg |p.2-q.2|,
    auto_parabolic_distance_nonneg p q,hs]

theorem auto_parabolic_distance_zero {n : ℕ} {p q : Point n} (h : parabolicDistance p q=0) : p=q := by
  have hx : ‖p.1-q.1‖≤ parabolicDistance p q := le_add_of_nonneg_right (Real.sqrt_nonneg _)
  rw [h] at hx
  have hxn : ‖p.1-q.1‖=0 := le_antisymm hx (norm_nonneg _)
  have ht := auto_parabolic_distance_time p q
  rw [h] at ht
  have htn : |p.2-q.2|=0 := by linarith only [ht,abs_nonneg (p.2-q.2)]
  exact Prod.ext (sub_eq_zero.mp (norm_eq_zero.mp hxn)) (sub_eq_zero.mp (abs_eq_zero.mp htn))

theorem auto_parabolic_distance_weight {n : ℕ} {delta : ℝ} (hd : 0≤ delta) (hd1 : delta≤ 1)
    (p q : Point n) : (parabolicDistance p q)^delta≤ holderWeight delta p q := by
  dsimp only [parabolicDistance,holderWeight]
  calc
    _ ≤ ‖p.1-q.1‖^delta+(Real.sqrt |p.2-q.2|)^delta :=
      Real.rpow_add_le_add_rpow (norm_nonneg _) (Real.sqrt_nonneg _) hd hd1
    _ = _ := by rw [← Real.rpow_div_two_eq_sqrt delta (abs_nonneg _)]

/-- Every pair in the fixed interior collar has a uniformly buffered containing cylinder. -/
theorem auto_holder_buffer {n : ℕ} {p q : Point n}
    (hp : p∈backward (3/4)) (hq : q∈backward (3/4)) :
    autoClosed p.1 (1/8) (max p.2 q.2)⊆unitClosed n ∧
    autoOpen p.1 (1/8) (max p.2 q.2)⊆unitOpen n := by
  have hpx : ‖p.1‖< 3/4 := by simpa only [backward,Metric.mem_ball,dist_zero_right] using hp.1
  have hpt : -(3/4 : ℝ)^2< p.2 ∧ p.2≤ 0 := hp.2
  have hqt : -(3/4 : ℝ)^2< q.2 ∧ q.2≤ 0 := hq.2
  have htop : max p.2 q.2≤ 0 := max_le hpt.2 hqt.2
  have hspace (x : Space n) (hx : dist x p.1≤ 1/8) : ‖x‖< 1 := by
    have hn := norm_add_le (x-p.1) p.1
    rw [sub_add_cancel] at hn
    rw [dist_eq_norm] at hx
    linarith only [hn,hx,hpx]
  constructor
  · intro z hz
    constructor
    · change dist z.1 0≤ 1
      simpa only [dist_zero_right] using (hspace z.1 hz.1).le
    · have hztime : max p.2 q.2-(1/8 : ℝ)^2≤ z.2 ∧ z.2≤ max p.2 q.2 := hz.2
      change (-1 : ℝ)≤ z.2 ∧ z.2≤ 0
      constructor
      · have hmax := le_max_left p.2 q.2
        linarith only [hztime.1,hpt.1,hmax]
      · exact hztime.2.trans htop
  · intro z hz
    constructor
    · change dist z.1 0< 1
      simpa only [dist_zero_right] using hspace z.1 hz.1.le
    · have hztime : max p.2 q.2-(1/8 : ℝ)^2< z.2 ∧ z.2< max p.2 q.2 := hz.2
      change (-1 : ℝ)< z.2 ∧ z.2< 0
      constructor
      · have hmax := le_max_left p.2 q.2
        linarith only [hztime.1,hpt.1,hmax]
      · exact hztime.2.trans_le htop

theorem auto_pair_in_distance_cylinder {n : ℕ} (p q : Point n) :
    p∈autoClosed p.1 (parabolicDistance p q) (max p.2 q.2) ∧
    q∈autoClosed p.1 (parabolicDistance p q) (max p.2 q.2) := by
  have hd := auto_parabolic_distance_nonneg p q
  have hdx : ‖p.1-q.1‖≤ parabolicDistance p q := le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have hdt := auto_parabolic_distance_time p q
  have hpmax : p.2≤ max p.2 q.2 := le_max_left _ _
  have hqmax : q.2≤ max p.2 q.2 := le_max_right _ _
  have hpt : max p.2 q.2-(parabolicDistance p q)^2≤ p.2 := by
    rcases le_total p.2 q.2 with h | h
    · rw [max_eq_right h]
      linarith only [hdt,neg_le_abs (p.2-q.2)]
    · rw [max_eq_left h]
      linarith only [sq_nonneg (parabolicDistance p q)]
  have hqt : max p.2 q.2-(parabolicDistance p q)^2≤ q.2 := by
    rcases le_total p.2 q.2 with h | h
    · rw [max_eq_right h]
      linarith only [sq_nonneg (parabolicDistance p q)]
    · rw [max_eq_left h]
      linarith only [hdt,le_abs_self (p.2-q.2)]
  constructor
  · exact ⟨by simpa only [Metric.mem_closedBall,dist_self] using hd,hpt,hpmax⟩
  · refine ⟨?_,hqt,hqmax⟩
    simpa only [Metric.mem_closedBall,dist_eq_norm,norm_sub_rev] using hdx

/-- Genuine space-time Hölder regularity from the exact proved Harnack theorem. -/
theorem auto_pucci_holder (n : ℕ) (hn : 0< n) (ell L : ℝ) (hell : 0< ell) (hL : ell≤ L) :
    ∃ delta C : ℝ, 0< delta ∧ delta< 1 ∧ 0< C ∧
      ∀ (w : Point n → ℝ) (M : ℝ), 0≤ M → ContinuousOn w (unitClosed n) →
      (∀ z∈unitClosed n, |w z|≤ M) → autoPucci ell L (unitOpen n) w →
      HolderBound delta (backward (3/4)) w (C*M) := by
  obtain ⟨delta,A,hd,hd1,hA,hOsc⟩ := auto_pucci_cylinder_oscillation hn hell hL
  let V := (1/8 : ℝ)^delta
  let C := 1+2*(A+1)/V
  have hV : 0< V := Real.rpow_pos_of_pos (by norm_num) _
  have hC : 0< C := by dsimp only [C]; positivity
  have hC1 : 1≤ C := by
    dsimp only [C]
    exact le_add_of_nonneg_right (div_nonneg (by positivity) hV.le)
  refine ⟨delta,C,hd,hd1,hC,?_⟩
  intro w M hM hw hb hP
  have hback : backward (3/4 : ℝ)⊆unitClosed n := by
    intro z hz
    constructor
    · change dist z.1 0≤ 1
      have hh : dist z.1 0< 3/4 := hz.1
      linarith only [hh]
    · have hh : -(3/4 : ℝ)^2< z.2 ∧ z.2≤ 0 := hz.2
      change (-1 : ℝ)≤ z.2 ∧ z.2≤ 0
      constructor <;> linarith only [hh.1,hh.2]
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
    by_cases hnear : D≤ 1/8
    · have hbuf := auto_holder_buffer hp hq
      have hcont := hw.mono hbuf.1
      have hclass : autoPucci ell L (autoOpen p.1 (1/8) (max p.2 q.2)) w :=
        ⟨viscositySub_mono_domain hP.1 hbuf.2,viscositySuper_mono_domain hP.2 hbuf.2⟩
      have hrange : ∀ z∈autoClosed p.1 (1/8) (max p.2 q.2), -M≤ w z ∧ w z≤ M :=
        fun z hz => abs_le.mp (hb z (hbuf.1 hz))
      have hpair := auto_pair_in_distance_cylinder p q
      have hh := hOsc p.1 (1/8) (max p.2 q.2) (by norm_num) w (-M) M hcont hrange hclass
        D hDpos hnear p hpair.1 q hpair.2
      rw [Real.div_rpow hD (by norm_num : (0 : ℝ)≤ 1/8)] at hh
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
    · have hfar : (1/8 : ℝ)≤ D := (lt_of_not_ge hnear).le
      have hpw : V≤ D^delta := Real.rpow_le_rpow (by norm_num) hfar hd.le
      have hcoef : 2≤ C*V := by
        dsimp only [C]
        rw [add_mul,one_mul,div_mul_cancel₀ _ hV.ne']
        linarith only [hV.le,hA.le]
      have hh := mul_le_mul_of_nonneg_left hpw (mul_nonneg hC.le hM)
      have htwo := mul_le_mul_of_nonneg_right hcoef hM
      nlinarith only [habs,hh,htwo]
  exact hmain.trans (mul_le_mul_of_nonneg_left hweight (mul_nonneg hC.le hM))

/-- Subtracting the actual zero solution puts the original equation in the two-Pucci class. -/
theorem auto_solution_pucci {n : ℕ} {ell L : ℝ} (hell : 0<ell) (hL : ell≤L)
    {Q : Set (Point n)} (hQ : IsOpen Q) {F : Sym n → ℝ} (hE : globalElliptic F ell L)
    (h0 : F 0=0) {u : Point n → ℝ} (hu : ContinuousOn u Q)
    (hsol : viscositySolution Q (fun H _ => F H) (fun _ => 0) u) : autoPucci ell L Q u := by
  have hz := perron_constant_solution hell hE h0 Q 0
  have hd := auto_difference_pucci hQ hell.le hL hE hu continuousOn_const hsol hz (a := 1) zero_lt_one
  simpa only [one_mul,sub_zero] using hd

end Yau.LeafProofs.L05AutonomousAux
