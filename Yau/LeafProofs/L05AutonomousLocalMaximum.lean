import Yau.LeafProofs.L05AutonomousHarnackMaxGeometry
import Yau.LeafProofs.L05AutonomousHarnackChebyshev

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

theorem autoBoundaryDistance_open_cylinder {n : ℕ} {z : Point n} (hz : z∈unitClosed n)
    {kappa : ℝ} (hk : 0< kappa) (hk1 : kappa< 1) (hD : 0< autoBoundaryDistance z) :
    autoOpen z.1 (kappa*autoBoundaryDistance z) z.2⊆unitOpen n := by
  have hgeo := autoBoundaryDistance_cylinder hz hk hk1 hD
  intro q hq
  have hc : q∈autoClosed z.1 (kappa*autoBoundaryDistance z) z.2 :=
    ⟨Metric.ball_subset_closedBall hq.1,hq.2.1.le,hq.2.2.le⟩
  have hpos : 0< autoBoundaryDistance q :=
    (mul_pos (sub_pos.mpr hk1) hD).trans_le (hgeo.2 q hc)
  have hx := hpos.trans_le (min_le_left (1-‖q.1‖) (Real.sqrt (q.2+1)))
  have ht := Real.sqrt_pos.mp (hpos.trans_le (min_le_right (1-‖q.1‖) (Real.sqrt (q.2+1))))
  constructor
  · change dist q.1 0< 1
    rw [dist_zero_right]
    linarith only [hx]
  · change (-1 : ℝ)< q.2 ∧ q.2< 0
    exact ⟨by linarith only [ht],hq.2.2.trans_le hz.2.2⟩

theorem autoEarly_subset_closed {n : ℕ} (c : Space n) {R : ℝ} (hR : 0< R) (T : ℝ) :
    autoEarly c R T⊆autoClosed c R T := by
  intro q hq
  have hh := autoEarly_subset_open c hR T hq
  exact ⟨Metric.ball_subset_closedBall hh.1,hh.2.1.le,hh.2.2.le⟩

/-- The actual weighted maximum has a universal Lp budget, with its full unknown amplitude cancelled. -/
theorem auto_weighted_pucci_mass (n : ℕ) (hn : 0< n) (ell L : ℝ) (hell : 0< ell) (hL : ell≤ L)
    (p : ℝ) (hp : 0< p) :
    ∃ a : ℝ, 0< a ∧ ∀ w : Point n → ℝ, ContinuousOn w (unitClosed n) →
      viscositySub (unitOpen n) (fun H _ => pucciPlus ell L H) (fun _ => 0) w →
      ∃ z∈unitClosed n,
        (∀ q∈unitClosed n,
          (autoBoundaryDistance q)^((2*n+2 : ℕ)/p)*max (w q) 0≤
          (autoBoundaryDistance z)^((2*n+2 : ℕ)/p)*max (w z) 0) ∧
        a*((autoBoundaryDistance z)^((2*n+2 : ℕ)/p)*max (w z) 0)^p≤
          ∫ q in unitOpen n, (max (w q) 0)^p := by
  obtain ⟨p₀,C,hp₀,hp₀1,hC,hWH⟩ := auto_weak_harnack_scaled_top hn hell hL
  let N : ℕ := 2*n+2
  let beta : ℝ := (N : ℝ)/p
  have hbeta : 0< beta := div_pos (by dsimp only [N]; positivity) hp
  let eps := 1/(4*C)
  have heps : 0< eps := one_div_pos.mpr (mul_pos (by norm_num) hC)
  obtain ⟨kappa,hk,hk1,hkp⟩ := auto_harnack_kappa hbeta heps
  let theta := 1-(1/2 : ℝ)^p₀
  have htheta : 0< theta := sub_pos.mpr (Real.rpow_lt_one (by norm_num) (by norm_num) hp₀)
  let a := theta*harnackMu (harnackQminus n)*kappa^N*(1/2 : ℝ)^p
  have hqmu : 0< harnackMu (harnackQminus n) := harnack_qminus_mu_pos n
  have ha : 0< a := by dsimp only [a]; positivity
  refine ⟨a,ha,?_⟩
  intro w hw hSub
  obtain ⟨z,hz,hmax⟩ := auto_boundary_weight_maximizer hbeta hw
  refine ⟨z,hz,hmax,?_⟩
  let D := autoBoundaryDistance z
  let K := w z
  let W := D^beta*max K 0
  change a*W^p≤ ∫ q in unitOpen n, (max (w q) 0)^p
  have hDnonneg : 0≤ D := autoBoundaryDistance_nonneg hz
  have hWnonneg : 0≤ W := mul_nonneg (Real.rpow_nonneg hDnonneg beta) (le_max_right K 0)
  by_cases hzero : W=0
  · rw [hzero,Real.zero_rpow hp.ne',mul_zero]
    exact integral_nonneg fun q => Real.rpow_nonneg (le_max_right (w q) 0) p
  have hD : 0< D := by
    by_contra hno
    have hh : D=0 := le_antisymm (le_of_not_gt hno) hDnonneg
    have hwzero : W=0 := by dsimp only [W]; rw [hh,Real.zero_rpow hbeta.ne',zero_mul]
    exact hzero hwzero
  have hK : 0< K := by
    by_contra hno
    have hh : K≤ 0 := le_of_not_gt hno
    have hwzero : W=0 := by dsimp only [W]; rw [max_eq_right hh,mul_zero]
    exact hzero hwzero
  have hWeq : W=D^beta*K := by dsimp only [W]; rw [max_eq_left hK.le]
  let r := kappa*D
  have hr : 0< r := mul_pos hk hD
  have hgeo := autoBoundaryDistance_cylinder hz hk hk1 hD
  have hopen := autoBoundaryDistance_open_cylinder hz hk hk1 hD
  have henvelope := auto_weighted_maximum_envelope hbeta hk hk1 hz hD hK hmax
  have hbound : ∀ q∈autoClosed z.1 r z.2, w q≤ (1+eps)*K := by
    intro q hq
    have hh := henvelope q hq
    simpa only [hkp,K] using hh
  let v : Point n → ℝ := fun q => (1+eps)*K-w q
  have hv : ContinuousOn v (autoClosed z.1 r z.2) := continuousOn_const.sub (hw.mono hgeo.1)
  have hv0 : ∀ q∈autoClosed z.1 r z.2, 0≤ v q := fun q hq => sub_nonneg.mpr (hbound q hq)
  have hsuper : viscositySuper (autoOpen z.1 r z.2)
      (fun H _ => -pucciPlus ell L (-H)) (fun _ => 0) v :=
    auto_pucci_deficit_super (viscositySub_mono_domain hSub hopen) ((1+eps)*K)
  have hmean := hWH z.1 r z.2 hr v hv hv0 hsuper
  have hcenter : C*v (z.1,z.2)=K/4 := by
    dsimp only [v,eps,K]
    simp only [Prod.eta]
    field_simp
    ring
  rw [hcenter] at hmean
  let E := autoEarly z.1 r z.2
  let G := autoDeficitGood E v K
  have hE : MeasurableSet E := (autoEarly_isOpen z.1 r z.2).measurableSet
  have hEs : E⊆autoClosed z.1 r z.2 := autoEarly_subset_closed z.1 hr z.2
  have hvi : IntegrableOn (fun q => (v q)^p₀) E :=
    ((hv.rpow_const (fun _ _ => Or.inr hp₀.le)).integrableOn_compact
      ((isCompact_closedBall z.1 r).prod isCompact_Icc)).mono_set hEs
  have hG : MeasurableSet G := ((hv.mono hEs).isOpen_inter_preimage
    (autoEarly_isOpen z.1 r z.2) isOpen_Iio).measurableSet
  have hmass := auto_deficit_good_mass hE (autoEarly_measure_ne_top z.1 r z.2)
    (autoEarly_mu_pos z.1 hr z.2) hp₀ hK (fun q hq => hv0 q (hEs hq)) hvi hG hmean
  have hGunit : G⊆unitOpen n := inter_subset_left.trans ((autoEarly_subset_open z.1 hr z.2).trans hopen)
  have hhigh : ∀ q∈G, K/2≤ w q := by
    intro q hq
    have hh : v q< K/2 := hq.2
    dsimp only [v] at hh
    have hmul := mul_nonneg heps.le hK.le
    nlinarith only [hh,hmul]
  have hlarge := auto_large_set_positive_integral hw hG hGunit hp hK.le hhigh
  have hfactor : 0≤ (K/2)^p := Real.rpow_nonneg (div_nonneg hK.le (by norm_num)) p
  have hmul := mul_le_mul_of_nonneg_right hmass hfactor
  have hlower := hmul.trans hlarge
  change theta*harnackMu (autoEarly z.1 r z.2)*(K/2)^p≤ _ at hlower
  rw [autoEarly_volume z.1 hr z.2] at hlower
  have hN : beta*p=(N : ℝ) := by dsimp only [beta]; exact div_mul_cancel₀ _ hp.ne'
  have hWP : W^p=D^N*K^p := by
    rw [hWeq,Real.mul_rpow (Real.rpow_nonneg hD.le beta) hK.le,← Real.rpow_mul hD.le,hN,Real.rpow_natCast]
  have hid : a*W^p=theta*(r^(2*n+2)*harnackMu (harnackQminus n))*(K/2)^p := by
    rw [hWP,show K/2=K*(1/2 : ℝ) by ring,Real.mul_rpow hK.le (by norm_num)]
    dsimp only [a,r,N]
    rw [mul_pow]
    ring
  rw [hid]
  exact hlower

/-- Local maximum for every p> 0, with the entire candidate-dependent maximum eliminated. -/
theorem auto_local_maximum (n : ℕ) (hn : 0< n) (ell L : ℝ) (hell : 0< ell) (hL : ell≤ L)
    (p : ℝ) (hp : 0< p) :
    ∃ C : ℝ, 0< C ∧ ∀ w : Point n → ℝ, ContinuousOn w (unitClosed n) →
      viscositySub (unitOpen n) (fun H _ => pucciPlus ell L H) (fun _ => 0) w →
      ∀ q∈backward (1/2), max (w q) 0≤ C*((∫ y in unitOpen n, (max (w y) 0)^p))^(1/p) := by
  obtain ⟨a,ha,hMass⟩ := auto_weighted_pucci_mass n hn ell L hell hL p hp
  let beta : ℝ := (2*n+2 : ℕ)/p
  let B := (2 : ℝ)^beta
  let A := a^(1/p)
  let C := B/A
  have hbeta : 0< beta := div_pos (by positivity) hp
  have hB : 0< B := Real.rpow_pos_of_pos (by norm_num) _
  have hA : 0< A := Real.rpow_pos_of_pos ha _
  refine ⟨C,div_pos hB hA,?_⟩
  intro w hw hSub
  obtain ⟨z,hz,hmax,hmass⟩ := hMass w hw hSub
  let W := (autoBoundaryDistance z)^beta*max (w z) 0
  let totalIntegral := ∫ y in unitOpen n, (max (w y) 0)^p
  have hW : 0≤ W := mul_nonneg (Real.rpow_nonneg (autoBoundaryDistance_nonneg hz) beta) (le_max_right _ _)
  change a*W^p≤ totalIntegral at hmass
  have hroot := Real.rpow_le_rpow (mul_nonneg ha.le (Real.rpow_nonneg hW p)) hmass (one_div_pos.mpr hp).le
  rw [Real.mul_rpow ha.le (Real.rpow_nonneg hW p),← Real.rpow_mul hW,
    show p*(1/p)=1 by field_simp [hp.ne'],Real.rpow_one] at hroot
  change A*W≤ totalIntegral^(1/p) at hroot
  have hhalf : B*(1/2 : ℝ)^beta=1 := by
    dsimp only [B]
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ)≤ 2) (by norm_num : (0 : ℝ)≤ 1/2),
      show (2 : ℝ)*(1/2)=1 by ring,Real.one_rpow]
  intro q hq
  have hqU : q∈unitClosed n := by
    constructor
    · exact Metric.closedBall_subset_closedBall (by norm_num : (1/2 : ℝ)≤ 1) (Metric.ball_subset_closedBall hq.1)
    · have ht : -(1/2 : ℝ)^2< q.2 ∧ q.2≤ 0 := hq.2
      change (-1 : ℝ)≤ q.2 ∧ q.2≤ 0
      constructor <;> linarith only [ht.1,ht.2]
  have hlower := Real.rpow_le_rpow (by norm_num : (0 : ℝ)≤ 1/2) (autoBoundaryDistance_half hq) hbeta.le
  have hpoint := (mul_le_mul_of_nonneg_right hlower (le_max_right (w q) 0)).trans (hmax q hqU)
  change (1/2 : ℝ)^beta*max (w q) 0≤ W at hpoint
  have hpointB : max (w q) 0≤ B*W := by
    have hh := mul_le_mul_of_nonneg_left hpoint hB.le
    have heq : B*((1/2 : ℝ)^beta*max (w q) 0)=max (w q) 0 := by rw [← mul_assoc,hhalf,one_mul]
    rwa [heq] at hh
  have hbound : max (w q) 0*A≤ B*totalIntegral^(1/p) := by
    have hleft := mul_le_mul_of_nonneg_left hpointB hA.le
    have hright := mul_le_mul_of_nonneg_left hroot hB.le
    nlinarith only [hleft,hright]
  change max (w q) 0≤ (B/A)*totalIntegral^(1/p)
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hA).mpr hbound

end Yau.LeafProofs.L05AutonomousAux
