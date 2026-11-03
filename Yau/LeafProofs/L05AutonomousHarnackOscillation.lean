import Yau.LeafProofs.L05AutonomousHarnackScaling

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- This total expression is used below only after genuine compact-image bounds are proved. -/
def autoOsc {n : ℕ} (w : Point n → ℝ) (Q : Set (Point n)) : ℝ :=
  sSup (w '' Q)-sInf (w '' Q)

theorem auto_osc_bounds {n : ℕ} {w : Point n → ℝ} {Q : Set (Point n)}
    (hQ : IsCompact Q) (hw : ContinuousOn w Q) :
    ∀ z∈Q, sInf (w '' Q)≤ w z ∧ w z≤ sSup (w '' Q) := by
  have hIm := hQ.image_of_continuousOn hw
  intro z hz
  exact ⟨csInf_le hIm.bddBelow ⟨z,hz,rfl⟩,le_csSup hIm.bddAbove ⟨z,hz,rfl⟩⟩

theorem auto_osc_nonneg {n : ℕ} {w : Point n → ℝ} {Q : Set (Point n)}
    (hQ : IsCompact Q) (hne : Q.Nonempty) (hw : ContinuousOn w Q) : 0≤ autoOsc w Q := by
  obtain ⟨z,hz⟩ := hne
  have hb := auto_osc_bounds hQ hw z hz
  dsimp only [autoOsc]
  linarith only [hb.1,hb.2]

theorem auto_osc_pair_le {n : ℕ} {w : Point n → ℝ} {Q : Set (Point n)}
    (hQ : IsCompact Q) (hw : ContinuousOn w Q) {z q : Point n} (hz : z∈Q) (hq : q∈Q) :
    |w z-w q|≤ autoOsc w Q := by
  have hz' := auto_osc_bounds hQ hw z hz
  have hq' := auto_osc_bounds hQ hw q hq
  dsimp only [autoOsc]
  exact abs_le.mpr ⟨by linarith only [hz'.1,hq'.2],by linarith only [hz'.2,hq'.1]⟩

theorem auto_osc_le_of_pair {n : ℕ} {w : Point n → ℝ} {Q : Set (Point n)} {K : ℝ}
    (hQ : IsCompact Q) (hne : Q.Nonempty) (hw : ContinuousOn w Q)
    (hp : ∀ z∈Q, ∀ q∈Q, w z-w q≤ K) : autoOsc w Q≤ K := by
  have him := hQ.image_of_continuousOn hw
  obtain ⟨z,hz,hzv⟩ := him.sSup_mem (hne.image w)
  obtain ⟨q,hq,hqv⟩ := him.sInf_mem (hne.image w)
  have hh := hp z hz q hq
  simpa only [autoOsc,hzv,hqv] using hh

theorem autoClosed_isCompact {n : ℕ} (c : Space n) (R T : ℝ) : IsCompact (autoClosed c R T) :=
  (isCompact_closedBall c R).prod isCompact_Icc

theorem autoClosed_nonempty {n : ℕ} (c : Space n) {R : ℝ} (hR : 0≤ R) (T : ℝ) :
    (autoClosed c R T).Nonempty := by
  refine ⟨(c,T),?_⟩
  change dist c c≤ R ∧ T-R^2≤ T ∧ T≤ T
  rw [dist_self]
  exact ⟨hR,sub_le_self _ (sq_nonneg R),le_rfl⟩

theorem autoClosed_subset {n : ℕ} (c : Space n) {r R : ℝ} (hr : 0≤ r) (hrR : r≤ R) (T : ℝ) :
    autoClosed c r T⊆autoClosed c R T := by
  intro z hz
  refine ⟨Metric.closedBall_subset_closedBall hrR hz.1,?_⟩
  have hs := (sq_le_sq₀ hr (hr.trans hrR)).mpr hrR
  change T-R^2≤ z.2 ∧ z.2≤ T
  have ht : T-r^2≤ z.2 ∧ z.2≤ T := hz.2
  constructor <;> linarith only [ht.1,ht.2,hs]

theorem autoOpen_subset {n : ℕ} (c : Space n) {r R : ℝ} (hr : 0≤ r) (hrR : r≤ R) (T : ℝ) :
    autoOpen c r T⊆autoOpen c R T := by
  intro z hz
  refine ⟨Metric.ball_subset_ball hrR hz.1,?_⟩
  have hs := (sq_le_sq₀ hr (hr.trans hrR)).mpr hrR
  change T-R^2< z.2 ∧ z.2< T
  have ht : T-r^2< z.2 ∧ z.2< T := hz.2
  constructor <;> linarith only [ht.1,ht.2,hs]

def autoQuarterRadius (R : ℝ) (j : ℕ) : ℝ := R*(1/4 : ℝ)^j

theorem autoQuarterRadius_pos {R : ℝ} (hR : 0< R) (j : ℕ) : 0< autoQuarterRadius R j := by
  dsimp only [autoQuarterRadius]
  positivity

theorem autoQuarterRadius_le {R : ℝ} (hR : 0≤ R) (j : ℕ) : autoQuarterRadius R j≤ R := by
  have hh := pow_le_one₀ (by norm_num : (0 : ℝ)≤ 1/4) (by norm_num : (1/4 : ℝ)≤ 1) (n := j)
  simpa only [autoQuarterRadius,mul_one] using mul_le_mul_of_nonneg_left hh hR

theorem autoQuarterRadius_succ (R : ℝ) (j : ℕ) :
    autoQuarterRadius R (j+1)=autoQuarterRadius R j/4 := by
  dsimp only [autoQuarterRadius]
  rw [pow_succ]
  ring

/-- Choose a genuine power strictly slower than the proved contraction, before any candidate. -/
theorem auto_choose_holder_exponent {theta : ℝ} (ht : theta< 1) :
    ∃ delta : ℝ, 0< delta ∧ delta< 1 ∧ theta< (1/4 : ℝ)^delta := by
  let delta := min (1/2) ((1-theta)/4)
  have hd : 0< delta := lt_min (by norm_num) (div_pos (sub_pos.mpr ht) (by norm_num))
  have hd1 : delta< 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hdt : delta≤ (1-theta)/4 := min_le_right _ _
  have hlog : Real.log 4< 4 := (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)< 4)).trans_lt (by norm_num)
  have hexp : (1/4 : ℝ)^delta=Real.exp (-delta*Real.log 4) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ)< 1/4),one_div,Real.log_inv]
    congr 1
    ring
  have hlower : 1-delta*Real.log 4≤ (1/4 : ℝ)^delta := by
    rw [hexp]
    have hh := Real.add_one_le_exp (-delta*Real.log 4)
    linarith only [hh]
  have hmul := mul_lt_mul_of_pos_left hlog hd
  exact ⟨delta,hd,hd1,(by nlinarith only [hdt,hmul] : theta< 1-delta*Real.log 4).trans_le hlower⟩

/-- Actual geometric decay of the compact-image oscillations follows from the native equations. -/
theorem auto_pucci_cylinder_oscillation {n : ℕ} (hn : 0< n) {ell L : ℝ}
    (hell : 0< ell) (hL : ell≤ L) :
    ∃ delta C : ℝ, 0< delta ∧ delta< 1 ∧ 0< C ∧
      ∀ (c : Space n) (R T : ℝ), 0< R → ∀ (w : Point n → ℝ) (m M : ℝ),
      ContinuousOn w (autoClosed c R T) → (∀ z∈autoClosed c R T, m≤ w z ∧ w z≤ M) →
      autoPucci ell L (autoOpen c R T) w → ∀ r : ℝ, 0< r → r≤ R →
      ∀ z∈autoClosed c r T, ∀ q∈autoClosed c r T,
        |w z-w q|≤ C*(r/R)^delta*(M-m) := by
  obtain ⟨a,ha,ha1,hstep⟩ := auto_pucci_scaled_quarter_contraction hn hell hL
  let theta := 1-a
  have ht : 0< theta := sub_pos.mpr ha1
  have ht1 : theta< 1 := sub_lt_self _ ha
  obtain ⟨delta,hd,hd1,hslow⟩ := auto_choose_holder_exponent ht1
  let C := (4 : ℝ)^delta
  refine ⟨delta,C,hd,hd1,by dsimp only [C]; positivity,?_⟩
  intro c R T hR w m M hw hb hP r hr hrR z hz q hq
  let Q (j : ℕ) := autoClosed c (autoQuarterRadius R j) T
  have hRad (j : ℕ) := autoQuarterRadius_pos hR j
  have hSub (j : ℕ) : Q j⊆autoClosed c R T :=
    autoClosed_subset c (hRad j).le (autoQuarterRadius_le hR.le j) T
  have hQC (j : ℕ) : IsCompact (Q j) := autoClosed_isCompact _ _ _
  have hQN (j : ℕ) : (Q j).Nonempty := autoClosed_nonempty c (hRad j).le T
  have hwj (j : ℕ) : ContinuousOn w (Q j) := hw.mono (hSub j)
  have hO (j : ℕ) : 0≤ autoOsc w (Q j) := auto_osc_nonneg (hQC j) (hQN j) (hwj j)
  have hDecay : ∀ j : ℕ, autoOsc w (Q j)≤ theta^j*(M-m) := by
    intro j
    induction j with
    | zero =>
      simp only [pow_zero,one_mul]
      apply auto_osc_le_of_pair (hQC 0) (hQN 0) (hwj 0)
      intro x hx y hy
      have hx' := hb x (hSub 0 hx)
      have hy' := hb y (hSub 0 hy)
      linarith only [hx'.2,hy'.1]
    | succ j ih =>
      have hrange := auto_osc_bounds (hQC j) (hwj j)
      have hPj : autoPucci ell L (autoOpen c (autoQuarterRadius R j) T) w :=
        ⟨viscositySub_mono_domain hP.1 (autoOpen_subset c (hRad j).le (autoQuarterRadius_le hR.le j) T),
          viscositySuper_mono_domain hP.2 (autoOpen_subset c (hRad j).le (autoQuarterRadius_le hR.le j) T)⟩
      have hnext := hstep c (autoQuarterRadius R j) T (hRad j) w
        (sInf (w '' Q j)) (sSup (w '' Q j)) (hwj j) hrange hPj
      have hh : autoOsc w (Q (j+1))≤ theta*autoOsc w (Q j) := by
        apply auto_osc_le_of_pair (hQC (j+1)) (hQN (j+1)) (hwj (j+1))
        simpa only [Q,autoQuarterRadius_succ,theta,autoOsc] using hnext
      calc
        _ ≤ theta*autoOsc w (Q j) := hh
        _ ≤ theta*(theta^j*(M-m)) := mul_le_mul_of_nonneg_left ih ht.le
        _ = _ := by rw [pow_succ]; ring
  obtain ⟨j,hjlow,hjup⟩ := exists_nat_pow_near_of_lt_one (div_pos hr hR)
    ((div_le_one hR).mpr hrR) (by norm_num : (0 : ℝ)< 1/4) (by norm_num : (1/4 : ℝ)< 1)
  have hrj : r≤ autoQuarterRadius R j := by
    have hh := (div_le_iff₀ hR).mp hjup
    simpa only [autoQuarterRadius,mul_comm] using hh
  have hnear : (1/4 : ℝ)^j≤ 4*(r/R) := by rw [pow_succ] at hjlow; linarith only [hjlow]
  have hpower : theta^j≤ (4 : ℝ)^delta*(r/R)^delta := by
    calc
      _ ≤ ((1/4 : ℝ)^delta)^j := pow_le_pow_left₀ ht.le hslow.le j
      _ = ((1/4 : ℝ)^j)^delta := by
        rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ)≤ 1/4),
          mul_comm delta (j : ℝ),Real.rpow_natCast_mul (by norm_num : (0 : ℝ)≤ 1/4)]
      _ ≤ (4*(r/R))^delta := Real.rpow_le_rpow (pow_nonneg (by norm_num) _) hnear hd.le
      _ = _ := Real.mul_rpow (by norm_num) (div_nonneg hr.le hR.le)
  have hMm : 0≤ M-m := by
    obtain ⟨x,hx⟩ := autoClosed_nonempty c hR.le T
    have hh := hb x hx
    linarith only [hh.1,hh.2]
  calc
    _ ≤ autoOsc w (Q j) := auto_osc_pair_le (hQC j) (hwj j)
      (autoClosed_subset c hr.le hrj T hz) (autoClosed_subset c hr.le hrj T hq)
    _ ≤ theta^j*(M-m) := hDecay j
    _ ≤ ((4 : ℝ)^delta*(r/R)^delta)*(M-m) := mul_le_mul_of_nonneg_right hpower hMm

end Yau.LeafProofs.L05AutonomousAux
