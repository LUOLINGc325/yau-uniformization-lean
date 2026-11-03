import Yau.LeafProofs.L05AutonomousMollifiedEnergy
import Yau.LeafProofs.L05AutonomousSecondEnergy
import Yau.LeafProofs.L05AutonomousSecondLimit
import Yau.LeafProofs.L05AutonomousCylinderIntegral

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius BoundedContinuousFunction
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

theorem auto_second_congr {n : ℕ} {K : Set (Point n)} {u v : Point n → ℝ}
    (huv : EqOn u v K) (e : Space n) (h : ℝ) (p : Point n) (hp : p∈K)
    (hplus : (p.1+h • e,p.2)∈K) (hminus : (p.1-h • e,p.2)∈K) :
    autoSecond u e h p=autoSecond v e h p := by
  simp only [autoSecond,huv hp,huv hplus,huv hminus]

theorem auto_second_closed_unit {n : ℕ} {R h : ℝ} (hR : 0 < R) (hbuf : R+|h| < 1)
    {e : Space n} (he : ‖e‖ ≤ 1) {p : Point n} (hp : p∈autoClosed (0 : Space n) R 0) :
    p∈unitClosed n ∧ (p.1+h • e,p.2)∈unitClosed n ∧ (p.1-h • e,p.2)∈unitClosed n := by
  have hx : ‖p.1‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hp.1
  have ht : -R^2 ≤ p.2 ∧ p.2 ≤ 0 := by simpa only [zero_sub,mem_Icc] using hp.2
  have hR1 : R < 1 := by linarith only [hbuf,abs_nonneg h]
  have htUnit : p.2∈Icc (-1 : ℝ) 0 := ⟨by nlinarith only [ht.1,hR,hR1],ht.2⟩
  have hv : ‖h • e‖ ≤ |h| := by
    rw [norm_smul,Real.norm_eq_abs]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he (abs_nonneg h)
  exact ⟨⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using hx.trans hR1.le,htUnit⟩,
    ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using
      (norm_add_le p.1 (h • e)).trans ((add_le_add hx hv).trans hbuf.le),htUnit⟩,
    ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using
      (norm_sub_le p.1 (h • e)).trans ((add_le_add hx hv).trans hbuf.le),htUnit⟩⟩

/-- The original data give a uniform positive second-difference bound, through genuine L2 energy. -/
theorem auto_uniform_second_positive :
    ∀ n : ℕ, 0 < n → ∀ ell L : ℝ, 0 < ell → ell ≤ L →
    ∃ C : ℝ, 0 < C ∧
      ∀ F : Sym n → ℝ, Continuous F → globalElliptic F ell L → ConcaveOn ℝ univ F → F 0=0 →
      ∀ u : Point n → ℝ, ContinuousOn u (unitClosed n) → (∀ p∈unitClosed n, |u p|≤ 1) →
        viscositySolution (unitOpen n) (fun H _ => F H) (fun _ => 0) u →
        ∀ e : Space n, ‖e‖=1 → ∀ h : ℝ, h≠0 → |h| < 1/512 →
        ∀ p∈autoClosed (0 : Space n) (23/32) 0, autoSecond u e h p ≤ C := by
  intro n hn ell L hell hL
  obtain ⟨B,E,hB,hE,hForF⟩ := auto_uniform_mollified_energy n hn ell L hell hL
  obtain ⟨D,hD,hSecondEnergy⟩ := auto_spatial_second_energy n
  obtain ⟨K,hK,hMax⟩ := auto_local_maximum_collar n hn ell L hell hL 2 (by norm_num)
    (by norm_num : (0 : ℝ) < 23/32) (by norm_num : (23/32 : ℝ) < 93/128)
  let Q := autoOpen (0 : Space n) (93/128) 0
  let Etot := (93/128 : ℝ)^2*(D*E)
  let C := 1+K*Etot^(1/(2 : ℝ))
  have hEtot : 0 ≤ Etot := by dsimp only [Etot];positivity
  refine ⟨C,by dsimp only [C];positivity,?_⟩
  intro F hF hEll hConc h0 u hu hb hsol e he h hh hsmall p hp
  obtain ⟨A,hA,hForU⟩ := hForF F hF hEll hConc h0
  obtain ⟨w,hwu,hw,hcw,hw1,hPacket⟩ := hForU u hu hb hsol
  let eps := autoDyadicStep (1/128 : ℝ)
  have heps (j : ℕ) : 0 < eps j := auto_dyadicStep_pos (by norm_num) j
  have hepsSmall (j : ℕ) : eps j < 1/64 :=
    (auto_dyadicStep_le (by norm_num : (0 : ℝ) ≤ 1/128) j).trans_lt (by norm_num)
  have hEpsEnergy (j : ℕ) :
      (∫ z in Q, (autoSecond (autoSpatialMollify (eps j) (heps j) w) e h z)^2) ≤ Etot := by
    have hslice (t : ℝ) (ht : t∈Icc (-(93/128 : ℝ)^2) 0) :
        (∫ x in Metric.ball (0 : Space n) (93/128),
          max ((autoSecond (autoSpatialMollify (eps j) (heps j) w) e h (x,t))^2) 0) ≤ D*E := by
      have hs := hSecondEnergy (fun x => autoSpatialMollify (eps j) (heps j) w (x,t))
        (autoSpatialMollify_spatial_contDiff (eps j) (heps j) w hw t)
        (93/128) (47/64) h (by norm_num) (by linarith only [hsmall]) hh e he.le
      have hHess := (hPacket (eps j) (heps j) (hepsSmall j)).2 t ht
      have hbound := hs.2.trans (mul_le_mul_of_nonneg_left hHess.2 hD.le)
      simpa only [autoSpatialSecond,autoSecond,max_eq_left (sq_nonneg _)] using hbound
    have hcont := (autoSecond_continuous (autoSpatialMollify_continuous (eps j) (heps j) w hw) e h).pow 2
    have hCylinder := auto_positive_cylinder_integral
      (by norm_num : -(93/128 : ℝ)^2 ≤ 0) hcont.continuousOn hslice
    simpa only [Q,autoOpen,zero_sub,neg_neg,Pi.pow_apply,max_eq_left (sq_nonneg _),Etot] using hCylinder.2
  let mu : Measure (Point n) := volume.restrict Q
  have hQSubset : Q⊆autoClosed (0 : Space n) (93/128) 0 :=
    fun _ hz => ⟨Metric.ball_subset_closedBall hz.1,Ioo_subset_Icc_self hz.2⟩
  let : IsFiniteMeasure mu := isFiniteMeasure_restrict.mpr
    ((measure_mono hQSubset).trans_lt (autoClosed_isCompact (0 : Space n) (93/128) 0).measure_lt_top).ne
  have hTotal : (∫ z in Q, (autoSecond w e h z)^2) ≤ Etot :=
    auto_second_mollifier_energy_bound mu w hw e hh eps heps (auto_dyadicStep_tendsto _) hEpsEnergy
  have hEq : EqOn (autoSecond w e h) (autoSecond u e h) (autoClosed (0 : Space n) (93/128) 0) := by
    intro z hz
    obtain ⟨hz0,hzPlus,hzMinus⟩ := auto_second_closed_unit (by norm_num : (0 : ℝ) < 93/128)
      (by linarith only [hsmall] : (93/128 : ℝ)+|h| < 1) he.le hz
    exact auto_second_congr hwu e h z hz0 hzPlus hzMinus
  have hsubU := auto_second_sub hn hell hL (by norm_num : (0 : ℝ) < 93/128)
    (by norm_num : (93/128 : ℝ) < 1) hF hEll hConc hu hsol he hh (by linarith only [hsmall])
  have hsubW := viscositySub_eqOn_open (autoOpen_isOpen (0 : Space n) (93/128) 0)
    (hEq.mono hQSubset) hsubU
  have hPositiveTotal : (∫ z in Q, (max (autoSecond w e h z) 0)^(2 : ℝ)) ≤ Etot := by
    have hInt : IntegrableOn (fun z => (autoSecond w e h z)^2) Q :=
      (((autoSecond_continuous w.continuous e h).pow 2).continuousOn.integrableOn_compact
        (autoClosed_isCompact (0 : Space n) (93/128) 0)).mono_set hQSubset
    have hMaxInt : IntegrableOn (fun z => (max (autoSecond w e h z) 0)^2) Q :=
      ((((autoSecond_continuous w.continuous e h).sup continuous_const).pow 2).continuousOn.integrableOn_compact
        (autoClosed_isCompact (0 : Space n) (93/128) 0)).mono_set hQSubset
    have hm := integral_mono hMaxInt hInt (fun z => by
      by_cases hz : 0 ≤ autoSecond w e h z
      · rw [max_eq_left hz]
      · rw [max_eq_right (le_of_not_ge hz)]
        simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0)] using sq_nonneg (autoSecond w e h z))
    simpa only [Real.rpow_two] using hm.trans hTotal
  have hPoint := hMax (autoSecond w e h) (autoSecond_continuous w.continuous e h).continuousOn hsubW p hp
  have hPower := Real.rpow_le_rpow
    (integral_nonneg fun z => Real.rpow_nonneg (le_max_right _ _) _) hPositiveTotal (by norm_num : (0 : ℝ) ≤ 1/2)
  have hUpper : autoSecond w e h p ≤ K*Etot^(1/(2 : ℝ)) :=
    (le_max_left _ _).trans (hPoint.trans (mul_le_mul_of_nonneg_left hPower hK.le))
  rw [hEq (autoClosed_subset 0 (by norm_num) (by norm_num) 0 hp)] at hUpper
  exact hUpper.trans (by dsimp only [C];linarith)

end Yau.LeafProofs.L05AutonomousAux
