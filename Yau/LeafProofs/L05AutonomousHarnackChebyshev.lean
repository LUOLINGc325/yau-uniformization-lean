import Yau.LeafProofs.L05AutonomousHarnackMean

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

def autoDeficitGood {n : ℕ} (E : Set (Point n)) (v : Point n → ℝ) (K : ℝ) : Set (Point n) :=
  E ∩ v ⁻¹' Iio (K/2)

/-- Genuine Bochner Chebyshev: a small early Lp deficit leaves a uniformly large good set. -/
theorem auto_deficit_good_mass {n : ℕ} {E : Set (Point n)} (hE : MeasurableSet E)
    (hfinite : (volume : Measure (Point n)) E≠⊤) (hmu : 0< harnackMu E)
    {v : Point n → ℝ} {p K : ℝ} (hp : 0< p) (hK : 0< K)
    (hv0 : ∀ z∈E, 0≤ v z) (hvi : IntegrableOn (fun z => (v z)^p) E)
    (hG : MeasurableSet (autoDeficitGood E v K)) (hmean : autoLpMean E p v≤ K/4) :
    (1-(1/2 : ℝ)^p)*harnackMu E≤ harnackMu (autoDeficitGood E v K) := by
  let G := autoDeficitGood E v K
  let H := E \ G
  have hGsub : G⊆E := inter_subset_left
  have hHsub : H⊆E := sdiff_subset
  have hH : MeasurableSet H := hE.diff hG
  have hHfinite : (volume : Measure (Point n)) H≠⊤ := measure_ne_top_of_subset hHsub hfinite
  have hI0 : 0≤ ∫ z in E, (v z)^p := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem hE] with z hz
    exact Real.rpow_nonneg (hv0 z hz) p
  have hmean0 : 0≤ autoLpMean E p v := Real.rpow_nonneg (div_nonneg hI0 hmu.le) _
  have hpower := Real.rpow_le_rpow hmean0 hmean hp.le
  change (((∫ z in E, (v z)^p)/harnackMu E)^(1/p))^p≤ (K/4)^p at hpower
  rw [← Real.rpow_mul (div_nonneg hI0 hmu.le),show (1/p)*p=1 by field_simp [hp.ne'],Real.rpow_one] at hpower
  have hupper : (∫ z in E, (v z)^p)≤ (K/4)^p*harnackMu E := (div_le_iff₀ hmu).mp hpower
  have hconst : IntegrableOn (fun _ : Point n => (K/2)^p) H := integrableOn_const hHfinite
  have hlocal := integral_mono_ae hconst (hvi.mono_set hHsub) (by
    filter_upwards [ae_restrict_mem hH] with z hz
    have hzv : K/2≤ v z := by
      by_contra hno
      have hh : z∈G := ⟨hz.1,lt_of_not_ge hno⟩
      exact hz.2 hh
    exact Real.rpow_le_rpow (div_nonneg hK.le (by norm_num)) hzv hp.le)
  have hrestrict := setIntegral_mono_set hvi (by
    filter_upwards [ae_restrict_mem hE] with z hz
    exact Real.rpow_nonneg (hv0 z hz) p) (ae_of_all volume fun z hz => hHsub hz)
  have hbadIntegral : harnackMu H*(K/2)^p≤ (K/4)^p*harnackMu E := by
    have hh := hlocal.trans (hrestrict.trans hupper)
    simpa only [setIntegral_const,smul_eq_mul,measureReal_def,harnackMu] using hh
  have hthreshold : 0< (K/2)^p := Real.rpow_pos_of_pos (div_pos hK (by norm_num)) _
  have hscale : (K/4)^p=(1/2 : ℝ)^p*(K/2)^p := by
    rw [show K/4=(1/2 : ℝ)*(K/2) by ring,Real.mul_rpow (by norm_num) (div_nonneg hK.le (by norm_num))]
  rw [hscale] at hbadIntegral
  have hbad : harnackMu H≤ (1/2 : ℝ)^p*harnackMu E := by
    apply (mul_le_mul_iff_of_pos_right hthreshold).mp
    convert hbadIntegral using 1
    ring
  have hpartition := measureReal_inter_add_sdiff (μ := (volume : Measure (Point n))) (s := E) hG hfinite
  rw [inter_eq_right.mpr hGsub] at hpartition
  change harnackMu G+harnackMu H=harnackMu E at hpartition
  change (1-(1/2 : ℝ)^p)*harnackMu E≤ harnackMu G
  nlinarith only [hbad,hpartition]

/-- An actual large high-value set gives the required positive Lp mass in the original domain. -/
theorem auto_large_set_positive_integral {n : ℕ} {w : Point n → ℝ}
    (hw : ContinuousOn w (unitClosed n)) {G : Set (Point n)} (hG : MeasurableSet G)
    (hGsub : G⊆unitOpen n) {p K : ℝ} (hp : 0< p) (hK : 0≤ K)
    (hhigh : ∀ z∈G, K/2≤ w z) :
    harnackMu G*(K/2)^p≤ ∫ z in unitOpen n, (max (w z) 0)^p := by
  have hc : IsCompact (unitClosed n) := (isCompact_closedBall (0 : Space n) 1).prod isCompact_Icc
  have hcont : ContinuousOn (fun z => (max (w z) 0)^p) (unitClosed n) :=
    (hw.sup continuousOn_const).rpow_const (fun _ _ => Or.inr hp.le)
  have hint : IntegrableOn (fun z => (max (w z) 0)^p) (unitOpen n) :=
    (hcont.integrableOn_compact hc).mono_set unitOpen_subset_unitClosed
  have hfinite : (volume : Measure (Point n)) G≠⊤ :=
    measure_ne_top_of_subset (hGsub.trans unitOpen_subset_unitClosed) hc.measure_lt_top.ne
  have hconst : IntegrableOn (fun _ : Point n => (K/2)^p) G := integrableOn_const hfinite
  have hlocal := integral_mono_ae hconst (hint.mono_set hGsub) (by
    filter_upwards [ae_restrict_mem hG] with z hz
    exact Real.rpow_le_rpow (div_nonneg hK (by norm_num)) ((hhigh z hz).trans (le_max_left _ _)) hp.le)
  have hrestrict := setIntegral_mono_set hint (by
    filter_upwards with z
    exact Real.rpow_nonneg (le_max_right (w z) 0) p) (ae_of_all volume fun z hz => hGsub hz)
  have hh := hlocal.trans hrestrict
  simpa only [setIntegral_const,smul_eq_mul,measureReal_def,harnackMu] using hh

end Yau.LeafProofs.L05AutonomousAux
