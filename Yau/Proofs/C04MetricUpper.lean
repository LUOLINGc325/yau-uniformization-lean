import Yau.Proofs.C04EigenExtrema
import Yau.Proofs.C04GramDeterminant
import Yau.Proofs.C04DistortionScalar
import Yau.Proofs.C04SpatialDensity

/-! C03's static distortion upgrades compact power decay to exponential clock decay. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

namespace Yau.Proofs.C04Aux
open Yau Blueprint
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem compact_metric_upper (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (hH : HarnackCompleteness X o h) (hCharts : UniformCharts X h) (hStatic : StaticDistortion X) :
    ∀ K : Set (Pt X), IsCompact K → ∃ cK, 0 < cK ∧ ∃ T, ∀ t, T ≤ t → ∀ p ∈ K,
      HermLE (gMat (h t) p) ((Real.exp (-cK * ρ o t) : ℂ) • gMat X.metric.form p) := by
  intro K hK
  obtain ⟨r, c, C, Tc, D, hr, hc, hC, hTc, hD, hchart⟩ :=
    original_chart_distortion X o h U P ρ hf hCharts hStatic K hK
  obtain ⟨Tρ, hρ⟩ := compact_rho_ratio X o h U P ρ hf hH K hK (1 / 2) (by norm_num)
  let Aconst := (n : ℝ) * (2 * Real.log D + 2 * D * Real.log 2)
  obtain ⟨Ts, hs⟩ := (tendsto_atTop_atTop.1 (rho_tendsto_atTop X o h U P ρ hf hH))
    (max 1 (4 * |Aconst|))
  let cK := (4 * (n : ℝ) * D)⁻¹
  have hn : 0 < n := dimension_pos X.manifold
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hcK : 0 < cK := inv_pos.mpr (by positivity)
  refine ⟨cK, hcK, max Tc (max Tρ Ts), ?_⟩
  intro t ht p hp
  have htTc : Tc ≤ t := (le_max_left _ _).trans ht
  have ht0 : 0 ≤ t := hTc.trans htTc
  have htρ : Tρ ≤ t := (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have htTs : Ts ≤ t := (le_max_right _ _).trans ((le_max_right _ _).trans ht)
  have hsbound := hs t htTs
  have hspos : 0 < ρ o t := zero_lt_one.trans_le ((le_max_left _ _).trans hsbound)
  have hρlower : ρ o t / 2 ≤ ρ p t := by
    have hh := (abs_le.mp (hρ t htρ p hp)).1
    have hh' : (1 / 2 : ℝ) ≤ ρ p t / ρ o t := by linarith
    have hmul := (le_div_iff₀ hspos).mp hh'
    linarith
  obtain ⟨Φ, hΦ, hdist⟩ := hchart t htTc p hp
  let Pm := Blueprint.Alignment.Y03Proof.centerFrameMatrix p Φ
  let Hm := gMat (h t) p
  let Gm := gMat X.metric.form p
  let Am := pullbackMat X.metric.form Φ 0
  have hgram : Pm.conjTranspose * Hm * Pm = 1 :=
    Blueprint.Alignment.Y03Proof.unitaryChart_centerFrame_gram hΦ
  have hframe : Pm.conjTranspose * Gm * Pm = Am :=
    pullback_zero_eq_conjugate X.metric.form p Φ hΦ.2.1
  have hPm : IsUnit Pm := unitary_frame_isUnit hgram
  have hHm : Hm.PosDef := LeafProofs.L18Aux.hMat_posDef (h t) p (chartPt p p) (mem_extChartAt_target p)
  have hGm : Gm.PosDef := LeafProofs.L18Aux.hMat_posDef X.metric.form p (chartPt p p) (mem_extChartAt_target p)
  have hAm : Am.PosDef := by
    rw [← hframe]
    exact hGm.conjTranspose_mul_mul_same (Matrix.mulVec_injective_iff_isUnit.mpr hPm)
  have hAI : (Am - 1).PosSemidef := by
    have hh := pullbackMat_order (h t) X.metric.form Φ 0 (hf.2.2.2.2.1 t ht0 (Φ 0))
    rw [hΦ.2.2.1] at hh
    exact hh
  obtain ⟨hmin1, hmaxpos, hminLower, hdetmax⟩ := min_max_determinant_bounds hn hAm hAI
  have hdetratio := unitary_gram_determinant_re Hm Gm Pm hHm hgram
  rw [hframe] at hdetratio
  have hratiopos : 0 < Hm.det.re / Gm.det.re :=
    div_pos (Complex.pos_iff.mp hHm.det_pos).1 (Complex.pos_iff.mp hGm.det_pos).1
  have hexp : Real.exp (ρ p t) = Gm.det.re / Hm.det.re := by
    rw [(hf.2.2.2.2.2.2.2.2.2.1 p t ht0).1,
      hf.2.2.2.2.2.2.2.2.1 p t ht0, Real.exp_neg, Real.exp_log hratiopos, inv_div]
  have hdetexp : Real.exp (ρ p t) ≤ (relMaxEigenvalue 1 Am) ^ n :=
    hexp.trans_le (hdetratio.symm.trans_le hdetmax)
  have hexpmin : Real.exp (cK * ρ o t) ≤ relMinEigenvalue 1 Am :=
    distortion_exponential_lower n D _ _ _ _ hn hD hmin1 hmaxpos hdetexp hdist hρlower
      ((le_max_right _ _).trans hsbound)
  have hexpLower : HermLE ((Real.exp (cK * ρ o t) : ℂ) • 1) Am :=
    hermLE_trans (hermLE_real_smul_mono _ Matrix.PosSemidef.one hexpmin) hminLower
  have hreflect : HermLE ((Real.exp (cK * ρ o t) : ℂ) • Hm) Gm := by
    apply conjugate_order_reflect _ _ Pm hPm
    rw [Matrix.mul_smul, Matrix.smul_mul, hgram, hframe]
    exact hexpLower
  have hfactor : (0 : ℂ) ≤ (Real.exp (-cK * ρ o t) : ℂ) :=
    Complex.nonneg_iff.mpr ⟨(Real.exp_pos _).le, by rw [Complex.ofReal_im]⟩
  have hscaled := hreflect.smul (α := ℂ) hfactor
  have hprod : (Real.exp (-cK * ρ o t) : ℂ) * (Real.exp (cK * ρ o t) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    rw [show -cK * ρ o t + cK * ρ o t = 0 by ring, Real.exp_zero, Complex.ofReal_one]
  change (((Real.exp (-cK * ρ o t) : ℂ) • Gm) - Hm).PosSemidef
  simpa only [smul_sub, smul_smul, hprod, one_smul] using hscaled

end Yau.Proofs.C04Aux
