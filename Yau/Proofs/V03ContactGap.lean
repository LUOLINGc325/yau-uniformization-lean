import Yau.Proofs.V03FunctionalLower

/-! The strict contact gives a positive lower bound away from its center
on the original compact cylinder. All values retain EReal endpoint semantics. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

def contactTest (d : VariationData X q) (p : CotangentCoord n × ℝ) : ℝ :=
  d.test (cotangentChartInv d.chart p.1) p.2

def contactEnvelope (d : VariationData X q) (p : CotangentCoord n × ℝ) : EReal :=
  envelopeChart d.h d.T d.chart (p.1.1, p.1.2, p.2)

def contactGap (d : VariationData X q) (p : CotangentCoord n × ℝ) : EReal :=
  contactEnvelope d p - (contactTest d p : EReal)

theorem contactTest_continuousOn {d : VariationData X q} (hd : VariationSetup d) :
    ContinuousOn (contactTest d) (centerCylinder d) := by
  obtain ⟨V, _, hCV, _, htest⟩ := hd.2.2.2.2.2.2.2.1.2.2.2.2.2.2
  exact htest.continuousOn.mono hCV

theorem contactEnvelope_lowerSemicontinuousOn {d : VariationData X q} (hd : VariationSetup d) :
    LowerSemicontinuousOn (contactEnvelope d) (centerCylinder d) := by
  have hc := hd.2.2.2.2.2.2.2.1
  let flat : CotangentCoord n × ℝ → ComplexVector n × ComplexVector n × ℝ :=
    fun p => (p.1.1, p.1.2, p.2)
  have hflat : Continuous flat :=
    (continuous_fst.comp continuous_fst).prodMk
      ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  exact (envelopeChart_lowerSemicontinuousOn d.h d.T d.chart).comp hflat.continuousOn
    (fun p hp => ⟨(hc.2.2.1 hp).1.1, (hc.2.2.1 hp).2⟩)

theorem contactGap_lowerSemicontinuousOn {d : VariationData X q} (hd : VariationSetup d) :
    LowerSemicontinuousOn (contactGap d) (centerCylinder d) := by
  have hneg : ContinuousOn (fun p => ((-contactTest d p : ℝ) : EReal)) (centerCylinder d) :=
    continuous_coe_real_ereal.comp_continuousOn (contactTest_continuousOn hd).neg
  have hh := (contactEnvelope_lowerSemicontinuousOn hd).add' hneg.lowerSemicontinuousOn
    (fun p _ => EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _))
      (Or.inr (EReal.coe_ne_top _)))
  intro p hp a ha
  have ha' : a < contactEnvelope d p + ((-contactTest d p : ℝ) : EReal) := by
    simpa only [contactGap, sub_eq_add_neg, EReal.coe_neg] using ha
  filter_upwards [hh p hp a ha'] with z hz
  simpa only [contactGap, sub_eq_add_neg, EReal.coe_neg] using hz

theorem contactGap_pos {d : VariationData X q} (hd : VariationSetup d)
    {p : CotangentCoord n × ℝ} (hp : p ∈ centerCylinder d) (hne : p ≠ d.contact) :
    0 < contactGap d p := by
  have hc := hd.2.2.2.2.2.2.2.1
  apply EReal.sub_pos.mpr
  exact lt_of_le_of_ne (hc.2.2.2.1 p hp)
    (fun heq => hne ((hc.2.2.2.2.1 p hp).mp heq))

theorem contactGap_uniform_pos_away {d : VariationData X q} (hd : VariationSetup d)
    {η : ℝ} (hη : 0 < η) : ∃ γ : ℝ, 0 < γ ∧
      ∀ p ∈ centerCylinder d, η ≤ ‖p - d.contact‖ → (γ : EReal) ≤ contactGap d p := by
  let K := centerCylinder d ∩ {p | η ≤ ‖p - d.contact‖}
  have hK : IsCompact K := hd.2.2.2.2.2.2.2.1.1.inter_right
    (isClosed_le continuous_const (continuous_id.sub continuous_const).norm)
  by_cases hne : K.Nonempty
  · obtain ⟨p, hp, hmin⟩ := (contactGap_lowerSemicontinuousOn hd).mono Set.inter_subset_left
      |>.exists_isMinOn hne hK
    have hpc : p ≠ d.contact := by
      intro heq
      have : η ≤ ‖p - d.contact‖ := hp.2
      simp only [heq, sub_self, norm_zero] at this
      linarith
    obtain ⟨γ, hγ0, hγgap⟩ := EReal.exists_between_coe_real (contactGap_pos hd hp.1 hpc)
    refine ⟨γ, ?_, fun x hx hxη => hγgap.le.trans (hmin ⟨hx, hxη⟩)⟩
    exact EReal.coe_lt_coe_iff.mp (by simpa only [EReal.coe_zero] using hγ0)
  · refine ⟨1, zero_lt_one, ?_⟩
    intro p hp hpη
    exact False.elim (hne ⟨p, hp, hpη⟩)

theorem contactGap_le_penalizedFunctional {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F)
    {ε : ℝ} (hε : 0 ≤ ε) :
    contactGap d (cotangentChart d.chart (F.f 0), F.s) ≤
      (penalizedFunctional d j ε F : EReal) := by
  have hc := hF.2.2.2.2.2.1
  have hvalid := hd.2.2.2.2.2.2.2.1.2.2.1 hc.2
  have hraw := envelopeChart_le_raw d.h d.T d.chart
    ((cotangentChart d.chart (F.f 0)).1, (cotangentChart d.chart (F.f 0)).2, F.s)
    ⟨hvalid.1.1, hvalid.2⟩
  have hround := cotangentChart_left_inv d.chart hc.1
  have heq : envelopeRawChart d.h d.T d.chart
      ((cotangentChart d.chart (F.f 0)).1, (cotangentChart d.chart (F.f 0)).2, F.s) =
      envelopeRaw d.h d.T (F.f 0).1 (F.f 0).2 F.s := by
    change envelopeRaw d.h d.T
      (cotangentChartInv d.chart (cotangentChart d.chart (F.f 0))).1
      (cotangentChartInv d.chart (cotangentChart d.chart (F.f 0))).2 F.s = _
    rw [hround]
  have henv := hraw.trans (heq.le.trans (envelopeRaw_le_disc_average hF))
  have hgap := EReal.sub_le_sub henv (le_refl (d.test (F.f 0) F.s : EReal))
  have hlo := penalizedFunctional_lower_wall_energy hd hF ε
  have hw := admissible_wallAverage_nonneg hd hF
  have he : 0 ≤ ε * (variationEnergy d j F).toReal := mul_nonneg hε ENNReal.toReal_nonneg
  have hreal : circleAverage (fun θ => let y := F.f (circlePoint θ)
      dualNorm (d.h (discTime F (circlePoint θ))) y.1 y.2) - d.test (F.f 0) F.s ≤
      penalizedFunctional d j ε F := by
    unfold penalizedFunctional
    rw [admissible_boundaryCost_split hd hF]
    linarith
  change _ - (d.test (cotangentChartInv d.chart (cotangentChart d.chart (F.f 0))) F.s : EReal) ≤ _
  rw [hround]
  exact hgap.trans (EReal.coe_le_coe_iff.mpr hreal)

end Yau.Blueprint.V03Proof
