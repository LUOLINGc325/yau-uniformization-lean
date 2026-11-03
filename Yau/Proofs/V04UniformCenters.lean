import Yau.Proofs.V03ContactGap

/-! A common compact set of centers is chosen before every minimizing
sequence. The outer index threshold comes from the infimum itself. -/

open Filter Set
open scoped Manifold Topology ContDiff Matrix ComplexOrder
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

theorem uniform_minimizing_centers {d : VariationData X q} (hd : VariationSetup d)
    (hloc : LocalizationEstimates d) :
    ∃ Kc : Set (CotangentCoord n × ℝ), IsCompact Kc ∧
      Kc ⊆ interior (centerCylinder d) ∧
      ∀ᶠ j in atTop, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        ∀ F : ℕ → VariationDisc X, MinimizingSequence d j ε F →
          ∀ᶠ ν in atTop, InCotangentTimeChart d.chart ((F ν).f 0) (F ν).s Kc := by
  have hc := hd.2.2.2.2.2.2.2.1
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp
    (isOpen_interior.mem_nhds hc.2.1)
  let Kc : Set (CotangentCoord n × ℝ) := Metric.closedBall d.contact (R / 2)
  have hK : Kc ⊆ interior (centerCylinder d) := by
    intro p hp
    apply hball
    have hp' : dist p d.contact ≤ R / 2 := hp
    exact lt_of_le_of_lt hp' (by linarith)
  obtain ⟨γ, hγ, hgap⟩ := contactGap_uniform_pos_away hd (half_pos hR)
  refine ⟨Kc, isCompact_closedBall _ _, hK, ?_⟩
  have hsmall := hloc.1.eventually
    (Iio_mem_nhds (show (0 : EReal) < ((γ / 4 : ℝ) : EReal) by
      exact_mod_cast (by positivity : (0 : ℝ) < γ / 4)))
  filter_upwards [hsmall, hloc.2.1] with j hj hcore
  have hright := hcore.2.2.2.2.1
  have hhalf : localizedInfimum d j 0 < ((γ / 2 : ℝ) : EReal) :=
    hj.trans (EReal.coe_lt_coe_iff.mpr (by linarith))
  filter_upwards [hright.eventually (Iio_mem_nhds hhalf), self_mem_nhdsWithin]
    with ε hεμ hε
  intro F hF
  have hcost : localizedInfimum d j ε < ((3 * γ / 4 : ℝ) : EReal) :=
    hεμ.trans (EReal.coe_lt_coe_iff.mpr (by linarith))
  filter_upwards [hF.2.eventually (Iio_mem_nhds hcost)] with ν hν
  have hcenter := (hF.1 ν).2.2.2.2.2.1
  refine ⟨hcenter.1, ?_⟩
  change dist (cotangentChart d.chart ((F ν).f 0), (F ν).s) d.contact ≤ R / 2
  by_contra hout
  have hnorm : R / 2 ≤
      ‖(cotangentChart d.chart ((F ν).f 0), (F ν).s) - d.contact‖ := by
    simpa only [dist_eq_norm] using (lt_of_not_ge hout).le
  have hγcost := (hgap _ hcenter.2 hnorm).trans
    (contactGap_le_penalizedFunctional hd (hF.1 ν) hε.le)
  exact (not_lt_of_ge hγcost) (hν.trans (EReal.coe_lt_coe_iff.mpr (by linarith)))

end Yau.Blueprint.V04Proof
