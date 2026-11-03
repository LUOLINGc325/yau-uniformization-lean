import Yau.Proofs.V03ConstantDisc
import Yau.Proofs.V03FunctionalLower

/-! Actual constant competitors at the contact point give eventual
nonemptiness and finite localized infima for all nonnegative penalties. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem boundaryRegion_at_point_eventually {d : VariationData X q} (hd : VariationSetup d)
    (y : CotangentPoint X.manifold) : ∀ᶠ j in atTop, y ∈ boundaryRegion d j := by
  have hA : Tendsto d.A atTop atTop := by
    rcases hd with ⟨_, _, _, _, _, _, _, _, _, _, _, _, h, _⟩
    exact h
  have hIndex : ∀ j : ℕ, (j : ℝ) + 1 ≤ d.B j := by
    intro j
    exact (hd.2.2.2.2.2.2.2.2.2.2.2.2.2 j).2.1
  have hbase := hA.eventually (eventually_gt_atTop (d.u y.1))
  have hnat : ∀ᶠ j : ℕ in atTop, dualNorm (d.h 0) y.1 y.2 + 1 ≤ (j : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun j : ℕ => (j : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop _)
  filter_upwards [hbase, hnat] with j hjA hjN
  refine ⟨hjA, ?_⟩
  have hB := hIndex j
  have hN := dualNorm_nonneg (d.h 0) y.1 y.2
  nlinarith [sq_nonneg (d.B j - 1)]

theorem admissible_nonempty_eventually {d : VariationData X q} (hd : VariationSetup d) :
    ∀ᶠ j in atTop, ∃ F : VariationDisc X, AdmissibleVariationDisc d j F := by
  have hcontact := hd.2.2.2.2.2.2.2.1
  have hc : d.contact ∈ centerCylinder d := interior_subset hcontact.2.1
  have hv := hcontact.2.2.1 hc
  let y := cotangentChartInv d.chart d.contact.1
  have hcenter : InCotangentTimeChart d.chart y d.contact.2 (centerCylinder d) := by
    refine ⟨cotangentChartInv_mapsTo d.chart hv.1, ?_⟩
    change (cotangentChart d.chart (cotangentChartInv d.chart d.contact.1), d.contact.2) ∈ centerCylinder d
    rw [cotangentChart_right_inv d.chart hv.1]
    exact hc
  filter_upwards [boundaryRegion_at_point_eventually hd y] with j hj
  exact ⟨constantVariationDisc y d.contact.2,
    constantVariation_admissible d j y d.contact.2 hv.2.1 hv.2.2 hcenter hj⟩

theorem localizedInfimum_finite_of_nonempty {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} (hF : ∃ F : VariationDisc X, AdmissibleVariationDisc d j F)
    {ε : ℝ} (hε : 0 ≤ ε) : localizedInfimum d j ε ≠ ⊥ ∧ localizedInfimum d j ε ≠ ⊤ := by
  obtain ⟨F, hF⟩ := hF
  refine ⟨ne_of_gt ((EReal.bot_lt_coe (0 : ℝ)).trans_le (localizedInfimum_nonneg hd j hε)), ?_⟩
  exact ne_of_lt ((localizedInfimum_le ε hF).trans_lt (EReal.coe_lt_top _))

theorem localizedInfimum_finite_eventually {d : VariationData X q} (hd : VariationSetup d) :
    ∀ᶠ j in atTop, (∃ F, AdmissibleVariationDisc d j F) ∧
      ∀ ε : ℝ, 0 ≤ ε → localizedInfimum d j ε ≠ ⊥ ∧ localizedInfimum d j ε ≠ ⊤ :=
  (admissible_nonempty_eventually hd).mono fun j hj =>
    ⟨hj, fun ε hε => localizedInfimum_finite_of_nonempty hd hj hε⟩

end Yau.Blueprint.V03Proof
