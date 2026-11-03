import Yau.Proofs.V03DiscScalars
import Yau.Proofs.V03ConstantDisc
import Yau.Proofs.V03BaseDensity
import Yau.Proofs.V03EuclideanRadial
import Yau.Proofs.V03ClockRadial
import Yau.Proofs.V03AmbientSmooth

/-! Every fixed original smooth closed disc eventually lies on both actual
cutoff plateaus. Its full computed energy is then finite. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem fixedDisc_cutoff_plateaus {d : VariationData X q} (hd : VariationSetup d)
    {f : ℂ → CotangentPoint X.manifold} (hf : CotangentDisc f) :
    ∀ᶠ j in atTop, ∀ ζ ∈ Metric.closedBall (0 : ℂ) 1,
      deltaBase d j (f ζ).1 = 1 ∧ deltaFiber d j (f ζ) = 1 := by
  have hu := (cotangentDisc_smoothFn_contDiffOn hd.2.2.2.1.1 hf).continuousOn
  have hN := (cotangentDisc_dualNorm_contDiffOn X.metric hf).continuousOn
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1).bddAbove_image hu
  obtain ⟨N, hNbd⟩ := (isCompact_closedBall (0 : ℂ) 1).bddAbove_image hN
  have hA : Tendsto d.A atTop atTop := hd.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAev := hA.eventually (eventually_gt_atTop (3 * |M| + 1))
  have hnat : ∀ᶠ j : ℕ in atTop, 2 * |N| + 1 ≤ (j : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun j : ℕ => (j : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop _)
  filter_upwards [hAev, hnat] with j hjA hjN ζ hζ
  have hj := hd.2.2.2.2.2.2.2.2.2.2.2.2.2 j
  have hBj := hj.2.1
  have hpos := setup_index_bounds hd j
  have huM : d.u (f ζ).1 ≤ M := hM ⟨ζ, hζ, rfl⟩
  have hNN : dualNorm (d.h 0) (f ζ).1 (f ζ).2 ≤ N := by
    rw [hd.2.2.1.1.1.1]
    exact hNbd ⟨ζ, hζ, rfl⟩
  constructor
  · apply (setup_wallProfiles hd).2.2.1 (d.u (f ζ).1 / d.A j) |>.2.2.2
    apply (div_le_iff₀ hpos.1).mpr
    nlinarith [le_abs_self M]
  · apply (setup_wallProfiles hd).2.2.2 (dualNorm (d.h 0) (f ζ).1 (f ζ).2 / d.B j ^ 2) |>.2.2.2
    apply (div_le_iff₀ (sq_pos_of_pos hpos.2)).mpr
    nlinarith [le_abs_self N, sq_nonneg (d.B j - 1)]

theorem cutoff_plateaus_mem_boundaryRegion {d : VariationData X q}
    (hd : VariationSetup d) {j : ℕ} {y : CotangentPoint X.manifold}
    (hy : deltaBase d j y.1 = 1 ∧ deltaFiber d j y = 1) : y ∈ boundaryRegion d j := by
  have hp := setup_wallProfiles hd
  have hpos := setup_index_bounds hd j
  have hbase : 0 < d.profileBase (d.u y.1 / d.A j) := by
    change 0 < deltaBase d j y.1
    rw [hy.1]; norm_num
  have hfiber : 0 < d.profileFiber (dualNorm (d.h 0) y.1 y.2 / d.B j ^ 2) := by
    change 0 < deltaFiber d j y
    rw [hy.2]; norm_num
  exact ⟨(div_lt_one hpos.1).mp ((hp.2.2.1 _).2.2.1.mp hbase),
    (div_lt_one (sq_pos_of_pos hpos.2)).mp ((hp.2.2.2 _).2.2.1.mp hfiber)⟩

theorem fixedDisc_energy_finite_eventually {d : VariationData X q} (hd : VariationSetup d)
    (F : VariationDisc X) (hf : CotangentDisc F.f)
    (hw : ContDiffOn ℂ ∞ F.w (Metric.closedBall 0 1)) :
    ∀ᶠ j in atTop, variationEnergy d j F ≠ ⊤ := by
  filter_upwards [fixedDisc_cutoff_plateaus hd hf] with j hj
  have hlog : (fun θ => Real.log (wallProduct d j (F.f (circlePoint θ)))) = fun _ => 0 := by
    funext θ
    obtain ⟨hb, hfi⟩ := hj _ (circlePoint_mem_closedBall θ)
    simp only [wallProduct, hb, hfi, one_mul, Real.log_one]
  have hbase := discArea_ne_top_of_cotangentDisc X.metric hf
  have hamb := euclideanArea_ne_top_of_closedDisc
    (cotangentDisc_ambient_contDiffOn hf hd.2.2.2.2.1.1)
  have hclock := clockArea_ne_top_of_closedDisc (F := F) hw
  simp only [variationEnergy, hlog, scalarDSq_const, ENNReal.add_ne_top]
  exact ⟨⟨⟨⟨hbase, hamb⟩, ENNReal.ofReal_ne_top⟩, hclock⟩, ENNReal.zero_ne_top⟩

end Yau.Blueprint.V03Proof
