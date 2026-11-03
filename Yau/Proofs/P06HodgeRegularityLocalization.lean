import Yau.Proofs.P06HodgeRegularityWeakProducts

/-! Compact localization of actual L² weak derivatives, including the
conversion from restricted measures to the whole coordinate space. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [IsLocallyFiniteMeasure ν]

theorem regularityMemLp_zero_off {O : Set E} (hO : MeasurableSet O) {f : E → ℝ}
    (hf : MemLp f 2 (ν.restrict O)) (hz : ∀ z, z ∉ O → f z = 0) : MemLp f 2 ν := by
  have h := (memLp_indicator_iff_restrict hO.nullMeasurableSet).mpr hf
  apply (memLp_congr_ae (μ := ν) ?_).mp h
  apply Eventually.of_forall
  intro z
  by_cases hzo : z ∈ O
  · exact Set.indicator_of_mem hzo f
  · rw [Set.indicator_of_notMem hzo, hz z hzo]

/-- A compact coefficient supported in the region turns a local weak
identity into an actual whole-space weak derivative, with full L² membership. -/
theorem regularityWeakDeriv_localize {O : Set E} (hO : IsOpen O) {e : E} {u v a : E → ℝ}
    (hu : MemLp u 2 (ν.restrict O)) (hv : MemLp v 2 (ν.restrict O))
    (hweak : regularityWeakDeriv ν O e u v)
    (ha : ContDiff ℝ ∞ a) (hca : HasCompactSupport a) (haO : tsupport a ⊆ O) :
    MemLp (fun z => a z * u z) 2 ν ∧
      MemLp (fun z => a z * v z + fderiv ℝ a z e * u z) 2 ν ∧
      regularityWeakDeriv ν Set.univ e (fun z => a z * u z)
        (fun z => a z * v z + fderiv ℝ a z e * u z) := by
  have htop : MemLp a (⊤ : ENNReal) (ν.restrict O) :=
    (ha.continuous.memLp_top_of_hasCompactSupport hca _).restrict O
  have hdtop : MemLp (fun z => fderiv ℝ a z e) (⊤ : ENNReal) (ν.restrict O) :=
    ((((ha.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous).memLp_top_of_hasCompactSupport (hca.fderiv_apply ℝ e) _).restrict O
  have ha0 (z : E) (hz : z ∉ O) : a z = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hz (haO h))
  have hda0 (z : E) (hz : z ∉ O) : fderiv ℝ a z e = 0 := by
    rw [fderiv_of_notMem_tsupport ℝ (fun h => hz (haO h))]
    rfl
  have hau : MemLp (fun z => a z * u z) 2 ν :=
    regularityMemLp_zero_off ν hO.measurableSet (htop.mul hu) (fun z hz => by rw [ha0 z hz, zero_mul])
  have hav : MemLp (fun z => a z * v z) 2 ν :=
    regularityMemLp_zero_off ν hO.measurableSet (htop.mul hv) (fun z hz => by rw [ha0 z hz, zero_mul])
  have hdau : MemLp (fun z => fderiv ℝ a z e * u z) 2 ν :=
    regularityMemLp_zero_off ν hO.measurableSet (hdtop.mul hu) (fun z hz => by rw [hda0 z hz, zero_mul])
  refine ⟨hau, hav.add hdau, ?_⟩
  intro φ hφ
  have hφL : MemLp φ 2 ν := hφ.1.continuous.memLp_of_hasCompactSupport hφ.2.1
  have hDφL : MemLp (fun z => fderiv ℝ φ z e) 2 ν :=
    ((regularityTest_direction hφ e).1.continuous.memLp_of_hasCompactSupport
      (regularityTest_direction hφ e).2.1)
  have htest : regularityTest O (fun z => φ z * a z) :=
    ⟨hφ.1.mul ha, hca.mul_left, tsupport_mul_subset_right.trans haO⟩
  have h := hweak (fun z => φ z * a z) htest
  rw [regularityTest_integral_restrict ν (regularityTest_direction htest e),
    regularityTest_integral_restrict ν htest] at h
  have hprod (z : E) : fderiv ℝ (fun y => φ y * a y) z e =
      φ z * fderiv ℝ a z e + a z * fderiv ℝ φ z e := by
    rw [fderiv_fun_mul (hφ.1.differentiable (by simp) z) (ha.differentiable (by simp) z)]
    rfl
  have hleft : (fun z => u z * fderiv ℝ (fun y => φ y * a y) z e) =
      fun z => (a z * u z) * fderiv ℝ φ z e + (fderiv ℝ a z e * u z) * φ z := by
    funext z
    rw [hprod]
    ring
  have hright : (fun z => v z * (φ z * a z)) = fun z => (a z * v z) * φ z := by
    funext z
    ring
  have hX : Integrable (fun z => (a z * u z) * fderiv ℝ φ z e) ν := hau.integrable_mul hDφL
  have hY : Integrable (fun z => (fderiv ℝ a z e * u z) * φ z) ν := hdau.integrable_mul hφL
  have hZ : Integrable (fun z => (a z * v z) * φ z) ν := hav.integrable_mul hφL
  rw [hleft, hright, integral_add hX hY] at h
  have hgoal : (fun z => (a z * v z + fderiv ℝ a z e * u z) * φ z) =
      fun z => (a z * v z) * φ z + (fderiv ℝ a z e * u z) * φ z := by
    funext z
    ring
  simp only [Measure.restrict_univ]
  rw [hgoal, integral_add hZ hY]
  linarith

end Yau.NodeProofs.P06Aux
