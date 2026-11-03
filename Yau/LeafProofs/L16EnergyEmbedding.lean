import Yau.LeafProofs.L16EnergyGraph
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! The spatial weak derivative and dense, injective value embedding of the actual
closed smooth `L²` graph. Only openness of the spatial set is needed. -/
open MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic
variable {n : ℕ}

/-- The real `L²` pairing with a specified representative. -/
theorem energy_inner_toLp {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (u : Lp ℝ 2 μ) {g : α → ℝ} (hg : MemLp g 2 μ) :
    inner ℝ u (hg.toLp g) = ∫ x, u x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hg.coeFn_toLp] with x hx
  simp only [hx, Real.inner_apply, mul_comm]

/-- The genuine compact-support integration-by-parts identity in the spatial tests. -/
theorem energySpatialTests_integration_by_parts {O : Set (Space n)}
    (u ψ : energySpatialTests O) (i : Yau.RIdx n) :
    (∫ x in O, u.1 x * d ψ.1 x i) = -(∫ x in O, d u.1 x i * ψ.1 x) := by
  have hdu : Continuous (fun x => d u.1 x i) :=
    (u.2.1.contDiff_fderiv_apply (m := 0) (by simp)).continuous.comp
      (continuous_id.prodMk continuous_const)
  have hdψ : Continuous (fun x => d ψ.1 x i) :=
    (ψ.2.1.contDiff_fderiv_apply (m := 0) (by simp)).continuous.comp
      (continuous_id.prodMk continuous_const)
  have hglobal : (∫ x, u.1 x * d ψ.1 x i) = -(∫ x, d u.1 x i * ψ.1 x) :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      ((hdu.mul ψ.2.1.continuous).integrable_of_hasCompactSupport ψ.2.2.1.mul_left)
      ((u.2.1.continuous.mul hdψ).integrable_of_hasCompactSupport u.2.2.1.mul_right)
      ((u.2.1.continuous.mul ψ.2.1.continuous).integrable_of_hasCompactSupport u.2.2.1.mul_right)
      (fun x _ => u.2.1.differentiable (by simp) x)
      (fun x _ => ψ.2.1.differentiable (by simp) x)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)]
  · exact hglobal
  · have hz : ψ.1 x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hx (ψ.2.2.2 h))
    simp only [hz, mul_zero]
  · have hz : u.1 x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hx (u.2.2.2 h))
    simp only [hz, zero_mul]

/-- The weak derivative identity extends from smooth graphs to their actual closure. -/
theorem energyGraph_spatial_integration_by_parts {O : Set (Space n)}
    (v : EnergyGraphSpace O) (ψ : energySpatialTests O) (i : Yau.RIdx n) :
    (∫ x in O, energyValueProjection O v x * d ψ.1 x i) =
      -(∫ x in O, energyGradientProjection O i v x * ψ.1 x) := by
  rw [← energy_inner_toLp _ (energySpatialTest_d_memLp ψ i),
    ← energy_inner_toLp _ (energySpatialTest_memLp ψ)]
  let C : Set (EnergyGraphSpace O) := {w |
    inner ℝ (energyValueProjection O w) ((energySpatialTest_d_memLp ψ i).toLp _) =
      -inner ℝ (energyGradientProjection O i w) ((energySpatialTest_memLp ψ).toLp _)}
  have hc : IsClosed C := isClosed_eq
    ((energyValueProjection O).continuous.inner continuous_const)
    (((energyGradientProjection O i).continuous.inner continuous_const).neg)
  apply closure_minimal (t := C) ?_ hc (energySpatialGraphInSpace_denseRange O v)
  rintro _ ⟨u, rfl⟩
  change inner ℝ ((energySpatialTest_memLp u).toLp _) _ =
    -inner ℝ ((energySpatialTest_d_memLp u i).toLp _) _
  rw [energy_inner_toLp, energy_inner_toLp]
  have hleft : (∫ x in O, ((energySpatialTest_memLp u).toLp u.1) x * d ψ.1 x i) =
      ∫ x in O, u.1 x * d ψ.1 x i := by
    apply integral_congr_ae
    filter_upwards [(energySpatialTest_memLp u).coeFn_toLp] with x hx
    rw [hx]
  have hright : (∫ x in O, ((energySpatialTest_d_memLp u i).toLp _) x * ψ.1 x) =
      ∫ x in O, d u.1 x i * ψ.1 x := by
    apply integral_congr_ae
    filter_upwards [(energySpatialTest_d_memLp u i).coeFn_toLp] with x hx
    rw [hx]
  rw [hleft, hright]
  exact energySpatialTests_integration_by_parts u ψ i

/-- The products in the spatial weak identity are genuine integrable functions. -/
theorem energy_L2_test_product_integrable {O : Set (Space n)}
    (u : Lp ℝ 2 (volume.restrict O)) {g : Space n → ℝ}
    (hg : MemLp g 2 (volume.restrict O)) :
    Integrable (fun x => u x * g x) (volume.restrict O) := by
  have h := L2.integrable_inner (𝕜 := ℝ) u (hg.toLp g)
  apply h.congr
  filter_upwards [hg.coeFn_toLp] with x hx
  simp only [hx, Real.inner_apply]

/-- An actual spatial `L²` class annihilating all spatial tests is zero. -/
theorem energy_test_annihilation_eq_zero {O : Set (Space n)} (hO : IsOpen O)
    (u : Lp ℝ 2 (volume.restrict O))
    (h : ∀ ψ : energySpatialTests O, (∫ x in O, u x * ψ.1 x) = 0) : u = 0 := by
  have hloc : LocallyIntegrableOn (fun x => u x) O (volume.restrict O) :=
    ((Lp.memLp u).locallyIntegrable (by norm_num)).locallyIntegrableOn O
  have hz := hO.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
    (fun g hg hgc hgs => by
      simpa only [smul_eq_mul, mul_comm] using h ⟨g, hg, hgc, hgs⟩)
  apply Lp.ext
  filter_upwards [hz, ae_restrict_mem hO.measurableSet,
    Lp.coeFn_zero ℝ 2 (volume.restrict O)] with x hx hmem hzero
  exact (hx hmem).trans hzero.symm

/-- Uniqueness of the spatial weak gradient makes the value projection injective. -/
theorem energyValueProjection_injective {O : Set (Space n)} (hO : IsOpen O) :
    Function.Injective (energyValueProjection O) := by
  apply (energyValueProjection O).toLinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro v hv
  have hval : energyValueProjection O v = 0 := hv
  apply Subtype.ext
  apply PiLp.ext
  intro k
  cases k with
  | none => exact hval
  | some i =>
    change energyGradientProjection O i v = 0
    apply energy_test_annihilation_eq_zero hO
    intro ψ
    have hleft : (∫ x in O, energyValueProjection O v x * d ψ.1 x i) = 0 := by
      rw [hval]
      apply integral_eq_zero_of_ae
      filter_upwards [Lp.coeFn_zero ℝ 2 (volume.restrict O)] with x hx
      simp only [hx, Pi.zero_apply, zero_mul]
    have hibp := energyGraph_spatial_integration_by_parts v ψ i
    rw [hleft] at hibp
    exact neg_eq_zero.mp hibp.symm

/-- The actual closed graph has dense value range in the spatial `L²` space. -/
theorem energyValueProjection_denseRange {O : Set (Space n)} (hO : IsOpen O) :
    DenseRange (energyValueProjection O) := by
  change Dense (↑((energyValueProjection O).toLinearMap.range) :
    Set (Lp ℝ 2 (volume.restrict O)))
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff]
  apply (Submodule.eq_bot_iff _).mpr
  intro u hu
  apply energy_test_annihilation_eq_zero hO
  intro ψ
  have hinner : inner ℝ u
      (energyValueProjection O (energySpatialGraphInSpace O ψ)) = 0 :=
    ((energyValueProjection O).toLinearMap.range.mem_orthogonal' u).mp hu _
      ⟨energySpatialGraphInSpace O ψ, rfl⟩
  change inner ℝ u ((energySpatialTest_memLp ψ).toLp ψ.1) = 0 at hinner
  rwa [energy_inner_toLp] at hinner

end Yau.LeafProofs.L16Aux
