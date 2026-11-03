import Yau.LeafProofs.L16EnergyUncurrying
import Yau.LeafProofs.L16EnergyForm
import Yau.LeafProofs.L16EnergyGalerkinSpaces

/-! Scalar time measurability and actual time-test functionals for the energy form.
The coefficient hypotheses are intermediate joint measurability and slice bounds. -/
open MeasureTheory Filter
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic

variable {n : ℕ}

/-- Reverse Fubini is applied to the finitely many actual graph coordinates.
No joint measurability of variable `Lp` representative evaluation is asserted. -/
theorem energyFormValue_time_aestronglyMeasurable
    {O : Set (Space n)} {T : ℝ} {a : Point n → Mat n}
    {b : Point n → Yau.RIdx n → ℝ}
    (ha : ∀ i j, AEStronglyMeasurable (fun p => a p i j)
      (productVolume O (Set.Ioo 0 T)))
    (hb : ∀ j, AEStronglyMeasurable (fun p => energyDrift a b p j)
      (productVolume O (Set.Ioo 0 T)))
    {U W : ℝ → EnergyGraphSpace O}
    (hU : MemLp U 2 (volume.restrict (Set.Ioo 0 T)))
    (hW : MemLp W 2 (volume.restrict (Set.Ioo 0 T))) :
    AEStronglyMeasurable (fun t => energyFormValue O a b t (U t) (W t))
      (volume.restrict (Set.Ioo 0 T)) := by
  classical
  have hUp (k : Option (Yau.RIdx n)) :=
    (energyCoordinateProjection O k).comp_memLp' hU
  have hWp (k : Option (Yau.RIdx n)) :=
    (energyCoordinateProjection O k).comp_memLp' hW
  choose G hG hGs hGn using fun k => energy_productVolume_uncurry O T (hUp k)
  choose H hH hHs hHn using fun k => energy_productVolume_uncurry O T (hWp k)
  let J : Point n → ℝ := fun p =>
    (∑ i, ∑ j, a p i j * G (some j) p * H (some i) p) -
      ∑ j, energyDrift a b p j * G (some j) p * H none p
  have hJ : AEStronglyMeasurable J (productVolume O (Set.Ioo 0 T)) := by
    exact (Finset.aestronglyMeasurable_fun_sum Finset.univ fun i _ =>
      Finset.aestronglyMeasurable_fun_sum Finset.univ fun j _ =>
        ((ha i j).mul (hG (some j)).aestronglyMeasurable).mul
          (hH (some i)).aestronglyMeasurable).sub
      (Finset.aestronglyMeasurable_fun_sum Finset.univ fun j _ =>
        ((hb j).mul (hG (some j)).aestronglyMeasurable).mul
          (hH none).aestronglyMeasurable)
  apply hJ.prod_swap.integral_prod_right' |>.congr
  filter_upwards [eventually_all.mpr hGs, eventually_all.mpr hHs] with t htG htH
  have hGe (k : Option (Yau.RIdx n)) :
      (fun x => G k (x,t)) =ᵐ[volume.restrict O]
        (energyCoordinateProjection O k (U t)) := by
    obtain ⟨hk, he⟩ := htG k
    simpa only [he, Function.comp_apply] using hk.coeFn_toLp.symm
  have hHe (k : Option (Yau.RIdx n)) :
      (fun x => H k (x,t)) =ᵐ[volume.restrict O]
        (energyCoordinateProjection O k (W t)) := by
    obtain ⟨hk, he⟩ := htH k
    simpa only [he, Function.comp_apply] using hk.coeFn_toLp.symm
  apply integral_congr_ae
  filter_upwards [eventually_all.mpr hGe, eventually_all.mpr hHe] with x hxG hxH
  simp only [J, Prod.swap_prod_mk, energyGradientProjection, energyValueProjection,
    hxG, hxH]

/-- Uniform actual slice bounds give time integrability by the `L²` product bound. -/
theorem energyFormValue_integrable
    {O : Set (Space n)} {T : ℝ} {a : Point n → Mat n}
    {b : Point n → Yau.RIdx n → ℝ} {A D : ℝ}
    (ha : ∀ i j, AEStronglyMeasurable (fun p => a p i j)
      (productVolume O (Set.Ioo 0 T)))
    (hb : ∀ j, AEStronglyMeasurable (fun p => energyDrift a b p j)
      (productVolume O (Set.Ioo 0 T)))
    (hSlice : ∀ t ∈ Set.Ioo 0 T, EnergySliceBounds O a b t A D)
    {U W : ℝ → EnergyGraphSpace O}
    (hU : MemLp U 2 (volume.restrict (Set.Ioo 0 T)))
    (hW : MemLp W 2 (volume.restrict (Set.Ioo 0 T))) :
    Integrable (fun t => energyFormValue O a b t (U t) (W t))
      (volume.restrict (Set.Ioo 0 T)) := by
  apply ((hU.norm.integrable_mul hW.norm).const_mul (energyFormBound n A D)).mono'
    (energyFormValue_time_aestronglyMeasurable ha hb hU hW)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  simpa only [← energyForm_apply (hSlice t ht), mul_assoc, Pi.mul_apply] using
    energyForm_apply_bound (hSlice t ht) (U t) (W t)


/-- The canonical operator norm with the time and scalar spaces specified explicitly. -/
instance energyTimeScalarMap_norm (O : Set (Space n)) (T : ℝ) :
    Norm (Lp (EnergyGraphSpace O) 2 (volume.restrict (Set.Ioo 0 T)) →L[ℝ]
      Lp ℝ 2 (volume.restrict (Set.Ioo 0 T))) :=
  @ContinuousLinearMap.hasOpNorm ℝ ℝ
    (Lp (EnergyGraphSpace O) 2 (volume.restrict (Set.Ioo 0 T)))
    (Lp ℝ 2 (volume.restrict (Set.Ioo 0 T)))
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance (RingHom.id ℝ)

/-- The canonical norm on actual energy-time scalar functionals. -/
instance energyTimeFunctional_norm (O : Set (Space n)) (T : ℝ) :
    Norm (Lp (EnergyGraphSpace O) 2 (volume.restrict (Set.Ioo 0 T)) →L[ℝ] ℝ) :=
  @ContinuousLinearMap.hasOpNorm ℝ ℝ
    (Lp (EnergyGraphSpace O) 2 (volume.restrict (Set.Ioo 0 T))) ℝ
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance (RingHom.id ℝ)

section FixedTest

variable {O : Set (Space n)} {T : ℝ} {a : Point n → Mat n}
    {b : Point n → Yau.RIdx n → ℝ} {A D : ℝ}
    (ha : ∀ i j, AEStronglyMeasurable (fun p => a p i j)
      (productVolume O (Set.Ioo 0 T)))
    (hb : ∀ j, AEStronglyMeasurable (fun p => energyDrift a b p j)
      (productVolume O (Set.Ioo 0 T)))
    (hSlice : ∀ t ∈ Set.Ioo 0 T, EnergySliceBounds O a b t A D)

include ha hb hSlice in
/-- Against a fixed spatial test, the actual scalar form is an `L²` time curve. -/
theorem energyFormValue_fixed_memLp (w : EnergyGraphSpace O)
    {U : ℝ → EnergyGraphSpace O}
    (hU : MemLp U 2 (volume.restrict (Set.Ioo 0 T))) :
    MemLp (fun t => energyFormValue O a b t (U t) w) 2
      (volume.restrict (Set.Ioo 0 T)) := by
  have hw : MemLp (fun _ : ℝ => w) 2 (volume.restrict (Set.Ioo 0 T)) := memLp_const w
  apply (hU.norm.const_mul (max 0 (energyFormBound n A D) * ‖w‖)).mono'
    (energyFormValue_time_aestronglyMeasurable ha hb hU hw)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  calc
    ‖energyFormValue O a b t (U t) w‖ ≤ energyFormBound n A D * ‖U t‖ * ‖w‖ := by
      simpa only [energyForm_apply] using energyForm_apply_bound (hSlice t ht) (U t) w
    _ ≤ (max 0 (energyFormBound n A D) * ‖w‖) * ‖U t‖ := by
      calc
        _ ≤ max 0 (energyFormBound n A D) * ‖U t‖ * ‖w‖ := by
          gcongr
          exact le_max_right _ _
        _ = _ := by ring

/-- The actual fixed-test scalar class in time `L²`. -/
def energyTimeFormCurve (w : EnergyGraphSpace O)
    (U : Lp (EnergyGraphSpace O) 2 (volume.restrict (Set.Ioo 0 T))) :
    Lp ℝ 2 (volume.restrict (Set.Ioo 0 T)) :=
  (energyFormValue_fixed_memLp ha hb hSlice w (Lp.memLp U)).toLp
    (fun t => energyFormValue O a b t (U t) w)

include ha hb hSlice in
theorem energyTimeFormCurve_coeFn (w : EnergyGraphSpace O)
    (U : Lp (EnergyGraphSpace O) 2 (volume.restrict (Set.Ioo 0 T))) :
    energyTimeFormCurve ha hb hSlice w U =ᵐ[volume.restrict (Set.Ioo 0 T)]
      fun t => energyFormValue O a b t (U t) w :=
  (energyFormValue_fixed_memLp ha hb hSlice w (Lp.memLp U)).coeFn_toLp

/-- Linearity of the actual scalar output class, using the genuine quotient operations. -/
def energyTimeFormLinearMap (w : EnergyGraphSpace O) :
    Lp (EnergyGraphSpace O) 2 (volume.restrict (Set.Ioo 0 T)) →ₗ[ℝ]
      Lp ℝ 2 (volume.restrict (Set.Ioo 0 T)) where
  toFun := energyTimeFormCurve ha hb hSlice w
  map_add' U V := by
    apply Lp.ext
    filter_upwards [energyTimeFormCurve_coeFn ha hb hSlice w (U+V),
      energyTimeFormCurve_coeFn ha hb hSlice w U,
      energyTimeFormCurve_coeFn ha hb hSlice w V, Lp.coeFn_add U V,
      Lp.coeFn_add (energyTimeFormCurve ha hb hSlice w U)
        (energyTimeFormCurve ha hb hSlice w V),
      ae_restrict_mem measurableSet_Ioo] with t hout hu hv hUV hsum htI
    simpa only [hout, hu, hv, hUV, hsum, Pi.add_apply] using
      energyFormValue_add_left (hSlice t htI) (U t) (V t) w
  map_smul' c U := by
    apply Lp.ext
    filter_upwards [energyTimeFormCurve_coeFn ha hb hSlice w (c • U),
      energyTimeFormCurve_coeFn ha hb hSlice w U, Lp.coeFn_smul c U,
      Lp.coeFn_smul c (energyTimeFormCurve ha hb hSlice w U),
      ae_restrict_mem measurableSet_Ioo] with t hcu hu hsm hsm' htI
    simpa only [hcu, hu, hsm, hsm', Pi.smul_apply, smul_eq_mul, RingHom.id_apply] using
      energyFormValue_smul_left (hSlice t htI) c (U t) w

include ha hb hSlice in
theorem energyTimeFormLinearMap_bound (w : EnergyGraphSpace O)
    (U : Lp (EnergyGraphSpace O) 2 (volume.restrict (Set.Ioo 0 T))) :
    ‖energyTimeFormLinearMap ha hb hSlice w U‖ ≤
      (max 0 (energyFormBound n A D) * ‖w‖) * ‖U‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [energyTimeFormCurve_coeFn ha hb hSlice w U,
    ae_restrict_mem measurableSet_Ioo] with t ht htI
  change ‖energyTimeFormCurve ha hb hSlice w U t‖ ≤ _
  rw [ht]
  calc
    _ ≤ energyFormBound n A D * ‖U t‖ * ‖w‖ := by
      simpa only [energyForm_apply] using energyForm_apply_bound (hSlice t htI) (U t) w
    _ ≤ (max 0 (energyFormBound n A D) * ‖w‖) * ‖U t‖ := by
      calc
        _ ≤ max 0 (energyFormBound n A D) * ‖U t‖ * ‖w‖ := by
          gcongr
          exact le_max_right _ _
        _ = _ := by ring

/-- The genuine scalar output curve as a bounded linear map of time `L²` spaces. -/
def energyTimeFormMap (w : EnergyGraphSpace O) :
    Lp (EnergyGraphSpace O) 2 (volume.restrict (Set.Ioo 0 T)) →L[ℝ]
      Lp ℝ 2 (volume.restrict (Set.Ioo 0 T)) :=
  @LinearMap.mkContinuous ℝ ℝ
    (Lp (EnergyGraphSpace O) 2 (volume.restrict (Set.Ioo 0 T)))
    (Lp ℝ 2 (volume.restrict (Set.Ioo 0 T)))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (RingHom.id ℝ) (energyTimeFormLinearMap ha hb hSlice w)
    (max 0 (energyFormBound n A D) * ‖w‖)
    (energyTimeFormLinearMap_bound ha hb hSlice w)

include ha hb hSlice in
theorem energyTimeFormMap_coeFn (w : EnergyGraphSpace O)
    (U : Lp (EnergyGraphSpace O) 2 (volume.restrict (Set.Ioo 0 T))) :
    energyTimeFormMap ha hb hSlice w U =ᵐ[volume.restrict (Set.Ioo 0 T)]
      fun t => energyFormValue O a b t (U t) w :=
  energyTimeFormCurve_coeFn ha hb hSlice w U

include ha hb hSlice in
theorem energyTimeFormMap_norm_le (w : EnergyGraphSpace O) :
    ‖energyTimeFormMap ha hb hSlice w‖ ≤ max 0 (energyFormBound n A D) * ‖w‖ :=
by
  apply @ContinuousLinearMap.opNorm_le_bound ℝ ℝ
    (Lp (EnergyGraphSpace O) 2 (volume.restrict (Set.Ioo 0 T)))
    (Lp ℝ 2 (volume.restrict (Set.Ioo 0 T)))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (RingHom.id ℝ) (energyTimeFormMap ha hb hSlice w)
    (max 0 (energyFormBound n A D) * ‖w‖) (by positivity)
  exact energyTimeFormLinearMap_bound ha hb hSlice w

include ha hb hSlice in
/-- The literal time-test integrand is integrable for every actual `L²(V)` curve. -/
theorem energyTimeFormFunctional_integrable {η : ℝ → ℝ}
    (hη : MemLp η 2 (volume.restrict (Set.Ioo 0 T))) (w : EnergyGraphSpace O)
    {U : ℝ → EnergyGraphSpace O}
    (hU : MemLp U 2 (volume.restrict (Set.Ioo 0 T))) :
    Integrable (fun t => η t * energyFormValue O a b t (U t) w)
      (volume.restrict (Set.Ioo 0 T)) :=
  hη.integrable_mul (energyFormValue_fixed_memLp ha hb hSlice w hU)

/-- The actual fixed-test energy integral is a continuous linear functional on time `L²(V)`. -/
def energyTimeFormFunctional {η : ℝ → ℝ}
    (hη : MemLp η 2 (volume.restrict (Set.Ioo 0 T))) (w : EnergyGraphSpace O) :
    Lp (EnergyGraphSpace O) 2 (volume.restrict (Set.Ioo 0 T)) →L[ℝ] ℝ :=
  (innerSL ℝ (hη.toLp η)).comp (energyTimeFormMap ha hb hSlice w)

include ha hb hSlice in
theorem energyTimeFormFunctional_apply {η : ℝ → ℝ}
    (hη : MemLp η 2 (volume.restrict (Set.Ioo 0 T))) (w : EnergyGraphSpace O)
    (U : Lp (EnergyGraphSpace O) 2 (volume.restrict (Set.Ioo 0 T))) :
    energyTimeFormFunctional ha hb hSlice hη w U =
      ∫ t in Set.Ioo 0 T, η t * energyFormValue O a b t (U t) w := by
  rw [energyTimeFormFunctional, ContinuousLinearMap.comp_apply, innerSL_apply_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hη.coeFn_toLp, energyTimeFormMap_coeFn ha hb hSlice w U] with t hηt ht
  simp only [RCLike.inner_apply, conj_trivial, hηt, ht]
  ring

include ha hb hSlice in
theorem energyTimeFormFunctional_norm_le {η : ℝ → ℝ}
    (hη : MemLp η 2 (volume.restrict (Set.Ioo 0 T))) (w : EnergyGraphSpace O) :
    ‖energyTimeFormFunctional ha hb hSlice hη w‖ ≤
      max 0 (energyFormBound n A D) * ‖w‖ * ‖hη.toLp η‖ := by
  calc
    _ ≤ ‖innerSL ℝ (hη.toLp η)‖ * ‖energyTimeFormMap ha hb hSlice w‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖hη.toLp η‖ * (max 0 (energyFormBound n A D) * ‖w‖) := by
      rw [innerSL_apply_norm]
      exact mul_le_mul_of_nonneg_left (energyTimeFormMap_norm_le ha hb hSlice w) (norm_nonneg _)
    _ = _ := by ring

include ha hb hSlice in
theorem energyTimeFormFunctional_norm_le_of_nonneg {η : ℝ → ℝ}
    (hη : MemLp η 2 (volume.restrict (Set.Ioo 0 T))) (w : EnergyGraphSpace O)
    (hA : 0 ≤ A) (hD : 0 ≤ D) :
    ‖energyTimeFormFunctional ha hb hSlice hη w‖ ≤
      energyFormBound n A D * ‖w‖ * ‖hη.toLp η‖ := by
  simpa only [max_eq_right (energyFormBound_pos hA hD).le] using
    energyTimeFormFunctional_norm_le ha hb hSlice hη w

end FixedTest

section FixedLinearMap
variable {α E : Type*} [MeasurableSpace α] {ν : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem timeTestFunctional_integrable {η : α → ℝ} (hη : MemLp η 2 ν)
    (L : E →L[ℝ] ℝ) {U : α → E} (hU : MemLp U 2 ν) :
    Integrable (fun t => η t * L (U t)) ν :=
  hη.integrable_mul (L.comp_memLp' hU)

/-- A generic fixed continuous linear spatial functional with an actual `L²` time test. -/
def timeTestFunctional {η : α → ℝ} (hη : MemLp η 2 ν) (L : E →L[ℝ] ℝ) :
    Lp E 2 ν →L[ℝ] ℝ :=
  (innerSL ℝ (hη.toLp η)).comp (L.compLpL 2 ν)

theorem timeTestFunctional_apply {η : α → ℝ} (hη : MemLp η 2 ν)
    (L : E →L[ℝ] ℝ) (U : Lp E 2 ν) :
    timeTestFunctional hη L U = ∫ t, η t * L (U t) ∂ν := by
  rw [timeTestFunctional, ContinuousLinearMap.comp_apply, innerSL_apply_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hη.coeFn_toLp, L.coeFn_compLpL (p := 2) (μ := ν) U] with t hηt ht
  simp only [RCLike.inner_apply, conj_trivial, hηt, ht]
  ring

theorem timeTestFunctional_norm_le {η : α → ℝ} (hη : MemLp η 2 ν)
    (L : E →L[ℝ] ℝ) : ‖timeTestFunctional hη L‖ ≤ ‖L‖ * ‖hη.toLp η‖ := by
  calc
    _ ≤ ‖innerSL ℝ (hη.toLp η)‖ * ‖L.compLpL 2 ν‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖hη.toLp η‖ * ‖L‖ := by
      rw [innerSL_apply_norm]
      exact mul_le_mul_of_nonneg_left (L.norm_compLpL_le (p := 2) (μ := ν)) (norm_nonneg _)
    _ = _ := mul_comm _ _

end FixedLinearMap
end Yau.LeafProofs.L16Aux
