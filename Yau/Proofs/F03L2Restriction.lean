import Yau.Proofs.F03ScalarL2

/-! Genuine restriction and zero extension in the actual scalar L² spaces. -/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal InnerProductSpace

namespace Yau.Proofs.F03Aux
set_option backward.isDefEq.respectTransparency false

variable {α : Type*} [MeasurableSpace α]

def restrictL2 (μ : Measure α) (O : Set α) (f : Lp ℝ 2 μ) : Lp ℝ 2 (μ.restrict O) :=
  ((Lp.memLp f).restrict O).toLp f

theorem restrictL2_coe (μ : Measure α) (O : Set α) (f : Lp ℝ 2 μ) :
    restrictL2 μ O f =ᵐ[μ.restrict O] f := ((Lp.memLp f).restrict O).coeFn_toLp

theorem restrictL2_norm_le (μ : Measure α) (O : Set α) (f : Lp ℝ 2 μ) :
    ‖restrictL2 μ O f‖ ≤ ‖f‖ := by
  rw [restrictL2, Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp f).eLpNorm_ne_top (eLpNorm_restrict_le f 2 μ O)

def restrictL2Linear (μ : Measure α) (O : Set α) :
    Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 (μ.restrict O) where
  toFun := restrictL2 μ O
  map_add' f k := by
    apply Lp.ext
    filter_upwards [restrictL2_coe μ O (f + k), restrictL2_coe μ O f, restrictL2_coe μ O k,
      ae_restrict_of_ae (Lp.coeFn_add f k), Lp.coeFn_add (restrictL2 μ O f) (restrictL2 μ O k)]
      with x hsum hf hk hsource htarget
    simp only [hsum, htarget, Pi.add_apply, hsource, hf, hk]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [restrictL2_coe μ O (c • f), restrictL2_coe μ O f,
      ae_restrict_of_ae (Lp.coeFn_smul c f), Lp.coeFn_smul c (restrictL2 μ O f)]
      with x hsmul hf hsource htarget
    simp only [RingHom.id_apply, hsmul, htarget, Pi.smul_apply, hsource, hf]

def l2Restriction (μ : Measure α) (O : Set α) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 (μ.restrict O) :=
  (restrictL2Linear μ O).mkContinuous 1 (fun f => by
    change ‖restrictL2 μ O f‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using restrictL2_norm_le μ O f)

theorem l2Restriction_apply (μ : Measure α) (O : Set α) (f : Lp ℝ 2 μ) :
    l2Restriction μ O f = restrictL2 μ O f := rfl

def extendL2 (μ : Measure α) (O : Set α) (hO : MeasurableSet O)
    (f : Lp ℝ 2 (μ.restrict O)) : Lp ℝ 2 μ :=
  ((memLp_indicator_iff_restrict hO.nullMeasurableSet).mpr (Lp.memLp f)).toLp (O.indicator f)

theorem extendL2_coe (μ : Measure α) (O : Set α) (hO : MeasurableSet O)
    (f : Lp ℝ 2 (μ.restrict O)) : extendL2 μ O hO f =ᵐ[μ] O.indicator f :=
  ((memLp_indicator_iff_restrict hO.nullMeasurableSet).mpr (Lp.memLp f)).coeFn_toLp

theorem extendL2_norm (μ : Measure α) (O : Set α) (hO : MeasurableSet O)
    (f : Lp ℝ 2 (μ.restrict O)) : ‖extendL2 μ O hO f‖ = ‖f‖ := by
  rw [extendL2, Lp.norm_toLp, eLpNorm_indicator_eq_eLpNorm_restrict hO.nullMeasurableSet]
  rfl

def extendL2Linear (μ : Measure α) (O : Set α) (hO : MeasurableSet O) :
    Lp ℝ 2 (μ.restrict O) →ₗ[ℝ] Lp ℝ 2 μ where
  toFun := extendL2 μ O hO
  map_add' f k := by
    apply Lp.ext
    have hsource := (ae_eq_restrict_iff_indicator_ae_eq hO).mp (Lp.coeFn_add f k)
    filter_upwards [extendL2_coe μ O hO (f + k), extendL2_coe μ O hO f,
      extendL2_coe μ O hO k, Lp.coeFn_add (extendL2 μ O hO f) (extendL2 μ O hO k), hsource]
      with x hsum hf hk htarget hsource
    rw [hsum, htarget, Pi.add_apply, hf, hk, hsource]
    by_cases hx : x ∈ O <;> simp [Set.indicator, hx]
  map_smul' c f := by
    apply Lp.ext
    have hsource := (ae_eq_restrict_iff_indicator_ae_eq hO).mp (Lp.coeFn_smul c f)
    filter_upwards [extendL2_coe μ O hO (c • f), extendL2_coe μ O hO f,
      Lp.coeFn_smul c (extendL2 μ O hO f), hsource]
      with x hsmul hf htarget hsource
    simp only [RingHom.id_apply]
    rw [hsmul, htarget, Pi.smul_apply, hf, hsource]
    by_cases hx : x ∈ O <;> simp [Set.indicator, hx]

def l2ZeroExtension (μ : Measure α) (O : Set α) (hO : MeasurableSet O) :
    Lp ℝ 2 (μ.restrict O) →L[ℝ] Lp ℝ 2 μ :=
  (extendL2Linear μ O hO).mkContinuous 1 (fun f => by
    rw [show extendL2Linear μ O hO f = extendL2 μ O hO f from rfl, extendL2_norm, one_mul])

theorem l2ZeroExtension_apply (μ : Measure α) (O : Set α) (hO : MeasurableSet O)
    (f : Lp ℝ 2 (μ.restrict O)) : l2ZeroExtension μ O hO f = extendL2 μ O hO f := rfl

theorem l2ZeroExtension_norm (μ : Measure α) (O : Set α) (hO : MeasurableSet O)
    (f : Lp ℝ 2 (μ.restrict O)) : ‖l2ZeroExtension μ O hO f‖ = ‖f‖ :=
  extendL2_norm μ O hO f

theorem l2Restriction_zeroExtension (μ : Measure α) (O : Set α) (hO : MeasurableSet O)
    (f : Lp ℝ 2 (μ.restrict O)) : l2Restriction μ O (l2ZeroExtension μ O hO f) = f := by
  apply Lp.ext
  filter_upwards [restrictL2_coe μ O (l2ZeroExtension μ O hO f),
    ae_restrict_of_ae (extendL2_coe μ O hO f), ae_restrict_mem hO] with x hr he hx
  change restrictL2 μ O (l2ZeroExtension μ O hO f) x = f x
  rw [hr]
  change extendL2 μ O hO f x = f x
  rw [he, indicator_of_mem hx]

theorem l2ZeroExtension_restriction_of_ae_zero (μ : Measure α) (O : Set α)
    (hO : MeasurableSet O) (f : Lp ℝ 2 μ) (hf : ∀ᵐ x ∂μ, x ∉ O → f x = 0) :
    l2ZeroExtension μ O hO (l2Restriction μ O f) = f := by
  apply Lp.ext
  have hr := (ae_eq_restrict_iff_indicator_ae_eq hO).mp (restrictL2_coe μ O f)
  filter_upwards [extendL2_coe μ O hO (l2Restriction μ O f), hr, hf] with x he hr hf
  change extendL2 μ O hO (l2Restriction μ O f) x = f x
  rw [he]
  change O.indicator (restrictL2 μ O f) x = f x
  rw [hr]
  by_cases hx : x ∈ O
  · exact indicator_of_mem hx _
  · rw [indicator_of_notMem hx, hf hx]

end Yau.Proofs.F03Aux
