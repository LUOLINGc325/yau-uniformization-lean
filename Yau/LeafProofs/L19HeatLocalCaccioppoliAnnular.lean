import Yau.LeafProofs.L19HeatCaccioppoliAnnular
import Yau.LeafProofs.L19HeatLocalCaccioppoli

/-! Annular energy on compact slabs inside an arbitrary open time domain. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.LeafProofs.L19Aux.LocalTime
open L12Aux L18Aux
variable {n : ℕ} {M : ComplexManifold n} {I : Set ℝ}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
/-- A compact-region integral of an original jointly smooth scalar is
continuous in positive time, without spatial compact support of the scalar. -/
theorem smoothSpaceTime_integralOn_compact_continuousOn (hI : IsOpen I)
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {v : M.Carrier → ℝ → ℝ} (hv : SmoothSpaceTime v I)
    {K : Set M.Carrier} (hK : IsCompact K) :
    ContinuousOn (fun t => ∫ x in K, v x t ∂μ) I := by
  let : IsLocallyFiniteMeasure μ := riemannianVolume_locallyFinite g μ hμ
  let : LocallyCompactSpace I := hI.locallyCompactSpace
  rw [continuousOn_iff_continuous_domRestrict]
  apply continuous_parametric_integral_of_continuous (f := fun (t : I) x => v x t) ?_ hK
  rw [continuous_iff_continuousAt]
  intro p
  exact (smoothSpaceTime_continuousAt hI hv p.2 p.1.property).comp
    (f := fun q : I × M.Carrier => (q.2, (q.1 : ℝ)))
    (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst)).continuousAt

/-- Compact-region positive-time integrals are interval integrable. -/
theorem smoothSpaceTime_integralOn_compact_intervalIntegrable (hI : IsOpen I)
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {v : M.Carrier → ℝ → ℝ} (hv : SmoothSpaceTime v I)
    {K : Set M.Carrier} (hK : IsCompact K) {s T : ℝ} (hslab : Icc s T ⊆ I) (hsT : s ≤ T) :
    IntervalIntegrable (fun t => ∫ x in K, v x t ∂μ) volume s T := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hsT]
  exact (smoothSpaceTime_integralOn_compact_continuousOn hI g μ hμ hv hK).mono
    hslab

/-- Transfer an actual smooth annular cutoff estimate to the unweighted
energy on the inner annulus. All localized scalar integrals are constructed. -/
theorem scalarHeat_caccioppoli_annular_transfer (hI : IsOpen I)
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {u : M.Carrier → ℝ → ℝ} (hu : SmoothSpaceTime u I)
    (x : M.Carrier) (R C : ℝ)
    {η : M.Carrier → ℝ} (hη : SmoothFn η) (hcη : HasCompactSupport η)
    (hηrange : ∀ y, η y ∈ Icc (0 : ℝ) 1)
    (hηone : ∀ y, R ≤ inducedDistance g.form x y → inducedDistance g.form x y ≤ 2 * R → η y = 1)
    (hηsupp : tsupport η ⊆ {y | R / 2 ≤ inducedDistance g.form x y ∧ inducedDistance g.form x y ≤ 4 * R})
    (hηE : ∀ y, scalarGradientPair g.form η η y ≤ C / R ^ 2)
    {s T e : ℝ} (hslab : Icc s T ⊆ I) (hsT : s ≤ T) (he : e ∈ I)
    (henergy : (∫ t in s..T, ∫ y, η y ^ 2 * scalarGradientPair g.form
      (fun z => u z t) (fun z => u z t) y ∂μ) ≤
      2 * (∫ y, η y ^ 2 * (u y e) ^ 2 ∂μ) +
      4 * ∫ t in s..T, ∫ y, (u y t) ^ 2 * scalarGradientPair g.form η η y ∂μ) :
    (∫ t in s..T, ∫ y in {y | R ≤ inducedDistance g.form x y ∧ inducedDistance g.form x y ≤ 2 * R},
      scalarGradientPair g.form (fun z => u z t) (fun z => u z t) y ∂μ) ≤
      2 * (∫ y in {y | R / 2 ≤ inducedDistance g.form x y ∧ inducedDistance g.form x y ≤ 4 * R},
        (u y e) ^ 2 ∂μ) +
      (4 * C / R ^ 2) * ∫ t in s..T,
        ∫ y in {y | R / 2 ≤ inducedDistance g.form x y ∧ inducedDistance g.form x y ≤ 4 * R},
          (u y t) ^ 2 ∂μ := by
  let S := {y | R ≤ inducedDistance g.form x y ∧ inducedDistance g.form x y ≤ 2 * R}
  let K := {y | R / 2 ≤ inducedDistance g.form x y ∧ inducedDistance g.form x y ≤ 4 * R}
  have hS : IsCompact S := scalarHeat_annulus_isCompact g x R (2 * R)
  have hK : IsCompact K := scalarHeat_annulus_isCompact g x (R / 2) (4 * R)
  have hreg := scalarHeat_cutoff_integrable hI g μ hμ hu hη hcη hslab hsT
  have hu2 : SmoothSpaceTime (fun y t => (u y t) ^ 2) I := fun a => (hu a).pow 2
  have hKi (t : ℝ) (ht : t ∈ I) : IntegrableOn (fun y => (u y t) ^ 2) K μ :=
    smoothFn_integrableOn_compact g μ hμ (smoothFn_pow (smoothSpaceTime_slice hu ht) 2) hK
  have hKt : IntervalIntegrable (fun t => ∫ y in K, (u y t) ^ 2 ∂μ) volume s T :=
    smoothSpaceTime_integralOn_compact_intervalIntegrable hI g μ hμ hu2 hK hslab hsT
  have hSt : IntervalIntegrable (fun t => ∫ y in S,
      scalarGradientPair g.form (fun z => u z t) (fun z => u z t) y ∂μ) volume s T :=
    smoothSpaceTime_integralOn_compact_intervalIntegrable hI g μ hμ
      (smoothSpaceTime_scalarGradientPair hI g hu hu) hS hslab hsT
  have hF : (∫ y, η y ^ 2 * (u y e) ^ 2 ∂μ) ≤ ∫ y in K, (u y e) ^ 2 ∂μ := by
    calc
      _ = ∫ y in K, η y ^ 2 * (u y e) ^ 2 ∂μ := by
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro y hy
        have hz : η y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (hηsupp h))
        simp [hz]
      _ ≤ _ := by
        apply setIntegral_mono_on (hreg.1 e he).1.integrableOn (hKi e he) hK.measurableSet
        intro y _hy
        have hy0 := (hηrange y).1
        have hy1 := (hηrange y).2
        exact mul_le_of_le_one_left (sq_nonneg _) (by nlinarith)
  have hB (t : ℝ) (ht : t ∈ I) :
      (∫ y, (u y t) ^ 2 * scalarGradientPair g.form η η y ∂μ) ≤
        (C / R ^ 2) * ∫ y in K, (u y t) ^ 2 ∂μ := by
    calc
      _ = ∫ y in K, (u y t) ^ 2 * scalarGradientPair g.form η η y ∂μ := by
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro y hy
        rw [scalarGradientPair_zero_of_notMem_tsupport g.form η η
          (fun h => hy (hηsupp h)), mul_zero]
      _ ≤ ∫ y in K, (C / R ^ 2) * (u y t) ^ 2 ∂μ := by
        apply setIntegral_mono_on (hreg.1 t ht).2.2.integrableOn ((hKi t ht).const_mul _) hK.measurableSet
        intro y _hy
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hηE y) (sq_nonneg (u y t))
      _ = _ := integral_const_mul _ _
  have hAt := intervalIntegral.integral_mono_on hsT hSt hreg.2.1 (fun t ht => by
    have ht0 := hslab ht
    calc
      (∫ y in S, scalarGradientPair g.form (fun z => u z t) (fun z => u z t) y ∂μ) =
          ∫ y in S, η y ^ 2 * scalarGradientPair g.form (fun z => u z t) (fun z => u z t) y ∂μ := by
        apply setIntegral_congr_fun hS.measurableSet
        intro y hy
        dsimp only
        rw [hηone y hy.1 hy.2, one_pow, one_mul]
      _ ≤ ∫ y, η y ^ 2 * scalarGradientPair g.form (fun z => u z t) (fun z => u z t) y ∂μ :=
        setIntegral_le_integral (hreg.1 t ht0).2.1
          (ae_of_all _ (fun y => mul_nonneg (sq_nonneg _) (scalarGradientPair_self_nonneg g.form _ _)) ))
  have hBt := intervalIntegral.integral_mono_on hsT hreg.2.2 (hKt.const_mul (C / R ^ 2))
    (fun t ht => hB t (hslab ht))
  rw [intervalIntegral.integral_const_mul] at hBt
  calc
    _ ≤ ∫ t in s..T, ∫ y, η y ^ 2 * scalarGradientPair g.form (fun z => u z t) (fun z => u z t) y ∂μ := hAt
    _ ≤ 2 * (∫ y, η y ^ 2 * (u y e) ^ 2 ∂μ) +
        4 * ∫ t in s..T, ∫ y, (u y t) ^ 2 * scalarGradientPair g.form η η y ∂μ := henergy
    _ ≤ 2 * (∫ y in K, (u y e) ^ 2 ∂μ) +
        4 * ((C / R ^ 2) * ∫ t in s..T, ∫ y in K, (u y t) ^ 2 ∂μ) := by linarith
    _ = _ := by ring



/-- Every integral occurring in the annular estimates is genuinely
integrable, using only original joint smoothness and compact annuli. -/
theorem scalarHeat_annular_integrable (hI : IsOpen I)
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {u : M.Carrier → ℝ → ℝ} (hu : SmoothSpaceTime u I)
    (x : M.Carrier) (r R : ℝ) {s T : ℝ} (hslab : Icc s T ⊆ I) (hsT : s ≤ T) :
    (∀ t, t ∈ I →
      IntegrableOn (fun y => (u y t) ^ 2)
        {y | r ≤ inducedDistance g.form x y ∧ inducedDistance g.form x y ≤ R} μ ∧
      IntegrableOn (fun y => scalarGradientPair g.form (fun z => u z t) (fun z => u z t) y)
        {y | r ≤ inducedDistance g.form x y ∧ inducedDistance g.form x y ≤ R} μ) ∧
    IntervalIntegrable (fun t => ∫ y in
      {y | r ≤ inducedDistance g.form x y ∧ inducedDistance g.form x y ≤ R}, (u y t) ^ 2 ∂μ) volume s T ∧
    IntervalIntegrable (fun t => ∫ y in
      {y | r ≤ inducedDistance g.form x y ∧ inducedDistance g.form x y ≤ R},
      scalarGradientPair g.form (fun z => u z t) (fun z => u z t) y ∂μ) volume s T := by
  have hK := scalarHeat_annulus_isCompact g x r R
  have hu2 : SmoothSpaceTime (fun y t => (u y t) ^ 2) I := fun a => (hu a).pow 2
  have hP := smoothSpaceTime_scalarGradientPair hI g hu hu
  refine ⟨?_, smoothSpaceTime_integralOn_compact_intervalIntegrable hI g μ hμ hu2 hK hslab hsT,
    smoothSpaceTime_integralOn_compact_intervalIntegrable hI g μ hμ hP hK hslab hsT⟩
  intro t ht
  exact ⟨smoothFn_integrableOn_compact g μ hμ (smoothSpaceTime_slice hu2 ht) hK,
    smoothFn_integrableOn_compact g μ hμ (smoothSpaceTime_slice hP ht) hK⟩

/-- Uniform actual annular Caccioppoli for both forward and backward heat.
The sole constant is selected before the geometry; no cutoff existence,
positivity, growth, mass or abstract regularity assumption is supplied. -/
theorem exists_uniform_scalar_heat_annular_caccioppoli (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ComplexManifold n) (g : SmoothMetric M), IsKahler g →
      ∀ (μ : Measure M.Carrier), IsRiemannianVolume g.form μ →
      ∀ (I : Set ℝ), IsOpen I → ∀ (u : M.Carrier → ℝ → ℝ), SmoothSpaceTime u I →
      ∀ (x : M.Carrier) (R : ℝ), 0 < R → ∀ (s T : ℝ), Icc s T ⊆ I → s ≤ T →
      ((∀ y t, t ∈ I → HasDerivAt (u y) (laplacian g.form (fun z => u z t) y) t) →
        (∫ t in s..T, ∫ y in {y | R ≤ inducedDistance g.form x y ∧ inducedDistance g.form x y ≤ 2 * R},
          scalarGradientPair g.form (fun z => u z t) (fun z => u z t) y ∂μ) ≤
          2 * (∫ y in {y | R / 2 ≤ inducedDistance g.form x y ∧ inducedDistance g.form x y ≤ 4 * R},
            (u y s) ^ 2 ∂μ) +
          (C / R ^ 2) * ∫ t in s..T,
            ∫ y in {y | R / 2 ≤ inducedDistance g.form x y ∧ inducedDistance g.form x y ≤ 4 * R},
              (u y t) ^ 2 ∂μ) ∧
      ((∀ y t, t ∈ I → HasDerivAt (u y) (-laplacian g.form (fun z => u z t) y) t) →
        (∫ t in s..T, ∫ y in {y | R ≤ inducedDistance g.form x y ∧ inducedDistance g.form x y ≤ 2 * R},
          scalarGradientPair g.form (fun z => u z t) (fun z => u z t) y ∂μ) ≤
          2 * (∫ y in {y | R / 2 ≤ inducedDistance g.form x y ∧ inducedDistance g.form x y ≤ 4 * R},
            (u y T) ^ 2 ∂μ) +
          (C / R ^ 2) * ∫ t in s..T,
            ∫ y in {y | R / 2 ≤ inducedDistance g.form x y ∧ inducedDistance g.form x y ≤ 4 * R},
              (u y t) ^ 2 ∂μ) := by
  obtain ⟨A, hA, hcut⟩ := exists_uniform_scalar_heat_annular_cutoffs n
  refine ⟨4 * A, by positivity, ?_⟩
  intro M g hK μ hμ I hI u hu x R hR s T hslab hsT
  obtain ⟨η, _hηC, hη, hcη, hηrange, hηone, hηsupp, hηE⟩ := hcut M g x R hR
  constructor
  · intro hheat
    exact scalarHeat_caccioppoli_annular_transfer hI g μ hμ hu x R A hη hcη hηrange hηone
      hηsupp hηE hslab hsT (hslab ⟨le_rfl, hsT⟩)
      (scalarHeat_caccioppoli_forward hI g hK μ hμ hu hheat hη hcη hslab hsT)
  · intro hheat
    exact scalarHeat_caccioppoli_annular_transfer hI g μ hμ hu x R A hη hcη hηrange hηone
      hηsupp hηE hslab hsT (hslab ⟨hsT, le_rfl⟩)
      (scalarHeat_caccioppoli_backward hI g hK μ hμ hu hheat hη hcη hslab hsT)


end Yau.LeafProofs.L19Aux.LocalTime
