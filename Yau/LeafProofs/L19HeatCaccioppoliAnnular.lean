import Yau.LeafProofs.L19HeatCaccioppoli

/-! Genuine annular spatial cutoffs and localized heat energy estimates. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.LeafProofs.L19Aux
open L12Aux L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- A compact-region integral of an original jointly smooth scalar is
continuous in positive time, without spatial compact support of the scalar. -/
theorem smoothSpaceTime_integralOn_compact_continuousOn
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {v : M.Carrier → ℝ → ℝ} (hv : SmoothSpaceTime v (Ioi 0))
    {K : Set M.Carrier} (hK : IsCompact K) :
    ContinuousOn (fun t => ∫ x in K, v x t ∂μ) (Ioi 0) := by
  let : IsLocallyFiniteMeasure μ := riemannianVolume_locallyFinite g μ hμ
  let : LocallyCompactSpace (Ioi (0 : ℝ)) := isOpen_Ioi.locallyCompactSpace
  rw [continuousOn_iff_continuous_domRestrict]
  apply continuous_parametric_integral_of_continuous (f := fun (t : Ioi (0 : ℝ)) x => v x t) ?_ hK
  rw [continuous_iff_continuousAt]
  intro p
  exact (smoothSpaceTime_continuousAt hv p.2 p.1.property).comp
    (f := fun q : Ioi (0 : ℝ) × M.Carrier => (q.2, (q.1 : ℝ)))
    (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst)).continuousAt

/-- Compact-region positive-time integrals are interval integrable. -/
theorem smoothSpaceTime_integralOn_compact_intervalIntegrable
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {v : M.Carrier → ℝ → ℝ} (hv : SmoothSpaceTime v (Ioi 0))
    {K : Set M.Carrier} (hK : IsCompact K) {s T : ℝ} (hs : 0 < s) (hsT : s ≤ T) :
    IntervalIntegrable (fun t => ∫ x in K, v x t ∂μ) volume s T := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hsT]
  exact (smoothSpaceTime_integralOn_compact_continuousOn g μ hμ hv hK).mono
    (fun _ ht => hs.trans_le ht.1)

/-- A true smooth compact annular cutoff. Its dimensional energy constant
is chosen before the geometry and its support lies in the expanded annulus. -/
theorem exists_uniform_scalar_heat_annular_cutoffs (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ComplexManifold n) (g : SmoothMetric M)
      (x : M.Carrier) (R : ℝ), 0 < R →
      ∃ η : M.Carrier → ℝ,
        ContMDiff 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) ∞ η ∧ SmoothFn η ∧ HasCompactSupport η ∧
        (∀ y, η y ∈ Icc (0 : ℝ) 1) ∧
        (∀ y, R ≤ inducedDistance g.form x y → inducedDistance g.form x y ≤ 2 * R → η y = 1) ∧
        tsupport η ⊆ {y | R / 2 ≤ inducedDistance g.form x y ∧ inducedDistance g.form x y ≤ 4 * R} ∧
        ∀ y, scalarGradientPair g.form η η y ≤ C / R ^ 2 := by
  obtain ⟨A, hA, hcut⟩ := exists_uniform_annular_scalar_energy_cutoffs n
  refine ⟨10 * A ^ 2, by positivity, ?_⟩
  intro M g x R hR
  obtain ⟨α, hαC, hα, hcα, hαrange, hαone, hαs, hαE⟩ :=
    hcut M g x (R / 2) R (by positivity) (by linarith)
  obtain ⟨β, hβC, hβ, hcβ, hβrange, hβone, hβs, hβE⟩ :=
    hcut M g x (2 * R) (4 * R) (by positivity) (by linarith)
  let η : M.Carrier → ℝ := fun y => (1 - α y) * β y
  have hη : SmoothFn η := smoothFn_mul (smoothFn_sub (smoothFn_const 1) hα) hβ
  refine ⟨η, (contMDiff_const.sub hαC).mul hβC, hη, hcβ.mul_left, ?_, ?_, ?_, ?_⟩
  · intro y
    have hαy := hαrange y
    have hβy := hβrange y
    exact ⟨mul_nonneg (by linarith [hαy.2]) hβy.1,
      by dsimp [η]; nlinarith [hβy.2, mul_nonneg hαy.1 hβy.1]⟩
  · intro y hy hy'
    have hzero : α y = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hyα
      have hd := (mem_distBall_iff g x y hR).mp (hαs hyα)
      linarith
    simp only [η, hzero, sub_zero, one_mul, hβone y hy']
  · have hsupp : Function.support η ⊆
        {y | R / 2 ≤ inducedDistance g.form x y ∧ inducedDistance g.form x y ≤ 4 * R} := by
      intro y hy
      constructor
      · by_contra hd
        have hz := hαone y (le_of_not_ge hd)
        exact hy (by simp [η, hz])
      · have hyβ : β y ≠ 0 := by intro hz; exact hy (by simp [η, hz])
        exact ((mem_distBall_iff g x y (by positivity)).mp (hβs (subset_closure hyβ))).le
    exact closure_minimal hsupp ((isClosed_le continuous_const (continuous_distFrom g x)).inter
      (isClosed_le (continuous_distFrom g x) continuous_const))
  · intro y
    have hc : scalarGradientPair g.form (fun z => 1 - α z) (fun z => 1 - α z) y =
        scalarGradientPair g.form α α y := by
      rw [scalarGradientPair_scalar_comp_self g.form hα (fun t : ℝ => 1 - t) y
        (((hasDerivAt_const (α y) 1).sub (hasDerivAt_id (α y))).differentiableAt)]
      have hd : deriv (fun t : ℝ => 1 - t) (α y) = -1 := by
        convert ((hasDerivAt_const (α y) (1 : ℝ)).sub (hasDerivAt_id (α y))).deriv using 1 <;> norm_num
      rw [hd]
      norm_num
    have hp := scalarGradientPair_product_self_le g.form hβ
      (smoothFn_sub (smoothFn_const 1) hα) y
    rw [hc] at hp
    have hα0 := (hαrange y).1
    have hα1 := (hαrange y).2
    have hβ0 := (hβrange y).1
    have hβ1 := (hβrange y).2
    have hαsq : (1 - α y) ^ 2 ≤ 1 := by nlinarith
    have hβsq : β y ^ 2 ≤ 1 := by nlinarith
    have hαnonneg := scalarGradientPair_self_nonneg g.form α y
    have hβnonneg := scalarGradientPair_self_nonneg g.form β y
    have hleft := mul_le_mul_of_nonneg_right hαsq hβnonneg
    have hright := mul_le_mul_of_nonneg_right hβsq hαnonneg
    have hαval : (A / (R - R / 2)) ^ 2 = 4 * A ^ 2 / R ^ 2 := by field_simp; ring
    have hβval : (A / (4 * R - 2 * R)) ^ 2 = (1 / 4 : ℝ) * A ^ 2 / R ^ 2 := by field_simp; ring
    have hαbound := hαE y
    have hβbound := hβE y
    rw [hαval] at hαbound
    rw [hβval] at hβbound
    change scalarGradientPair g.form η η y ≤ 10 * A ^ 2 / R ^ 2
    change scalarGradientPair g.form η η y ≤ _ at hp
    simp only [mul_div_assoc] at hαbound hβbound ⊢
    nlinarith [div_nonneg (sq_nonneg A) (sq_nonneg R)]



/-- Closed annuli of the original induced distance are compact. -/
theorem scalarHeat_annulus_isCompact (g : SmoothMetric M) (x : M.Carrier) (r R : ℝ) :
    IsCompact {y | r ≤ inducedDistance g.form x y ∧ inducedDistance g.form x y ≤ R} := by
  apply (isCompact_inducedDistance_sublevel g x R).of_isClosed_subset
    ((isClosed_le continuous_const (continuous_distFrom g x)).inter
      (isClosed_le (continuous_distFrom g x) continuous_const))
  intro y hy
  exact hy.2

/-- Transfer an actual smooth annular cutoff estimate to the unweighted
energy on the inner annulus. All localized scalar integrals are constructed. -/
theorem scalarHeat_caccioppoli_annular_transfer
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {u : M.Carrier → ℝ → ℝ} (hu : SmoothSpaceTime u (Ioi 0))
    (x : M.Carrier) (R C : ℝ)
    {η : M.Carrier → ℝ} (hη : SmoothFn η) (hcη : HasCompactSupport η)
    (hηrange : ∀ y, η y ∈ Icc (0 : ℝ) 1)
    (hηone : ∀ y, R ≤ inducedDistance g.form x y → inducedDistance g.form x y ≤ 2 * R → η y = 1)
    (hηsupp : tsupport η ⊆ {y | R / 2 ≤ inducedDistance g.form x y ∧ inducedDistance g.form x y ≤ 4 * R})
    (hηE : ∀ y, scalarGradientPair g.form η η y ≤ C / R ^ 2)
    {s T e : ℝ} (hs : 0 < s) (hsT : s ≤ T) (he : 0 < e)
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
  have hreg := scalarHeat_cutoff_integrable g μ hμ hu hη hcη hs hsT
  have hu2 : SmoothSpaceTime (fun y t => (u y t) ^ 2) (Ioi 0) := fun a => (hu a).pow 2
  have hKi (t : ℝ) (ht : 0 < t) : IntegrableOn (fun y => (u y t) ^ 2) K μ :=
    smoothFn_integrableOn_compact g μ hμ (smoothFn_pow (smoothSpaceTime_slice hu ht) 2) hK
  have hKt : IntervalIntegrable (fun t => ∫ y in K, (u y t) ^ 2 ∂μ) volume s T :=
    smoothSpaceTime_integralOn_compact_intervalIntegrable g μ hμ hu2 hK hs hsT
  have hSt : IntervalIntegrable (fun t => ∫ y in S,
      scalarGradientPair g.form (fun z => u z t) (fun z => u z t) y ∂μ) volume s T :=
    smoothSpaceTime_integralOn_compact_intervalIntegrable g μ hμ
      (smoothSpaceTime_scalarGradientPair g hu hu) hS hs hsT
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
  have hB (t : ℝ) (ht : 0 < t) :
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
    have ht0 := hs.trans_le ht.1
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
    (fun t ht => hB t (hs.trans_le ht.1))
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
theorem scalarHeat_annular_integrable
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {u : M.Carrier → ℝ → ℝ} (hu : SmoothSpaceTime u (Ioi 0))
    (x : M.Carrier) (r R : ℝ) {s T : ℝ} (hs : 0 < s) (hsT : s ≤ T) :
    (∀ t, 0 < t →
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
  have hu2 : SmoothSpaceTime (fun y t => (u y t) ^ 2) (Ioi 0) := fun a => (hu a).pow 2
  have hP := smoothSpaceTime_scalarGradientPair g hu hu
  refine ⟨?_, smoothSpaceTime_integralOn_compact_intervalIntegrable g μ hμ hu2 hK hs hsT,
    smoothSpaceTime_integralOn_compact_intervalIntegrable g μ hμ hP hK hs hsT⟩
  intro t ht
  exact ⟨smoothFn_integrableOn_compact g μ hμ (smoothSpaceTime_slice hu2 ht) hK,
    smoothFn_integrableOn_compact g μ hμ (smoothSpaceTime_slice hP ht) hK⟩

/-- Uniform actual annular Caccioppoli for both forward and backward heat.
The sole constant is selected before the geometry; no cutoff existence,
positivity, growth, mass or abstract regularity assumption is supplied. -/
theorem exists_uniform_scalar_heat_annular_caccioppoli (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ComplexManifold n) (g : SmoothMetric M), IsKahler g →
      ∀ (μ : Measure M.Carrier), IsRiemannianVolume g.form μ →
      ∀ (u : M.Carrier → ℝ → ℝ), SmoothSpaceTime u (Ioi 0) →
      ∀ (x : M.Carrier) (R : ℝ), 0 < R → ∀ (s T : ℝ), 0 < s → s ≤ T →
      ((∀ y t, 0 < t → HasDerivAt (u y) (laplacian g.form (fun z => u z t) y) t) →
        (∫ t in s..T, ∫ y in {y | R ≤ inducedDistance g.form x y ∧ inducedDistance g.form x y ≤ 2 * R},
          scalarGradientPair g.form (fun z => u z t) (fun z => u z t) y ∂μ) ≤
          2 * (∫ y in {y | R / 2 ≤ inducedDistance g.form x y ∧ inducedDistance g.form x y ≤ 4 * R},
            (u y s) ^ 2 ∂μ) +
          (C / R ^ 2) * ∫ t in s..T,
            ∫ y in {y | R / 2 ≤ inducedDistance g.form x y ∧ inducedDistance g.form x y ≤ 4 * R},
              (u y t) ^ 2 ∂μ) ∧
      ((∀ y t, 0 < t → HasDerivAt (u y) (-laplacian g.form (fun z => u z t) y) t) →
        (∫ t in s..T, ∫ y in {y | R ≤ inducedDistance g.form x y ∧ inducedDistance g.form x y ≤ 2 * R},
          scalarGradientPair g.form (fun z => u z t) (fun z => u z t) y ∂μ) ≤
          2 * (∫ y in {y | R / 2 ≤ inducedDistance g.form x y ∧ inducedDistance g.form x y ≤ 4 * R},
            (u y T) ^ 2 ∂μ) +
          (C / R ^ 2) * ∫ t in s..T,
            ∫ y in {y | R / 2 ≤ inducedDistance g.form x y ∧ inducedDistance g.form x y ≤ 4 * R},
              (u y t) ^ 2 ∂μ) := by
  obtain ⟨A, hA, hcut⟩ := exists_uniform_scalar_heat_annular_cutoffs n
  refine ⟨4 * A, by positivity, ?_⟩
  intro M g hK μ hμ u hu x R hR s T hs hsT
  obtain ⟨η, _hηC, hη, hcη, hηrange, hηone, hηsupp, hηE⟩ := hcut M g x R hR
  constructor
  · intro hheat
    exact scalarHeat_caccioppoli_annular_transfer g μ hμ hu x R A hη hcη hηrange hηone
      hηsupp hηE hs hsT hs
      (scalarHeat_caccioppoli_forward g hK μ hμ hu hheat hη hcη hs hsT)
  · intro hheat
    exact scalarHeat_caccioppoli_annular_transfer g μ hμ hu x R A hη hcη hηrange hηone
      hηsupp hηE hs hsT (hs.trans_le hsT)
      (scalarHeat_caccioppoli_backward g hK μ hμ hu hheat hη hcη hs hsT)

end Yau.LeafProofs.L19Aux
