import Yau.LeafProofs.L24Localization

/-! Compact-cylinder localization and the genuine local scalar gradient bound. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.LeafProofs.L24Aux
open L12Aux L18Aux L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem bernsteinAuxiliary_cylinder_bound (g : SmoothMetric M) (hK : IsKahler g)
    (hRic : ∀ z, (ricci g.form z).PosSemidef)
    {v : M.Carrier → ℝ → ℝ} (hv : LeafCandidates.PositiveHeatSolution g.form v)
    (x : M.Carrier) {τ T R : ℝ} (hτ : 0 < τ) (hT : 0 < T) (hR : 0 < R)
    (hbound : ∀ z s, inducedDistance g.form x z ≤ R →
      s ∈ Set.Icc 0 T → v z (τ+s) ≤ 1) :
    bernsteinAuxiliary g v τ x T ≤ (2 / bernsteinBeta) *
      (1 + (8 * (n : ℝ) + 16 + 4 / bernsteinBeta) * T / R ^ 2) := by
  have hβ := bernsteinBeta_pos
  have hC : 0 ≤ (8 * (n : ℝ) + 16 + 4 / bernsteinBeta) / R ^ 2 := by positivity
  by_cases htarget : bernsteinAuxiliary g v τ x T ≤ 0
  · exact htarget.trans (by positivity)
  have htargetpos : 0 < bernsteinAuxiliary g v τ x T := lt_of_not_ge htarget
  have hW := bernsteinEnergy_smoothSpaceTime g hv.1
  have hcont : ContinuousOn (fun p : M.Carrier × ℝ => bernsteinEnergy g v p.1 (τ+p.2))
      ({y | inducedDistance g.form x y ≤ R} ×ˢ Set.Icc 0 T) := by
    intro p hp
    have ht : 0 < τ + p.2 := add_pos_of_pos_of_nonneg hτ hp.2.1
    have hmap : ContinuousAt (fun r : M.Carrier × ℝ => (r.1, τ+r.2)) p :=
      continuousAt_fst.prodMk (continuousAt_const.add continuousAt_snd)
    exact ((smoothSpaceTime_continuousAt hW p.1 ht).comp
      (f := fun r : M.Carrier × ℝ => (r.1, τ+r.2)) hmap).continuousWithinAt
  obtain ⟨q, s, hq, hs, hmax₀⟩ := exists_distanceCutoff_cylinder_maximum g x hR hT
    (W := fun z s => bernsteinEnergy g v z (τ+s)) hcont
  have hmax : ∀ y r, inducedDistance g.form x y ≤ R → r ∈ Set.Icc 0 T →
      distanceCutoff g x R y * bernsteinAuxiliary g v τ y r ≤
        distanceCutoff g x R q * bernsteinAuxiliary g v τ q s := by
    intro y r hy hr
    simpa only [bernsteinAuxiliary, mul_assoc] using hmax₀ y r hy hr
  have hxx : inducedDistance g.form x x ≤ R := by
    rw [g.induced_distance_eq_zero.mpr rfl]
    exact hR.le
  have hcenter := hmax x T hxx ⟨hT.le, le_rfl⟩
  rw [distanceCutoff_center, one_mul] at hcenter
  have hmaxpos : 0 < distanceCutoff g x R q * bernsteinAuxiliary g v τ q s :=
    htargetpos.trans_le hcenter
  have hpositive : 0 < distanceCutoff g x R q ∧ 0 < bernsteinAuxiliary g v τ q s := by
    rcases mul_pos_iff.mp hmaxpos with hh | hh
    · exact hh
    · exact False.elim ((not_lt_of_ge (distanceCutoff_nonneg g x R q)) hh.1)
  have hqinside : inducedDistance g.form x q < R :=
    (distanceCutoff_pos_iff g x q hR).mp hpositive.1
  have hspos : 0 < s := by
    by_contra h
    have hs0 : s = 0 := le_antisymm (le_of_not_gt h) hs.1
    simpa [bernsteinAuxiliary, hs0] using hpositive.2
  have htime : 0 < τ + s := add_pos hτ hspos
  obtain ⟨η, hηC2, hηvalue, hηnear, hηpos, hηone, hηgrad, hηlap⟩ :=
    exists_distanceCutoff_lower_support_chart g hK hRic x q hR hqinside
  have hF : SmoothFn (fun y => bernsteinAuxiliary g v τ y s) :=
    bernsteinAuxiliary_slice g hv.1 τ s htime
  have hspace : IsLocalMax (fun z => inChart q η z *
      inChart q (fun y => bernsteinAuxiliary g v τ y s) z) (chartPt q q) :=
    lower_support_preserves_space_max g x q hqinside hηvalue hηnear
      (continuous_of_smoothFn hF).continuousAt hpositive.2
      (fun y hy => hmax y s hy hs)
  have htimemax : IsLocalMaxOn (fun r => η q * bernsteinAuxiliary g v τ q r)
      (Set.Iic s) s := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hspos), self_mem_nhdsWithin]
      with r hr hrle
    have hrt : r ∈ Set.Icc 0 T := ⟨(show 0 < r from hr).le, (show r ≤ s from hrle).trans hs.2⟩
    have hh := hmax q r hq hrt
    rwa [← hηvalue] at hh
  have hdt := ((bernsteinAuxiliary_time_hasDerivAt g hv.1 τ q htime).differentiableAt.hasDerivAt).const_mul (η q)
  have hdtpos := hasDerivAt_nonneg_at_left_max hdt htimemax
  have hd : 0 ≤ deriv (bernsteinAuxiliary g v τ q) s :=
    nonneg_of_mul_nonneg_right hdtpos hηpos
  have hunit : v q (τ+s) ^ 2 ≤ 1 := by
    have hupp := hbound q s hq hs
    have hpos := (hv.2 q (τ+s) htime).1
    nlinarith
  have henergy : s * gradNormSq g.form (fun z => v z (τ+s)) q ≤
      bernsteinAuxiliary g v τ q s :=
    mul_le_mul_of_nonneg_left (gradNormSq_le_bernsteinEnergy g hv.1 q htime) hspos.le
  have hmaximum := bernstein_bound_at_positive_maximum g hK
    (positiveHeatSolution_slice g.form hv htime) hF q hβ hspos hR hηC2
    hηpos hηone hpositive.2 hd hunit henergy hspace hηgrad hηlap
    (bernsteinAuxiliary_drift g hK hRic hv hτ.le hspos q hunit)
  have hcenter' : bernsteinAuxiliary g v τ x T ≤ η q * bernsteinAuxiliary g v τ q s := by
    simpa only [hηvalue] using hcenter
  have hmono : (2 / bernsteinBeta) *
      (1 + (8 * (n : ℝ) + 16 + 4 / bernsteinBeta) * s / R ^ 2) ≤
      (2 / bernsteinBeta) *
      (1 + (8 * (n : ℝ) + 16 + 4 / bernsteinBeta) * T / R ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hm : (8 * (n : ℝ) + 16 + 4 / bernsteinBeta) * s / R ^ 2 ≤
        (8 * (n : ℝ) + 16 + 4 / bernsteinBeta) * T / R ^ 2 := by
      convert mul_le_mul_of_nonneg_right hs.2 hC using 1 <;> ring
    linarith only [hm]
  exact hcenter'.trans (hmaximum.trans hmono)

theorem positiveHeatSolution_local_gradient_sq_bound
    (g : SmoothMetric M) (hK : IsKahler g)
    (hRic : ∀ z, (ricci g.form z).PosSemidef)
    {u : M.Carrier → ℝ → ℝ} (hu : LeafCandidates.PositiveHeatSolution g.form u)
    (x : M.Carrier) {τ T R A : ℝ}
    (hτ : 0 < τ) (hT : 0 < T) (hR : 0 < R) (hA : 0 < A)
    (hbound : ∀ z s, inducedDistance g.form x z ≤ R →
      s ∈ Set.Icc 0 T → u z (τ+s) ≤ A) :
    gradNormSq g.form (fun z => u z (τ+T)) x ≤
      8 * bernsteinE * A ^ 2 *
        (1 / T + (8 * (n : ℝ) + 16 + 16 * bernsteinE) / R ^ 2) := by
  let v : M.Carrier → ℝ → ℝ := fun z s => u z s / A
  have hv : LeafCandidates.PositiveHeatSolution g.form v := positiveHeatSolution_div_pos g.form hu hA
  have hvbound : ∀ z s, inducedDistance g.form x z ≤ R →
      s ∈ Set.Icc 0 T → v z (τ+s) ≤ 1 := by
    intro z s hz hs
    exact (div_le_one hA).mpr (hbound z s hz hs)
  have hh := bernsteinAuxiliary_cylinder_bound g hK hRic hv x hτ hT hR hvbound
  have ht : 0 < τ + T := add_pos hτ hT
  have he := mul_le_mul_of_nonneg_left (gradNormSq_le_bernsteinEnergy g hv.1 x ht) hT.le
  have hq : gradNormSq g.form (fun z => v z (τ+T)) x ≤
      ((2 / bernsteinBeta) *
        (1 + (8 * (n : ℝ) + 16 + 4 / bernsteinBeta) * T / R ^ 2)) / T := by
    apply (le_div_iff₀ hT).mpr
    calc
      _ = T * gradNormSq g.form (fun z => v z (τ+T)) x := by ring
      _ ≤ bernsteinAuxiliary g v τ x T := he
      _ ≤ _ := hh
  have hβ2 : 2 / bernsteinBeta = 8 * bernsteinE := by
    unfold bernsteinBeta
    field_simp
    ring
  have hβ4 : 4 / bernsteinBeta = 16 * bernsteinE := by
    unfold bernsteinBeta
    field_simp
    ring
  rw [hβ2, hβ4] at hq
  have hq' : gradNormSq g.form (fun z => v z (τ+T)) x ≤
      8 * bernsteinE * (1 / T + (8 * (n : ℝ) + 16 + 16 * bernsteinE) / R ^ 2) := by
    convert hq using 1
    field_simp
  have hscale := gradNormSq_div_const g.form (positiveHeatSolution_slice g.form hu ht) A x
  change gradNormSq g.form (fun z => v z (τ+T)) x =
    gradNormSq g.form (fun z => u z (τ+T)) x / A ^ 2 at hscale
  rw [hscale] at hq'
  have hfinal := (div_le_iff₀ (sq_pos_of_pos hA)).mp hq'
  convert hfinal using 1
  ring

theorem localGradientConstant_pos (n : ℕ) : 0 < localGradientConstant n := by
  have hE := bernsteinE_pos
  unfold localGradientConstant
  positivity

theorem positiveHeatSolution_gradient_at_sqrt_scale
    (g : SmoothMetric M) (hK : IsKahler g)
    (hRic : ∀ z, (ricci g.form z).PosSemidef)
    {u : M.Carrier → ℝ → ℝ} (hu : LeafCandidates.PositiveHeatSolution g.form u)
    (x : M.Carrier) {t A : ℝ} (ht : 0 < t) (hA : 0 < A)
    (hbound : ∀ z s, inducedDistance g.form x z ≤ Real.sqrt t →
      s ∈ Set.Icc (t / 2) t → u z s ≤ A) :
    Real.sqrt (gradNormSq g.form (fun z => u z t) x) ≤
      localGradientConstant n * A / Real.sqrt t := by
  have hhalf : 0 < t / 2 := by positivity
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hKpos := localGradientConstant_pos n
  have hE := bernsteinE_pos
  have hb : ∀ z s, inducedDistance g.form x z ≤ Real.sqrt t →
      s ∈ Set.Icc 0 (t / 2) → u z (t / 2 + s) ≤ A := by
    intro z s hz hs
    apply hbound z (t/2+s) hz
    constructor <;> linarith [hs.1, hs.2]
  have hh := positiveHeatSolution_local_gradient_sq_bound g hK hRic hu x
    hhalf hhalf hsqrt hA hb
  rw [show t/2+t/2=t by ring, Real.sq_sqrt ht.le] at hh
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  convert hh using 1
  rw [div_pow, mul_pow, Real.sq_sqrt ht.le]
  unfold localGradientConstant
  rw [Real.sq_sqrt (by positivity)]
  field_simp
  ring

end Yau.LeafProofs.L24Aux
