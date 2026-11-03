import Yau.LeafProofs.L19LocalizationCalculus

/-! The Li--Yau estimate obtained from the actual compact-cylinder
maximum argument and the genuine distance-square upper supports. -/

noncomputable section
open Filter
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.LeafProofs.L19Aux
open L12Aux L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem liYauAuxiliary_bound_of_CD (g : SmoothMetric M) (hn : 0 < n)
    (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef) (hCD : ComplexCD g)
    {u : M.Carrier → ℝ → ℝ} (hu : LeafCandidates.PositiveHeatSolution g.form u)
    {α τ T R : ℝ} (hα : 1 < α) (hτ : 0 < τ) (hT : 0 < T) (hR : 0 < R)
    (x : M.Carrier) :
    liYauAuxiliary g.form u α τ x T ≤ (n : ℝ) * α ^ 2 *
      (1 + T * (8 * (n : ℝ) + 16 + 4 * (n : ℝ) * α ^ 2 / (α - 1)) / R ^ 2) := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hαpos : 0 < α := lt_trans zero_lt_one hα
  have hα1 : 0 < α - 1 := sub_pos.mpr hα
  have hC : 0 ≤ (8 * (n : ℝ) + 16 + 4 * (n : ℝ) * α ^ 2 / (α - 1)) / R ^ 2 := by
    positivity
  by_cases htarget : liYauAuxiliary g.form u α τ x T ≤ 0
  · exact htarget.trans (by positivity)
  have htargetpos : 0 < liYauAuxiliary g.form u α τ x T := lt_of_not_ge htarget
  obtain ⟨q, s, hq, hs, hmax⟩ := exists_liYauAuxiliary_cylinder_maximum g hu α hτ hR hT x
  have hxx : inducedDistance g.form x x ≤ R := by
    rw [show inducedDistance g.form x x = 0 from g.induced_distance_eq_zero.mpr rfl]
    exact hR.le
  have hcenter := hmax x T hxx ⟨hT.le, le_rfl⟩
  rw [distanceCutoff_center, one_mul] at hcenter
  have hmaxpos : 0 < distanceCutoff g x R q * liYauAuxiliary g.form u α τ q s :=
    htargetpos.trans_le hcenter
  have hpositive : 0 < distanceCutoff g x R q ∧ 0 < liYauAuxiliary g.form u α τ q s := by
    rcases mul_pos_iff.mp hmaxpos with hh | hh
    · exact hh
    · exact False.elim ((not_lt_of_ge (distanceCutoff_nonneg g x R q)) hh.1)
  have hqinside : inducedDistance g.form x q < R :=
    (distanceCutoff_pos_iff g x q hR).mp hpositive.1
  have hspos : 0 < s := by
    by_contra h
    have hs0 : s = 0 := le_antisymm (le_of_not_gt h) hs.1
    simpa [liYauAuxiliary, hs0] using hpositive.2
  have htime : 0 < τ + s := add_pos hτ hspos
  obtain ⟨η, hηC2, hηvalue, hηnear, hηpos, hηone, hηgrad, hηlap⟩ :=
    exists_distanceCutoff_lower_support_chart g hK hRic x q hR hqinside
  have hF : SmoothFn (fun y => liYauAuxiliary g.form u α τ y s) :=
    liYauAuxiliary_slice g hu α τ s htime
  have hspace : IsLocalMax (fun z => inChart q η z *
      inChart q (fun y => liYauAuxiliary g.form u α τ y s) z) (chartPt q q) :=
    lower_support_preserves_space_max g x q hqinside hηvalue hηnear
      (continuous_of_smoothFn hF).continuousAt hpositive.2
      (fun y hy => hmax y s hy hs)
  have htimemax : IsLocalMaxOn (fun r => η q * liYauAuxiliary g.form u α τ q r)
      (Set.Iic s) s := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hspos), self_mem_nhdsWithin]
      with r hr hrle
    have hrt : r ∈ Set.Icc 0 T := ⟨(show 0 < r from hr).le, (show r ≤ s from hrle).trans hs.2⟩
    have hh := hmax q r hq hrt
    rwa [← hηvalue] at hh
  have hdt := ((liYauAuxiliary_time_contDiffAt g hu α τ q htime).differentiableAt
    (by simp)).hasDerivAt.const_mul (η q)
  have hdtpos := hasDerivAt_nonneg_at_left_max hdt htimemax
  have hd : 0 ≤ deriv (liYauAuxiliary g.form u α τ q) s := by
    exact nonneg_of_mul_nonneg_right hdtpos hηpos
  have hf := positiveHeatSolution_log_slice g.form hu htime
  have hbound := liYau_bound_at_positive_maximum g hK hn hf hF q hα hspos hR
    hηC2 hηpos hηone hpositive.2 hd hspace hηgrad hηlap
    (liYauAuxiliary_drift_of_CD g hn hCD hu hα hτ.le hspos q)
  have hcenter' : liYauAuxiliary g.form u α τ x T ≤ η q * liYauAuxiliary g.form u α τ q s := by
    simpa only [hηvalue] using hcenter
  have hmonotone : (n : ℝ) * α ^ 2 *
      (1 + s * (8 * (n : ℝ) + 16 + 4 * (n : ℝ) * α ^ 2 / (α - 1)) / R ^ 2) ≤
      (n : ℝ) * α ^ 2 *
      (1 + T * (8 * (n : ℝ) + 16 + 4 * (n : ℝ) * α ^ 2 / (α - 1)) / R ^ 2) := by
    have hh := mul_le_mul_of_nonneg_right hs.2 hC
    have hh' := mul_le_mul_of_nonneg_left hh (mul_nonneg hnR.le (sq_nonneg α))
    convert add_le_add_left hh' ((n : ℝ) * α ^ 2) using 1 <;> ring
  exact hcenter'.trans (hbound.trans hmonotone)

/-- The strict-coefficient local Li--Yau estimate, with no growth or
support hypothesis on the positive heat solution. -/
theorem liYau_local_alpha_of_CD (g : SmoothMetric M) (hn : 0 < n)
    (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef) (hCD : ComplexCD g)
    {u : M.Carrier → ℝ → ℝ} (hu : LeafCandidates.PositiveHeatSolution g.form u)
    {α τ t R : ℝ} (hα : 1 < α) (hτ : 0 < τ) (hτt : τ < t) (hR : 0 < R)
    (x : M.Carrier) :
    gradNormSq g.form (fun y => Real.log (u y t)) x -
      α * deriv (fun s => Real.log (u x s)) t ≤
      (n : ℝ) * α ^ 2 / (t - τ) + (n : ℝ) * α ^ 2 *
        (8 * (n : ℝ) + 16 + 4 * (n : ℝ) * α ^ 2 / (α - 1)) / R ^ 2 := by
  have hT : 0 < t - τ := sub_pos.mpr hτt
  have hh := liYauAuxiliary_bound_of_CD g hn hK hRic hCD hu hα hτ hT hR x
  have ht : τ + (t - τ) = t := by ring
  simp only [liYauAuxiliary, ht] at hh
  have hrhs : (n : ℝ) * α ^ 2 / (t - τ) + (n : ℝ) * α ^ 2 *
      (8 * (n : ℝ) + 16 + 4 * (n : ℝ) * α ^ 2 / (α - 1)) / R ^ 2 =
      ((n : ℝ) * α ^ 2 * (1 + (t - τ) *
        (8 * (n : ℝ) + 16 + 4 * (n : ℝ) * α ^ 2 / (α - 1)) / R ^ 2)) / (t - τ) := by
    field_simp
    <;> ring
  rw [hrhs]
  apply (le_div_iff₀ hT).mpr
  convert hh using 1 <;> ring

/-- Removing all three localizations gives the original sharp per-point
complex Li--Yau differential estimate. -/
theorem liYau_at_point_of_CD (g : SmoothMetric M) (hn : 0 < n)
    (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef) (hCD : ComplexCD g)
    {u : M.Carrier → ℝ → ℝ} (hu : LeafCandidates.PositiveHeatSolution g.form u)
    (x : M.Carrier) {t : ℝ} (ht : 0 < t) :
    gradNormSq g.form (fun y => Real.log (u y t)) x -
      deriv (fun s => Real.log (u x s)) t ≤ (n : ℝ) / t := by
  apply liYau_remove_localizations ht
  intro α hα τ hτ hτt
  refine ⟨(n : ℝ) * α ^ 2 * (8 * (n : ℝ) + 16 + 4 * (n : ℝ) * α ^ 2 / (α - 1)), ?_⟩
  intro R hR
  exact liYau_local_alpha_of_CD g hn hK hRic hCD hu hα hτ hτt hR x

end Yau.LeafProofs.L19Aux
