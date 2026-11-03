import Yau.Proofs.P06CutoffTailProjection
import Yau.Proofs.P06ScalarUniquenessVolume

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace ComplexOrder

namespace Yau.NodeProofs.P06Aux.CutoffTail
open Yau Yau.LeafProofs Yau.LeafProofs.L03 Davies
variable {n k : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem exists_pos_ball_contains_compact (g : SmoothMetric M) (o : M.Carrier)
    {K : Set M.Carrier} (hK : IsCompact K) :
    ∃ r : ℝ, 0 < r ∧ K ⊆ distBall g.form o r := by
  have hc : Continuous (fun x => inducedDistance g.form o x) :=
    L12Aux.continuous_inducedDistance g |>.comp (continuous_const.prodMk continuous_id)
  obtain ⟨b, hb⟩ := hK.bddAbove_image hc.continuousOn
  refine ⟨max 1 (b + 1), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro x hx
  apply (L12Aux.mem_distBall_iff g o x (lt_of_lt_of_le zero_lt_one (le_max_left _ _))).mpr
  have hxbound : inducedDistance g.form o x ≤ b := hb (Set.mem_image_of_mem _ hx)
  have hmax : b + 1 ≤ max 1 (b + 1) := le_max_right _ _
  linarith

theorem compactlySupported_indicator_eventually_self
    (g : SmoothMetric M) (μ : Measure M.Carrier) (o : M.Carrier)
    (A : RealForm M k) (hA : L2RealForm g.form μ A)
    (hcA : CompactlySupportedRealForm A) :
    ∀ᶠ N : ℕ in atTop,
      indicator g μ (distBall g.form o (radius N))
        (L12Aux.measurableSet_distBall g o (radius N)) (realizeActualForm g μ A hA) =
          realizeActualForm g μ A hA := by
  obtain ⟨r, hr, hsub⟩ := exists_pos_ball_contains_compact g o hcA
  filter_upwards [radius_tendsto.eventually (eventually_ge_atTop r)] with N hN
  apply indicator_realize_eq_self g μ _ _ A hA (Eventually.of_forall ?_)
  intro x hx
  by_contra hn
  have hxr := hsub (subset_closure hn)
  have hlt := (L12Aux.mem_distBall_iff g o x hr).mp hxr
  exact hx ((L12Aux.mem_distBall_iff g o x (radius_pos N)).mpr (hlt.trans_le hN))

/-- The annular input norm uses actual L12 polynomial volume growth.  It
has no dependence on the support radius of the full cutoff datum. -/
theorem indicator_realize_polynomial_bound
    (g : SmoothMetric M) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (o : M.Carrier) (A : RealForm M k) (hA : L2RealForm g.form μ A)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ x, formNormSq g.form A x ≤ B ^ 2)
    (r : ℝ) (hr : 1 ≤ r) :
    ‖indicator g μ (distBall g.form o r) (L12Aux.measurableSet_distBall g o r)
      (realizeActualForm g μ A hA)‖ ≤
        B * r ^ n * Real.sqrt (μ.real (distBall g.form o 1)) := by
  have hrpos : 0 < r := zero_lt_one.trans_le hr
  have hn := norm_setIntegral_le_of_norm_le_const (distBall_measure_lt_top g μ hμ o hrpos)
    (f := formNormSq g.form A) (C := B ^ 2) (fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg (formNormSq_nonneg g.form A x)]
      exact hb x)
  have hv := distBall_real_volume_polynomial g hK hRic μ hμ o hr
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity :
    0 ≤ B * r ^ n * Real.sqrt (μ.real (distBall g.form o 1)))).mp
  calc
    _ = ∫ x in distBall g.form o r, formNormSq g.form A x ∂μ :=
      indicator_realize_norm_sq g μ _ _ A hA
    _ ≤ B ^ 2 * μ.real (distBall g.form o r) := (le_abs_self _).trans hn
    _ ≤ B ^ 2 * (r ^ (2 * n) * μ.real (distBall g.form o 1)) :=
      mul_le_mul_of_nonneg_left hv (sq_nonneg _)
    _ = _ := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ μ.real (distBall g.form o 1))]
      rw [← pow_mul, Nat.mul_comm n 2]
      ring

end Yau.NodeProofs.P06Aux.CutoffTail
