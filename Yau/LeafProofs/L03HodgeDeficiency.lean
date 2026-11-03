import Yau.LeafProofs.L03HodgeCaccioppoli

open MeasureTheory Filter
open scoped Topology InnerProductSpace

noncomputable section

namespace Yau.LeafProofs.L03

variable {n k : ℕ} {M : ComplexManifold n}

theorem hodge_deficiency_ae_zero_of_cutoffs
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A : RealForm M k) (hmax : OperatorCandidates.HodgeMaximalGraph g.form μ A (-A))
    (η : ℕ → M.Carrier → ℝ) (hη : ∀ j, SmoothFn (η j))
    (hcη : ∀ j, HasCompactSupport (η j))
    (hηrange : ∀ j y, η j y ∈ Set.Icc (0 : ℝ) 1)
    (htη : ∀ y, Tendsto (fun j => η j y) atTop (𝓝 1))
    (γ : ℕ → ℝ) (htγ : Tendsto γ atTop (𝓝 0))
    (hgrad : ∀ j y, L18Aux.scalarGradientPair g.form (η j) (η j) y ≤ γ j ^ 2) :
    ∀ᵐ y ∂μ, A y = 0 := by
  have hA := hmax.1
  let S := fun j => multiplyRealForm (η j) A
  have hS (j : ℕ) : L2RealForm g.form μ (S j) :=
    l2RealForm_multiply_smooth_compact g μ (η j) (hη j) (hcη j) A hA
  have htS := multiplyRealForm_l2_distance_tendsto g μ A hA η hη hηrange htη
  have hSt : Tendsto (fun j => ∫ y, formNormSq g.form (S j) y ∂μ) atTop
      (𝓝 (∫ y, formNormSq g.form A y ∂μ)) := by
    simpa only [one_mul] using integral_weighted_formNormSq_tendsto g μ S A hS hA htS
      (fun _ => 1) aestronglyMeasurable_const 1 zero_le_one (fun _ => by norm_num)
  have hb (j : ℕ) : (∫ y, formNormSq g.form (S j) y ∂μ) ≤
      γ j ^ 2 * (∫ y, formNormSq g.form A y ∂μ) := by
    let w := L18Aux.scalarGradientPair g.form (η j) (η j)
    have hwm := (L18Aux.continuous_of_smoothFn (L18Aux.smoothFn_scalarGradientPair g (hη j) (hη j))).aestronglyMeasurable (μ := μ)
    have hw : ∀ y, |w y| ≤ γ j ^ 2 := fun y => by
      rw [abs_of_nonneg (L18Aux.scalarGradientPair_self_nonneg g.form (η j) y)]
      exact hgrad j y
    have hWA := l2RealForm_multiply_bounded g μ w hwm (γ j ^ 2) (sq_nonneg _) hw A hA
    have hi : Integrable (fun y => w y * formNormSq g.form A y) μ := by
      have hh := formInner_integrable g μ (multiplyRealForm w A) A hWA hA
      exact hh.congr (Eventually.of_forall fun y => multiplyRealForm_inner_left g.form w A A y)
    apply (hodge_deficiency_cutoff_energy_le g μ hμ A hmax (η j) (hη j) (hcη j)).trans
    have hm := integral_mono hi ((formNormSq_integrable g μ A hA).const_mul (γ j ^ 2))
      (fun y => mul_le_mul_of_nonneg_right (hgrad j y) (formNormSq_nonneg g.form A y))
    simpa only [integral_const_mul] using hm
  have htbound : Tendsto (fun j => γ j ^ 2 * (∫ y, formNormSq g.form A y ∂μ)) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : 2 ≠ 0), zero_mul] using
      (htγ.pow 2).mul_const (∫ y, formNormSq g.form A y ∂μ)
  have hzero : Tendsto (fun j => ∫ y, formNormSq g.form (S j) y ∂μ) atTop (𝓝 0) :=
    squeeze_zero (fun j => integral_nonneg fun y => formNormSq_nonneg g.form (S j) y) hb htbound
  exact (integral_formNormSq_eq_zero_iff_ae g μ A hA).mp (tendsto_nhds_unique hSt hzero)

/-- Uniqueness for the actual original raw negative Hodge deficiency
equation. All local regularization and global cutoff hypotheses are
constructed internally. -/
theorem hodgeMaximalGraph_neg_self_ae_zero
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A : RealForm M k) (hmax : OperatorCandidates.HodgeMaximalGraph g.form μ A (-A)) :
    ∀ᵐ y ∂μ, A y = 0 := by
  classical
  cases isEmpty_or_nonempty M.Carrier with
  | inl hEmpty =>
      haveI := hEmpty
      exact Eventually.of_forall fun y => isEmptyElim y
  | inr hNonempty =>
      let x : M.Carrier := Classical.choice hNonempty
      obtain ⟨C, hC, hCut⟩ := L18Aux.exists_uniform_scalar_energy_cutoffs n
      have h (j : ℕ) := hCut M g x ((j : ℝ) + 1) (by positivity)
      choose η hη using h
      have htη (y : M.Carrier) : Tendsto (fun j => η j y) atTop (𝓝 1) := by
        obtain ⟨N, hN⟩ := exists_nat_gt (inducedDistance g.form x y)
        have heq : (fun j => η j y) =ᶠ[atTop] (fun _ => (1 : ℝ)) := by
          filter_upwards [eventually_ge_atTop N] with j hj
          apply (hη j).2.2.2.2.1 y
          have hcast : (N : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
          linarith
        exact (tendsto_congr' heq).mpr tendsto_const_nhds
      apply hodge_deficiency_ae_zero_of_cutoffs g μ hμ A hmax η
        (fun j => (hη j).2.1) (fun j => (hη j).2.2.1) (fun j => (hη j).2.2.2.1) htη
        (fun j => C / ((j : ℝ) + 1))
      · exact tendsto_const_nhds.div_atTop
          (Filter.tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ)))
      · intro j y
        exact (hη j).2.2.2.2.2.2 y

end Yau.LeafProofs.L03
