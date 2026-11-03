import Yau.Proofs.D02Fields

/-! A uniform fibre coercivity constant from the actual spanning fields.
The dual norm is squared throughout. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n m : ℕ} {M : ComplexManifold n}

theorem dualNorm_continuousOn_chart (g : HermitianField M) (hg : MetricSmooth g)
    (x : M.Carrier) :
    ContinuousOn (fun p : CotangentCoord n =>
      dualNorm g (cotangentChartInv x p).1 (cotangentChartInv x p).2) (cotangentTarget x) := by
  exact (dualNormChart_contDiffOn_of_metricSmooth g hg x).continuousOn.congr
    fun p hp => dualNorm_cotangentChartInv g x hp

theorem cotangentUnitSphere_compact (g : HermitianField M) (hg : MetricSmooth g)
    {K : Set M.Carrier} (hK : IsCompact K) :
    CotangentCompact {y : CotangentPoint M | y.1 ∈ K ∧ dualNorm g y.1 y.2 = 1} := by
  have h := cotangentCompact_inter_preimage (cotangentBoxCompact n M g hg K 1 hK)
    (F := fun y => dualNorm g y.1 y.2) (dualNorm_continuousOn_chart g hg)
    (S := {(1 : ℝ)}) isClosed_singleton
  convert h using 1
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
    InCotangentCompact]
  constructor
  · rintro ⟨hy, hq⟩
    exact ⟨⟨hy, hq.le⟩, hq⟩
  · rintro ⟨⟨hy, _⟩, hq⟩
    exact ⟨hy, hq⟩

theorem dualNorm_smul (g : HermitianField M) (x : M.Carrier)
    (c : ℂ) (ξ : Covector n) :
    dualNorm g x (c • ξ) = ‖c‖ ^ 2 * dualNorm g x ξ := by
  have hc : covectorCoords x x (c • ξ) = c • covectorCoords x x ξ := by
    ext i
    rfl
  change dualNormMat (gMat g x) (covectorCoords x x (c • ξ)) = _
  rw [hc, dualNormMat_smul]
  rfl

theorem fieldEvaluationSq_smul (V : Fin m → VectorField M) (x : M.Carrier)
    (c : ℂ) (ξ : Covector n) :
    fieldEvaluationSq V (x, c • ξ) = ‖c‖ ^ 2 * fieldEvaluationSq V (x, ξ) := by
  change (∑ i, ‖c * ξ (V i x)‖ ^ 2) = ‖c‖ ^ 2 * ∑ i, ‖ξ (V i x)‖ ^ 2
  simp only [norm_mul, mul_pow, Finset.mul_sum]

theorem fieldEvaluationSq_nonneg (V : Fin m → VectorField M) (y : CotangentPoint M) :
    0 ≤ fieldEvaluationSq V y := Finset.sum_nonneg fun _i _ => sq_nonneg _

/-- One coercivity constant for all fibres over the one original compact base. -/
theorem fieldEvaluationSq_coercive (g : HermitianField M) (hg : MetricSmooth g)
    {K : Set M.Carrier} (hK : IsCompact K) {V : Fin m → VectorField M}
    (hV : ∀ i, IsHolomorphicField (V i))
    (hspan : ∀ x, Submodule.span ℂ (Set.range fun i => V i x) = ⊤) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ ξ : Covector n,
      c * dualNorm g x ξ ≤ fieldEvaluationSq V (x, ξ) := by
  obtain ⟨c, hc, hb⟩ := cotangentCompact_pos_lower_bound (cotangentUnitSphere_compact g hg hK)
    (fieldEvaluationSq_continuousOn_chart hV) (by
      intro y hy
      apply fieldEvaluationSq_pos hspan
      intro hzero
      have hq := (dualNorm_eq_zero_iff g y.1 y.2).mpr hzero
      rw [hy.2] at hq
      exact one_ne_zero hq)
  refine ⟨c, hc, fun x hx ξ => ?_⟩
  by_cases hξ : ξ = 0
  · rw [(dualNorm_eq_zero_iff g x ξ).mpr hξ, mul_zero]
    exact fieldEvaluationSq_nonneg V (x, ξ)
  have hq : 0 < dualNorm g x ξ :=
    lt_of_le_of_ne (dualNorm_nonneg g x ξ)
      (Ne.symm ((dualNorm_eq_zero_iff g x ξ).not.mpr hξ))
  let a : ℂ := ((Real.sqrt (dualNorm g x ξ))⁻¹ : ℝ)
  have ha : ‖a‖ ^ 2 = (dualNorm g x ξ)⁻¹ := by
    dsimp only [a]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr hq)), inv_pow, Real.sq_sqrt hq.le]
  have hunit : dualNorm g x (a • ξ) = 1 := by
    rw [dualNorm_smul, ha, inv_mul_cancel₀ hq.ne']
  have h := hb (x, a • ξ) ⟨hx, hunit⟩
  rw [fieldEvaluationSq_smul, ha] at h
  have hm := mul_le_mul_of_nonneg_right h hq.le
  have he : ((dualNorm g x ξ)⁻¹ * fieldEvaluationSq V (x, ξ)) * dualNorm g x ξ =
      fieldEvaluationSq V (x, ξ) := by field_simp [hq.ne']
  rwa [he] at hm

/-- A single evaluation bound gives a single squared dual-norm bound. -/
theorem dualNorm_le_of_fieldEvaluationSq_le (g : HermitianField M) (hg : MetricSmooth g)
    {K : Set M.Carrier} (hK : IsCompact K) {V : Fin m → VectorField M}
    (hV : ∀ i, IsHolomorphicField (V i))
    (hspan : ∀ x, Submodule.span ℂ (Set.range fun i => V i x) = ⊤) :
    ∃ c : ℝ, 0 < c ∧ ∀ B : ℝ, ∀ x ∈ K, ∀ ξ : Covector n,
      fieldEvaluationSq V (x, ξ) ≤ B → dualNorm g x ξ ≤ B / c := by
  obtain ⟨c, hc, hb⟩ := fieldEvaluationSq_coercive g hg hK hV hspan
  refine ⟨c, hc, fun B x hx ξ hB => ?_⟩
  exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using (hb x hx ξ).trans hB)

end Yau.NodeProofs.D02Aux
