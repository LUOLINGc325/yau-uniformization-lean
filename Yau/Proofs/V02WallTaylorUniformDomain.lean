import Yau.Proofs.V02WallTaylorIncrementDomain

/-! A common parameter radius puts every compact independent datum inside
the genuine open smooth domain of the literal increments. -/

open scoped Topology ContDiff Manifold

noncomputable section
namespace Yau.Blueprint.V02WallTaylorProof
open Yau Yau.Blueprint V03Proof Metric

variable {n q b : ℕ} {X : KahlerManifold n}

theorem norm_scaled_chartFactorDirection_lt {m C R : ℝ} (hm : m ∈ Set.Icc 0 1)
    (hC : 0 ≤ C) {p : ℂ × ChartFactorAux n b}
    (hβ : ‖p.2.2.1‖ ≤ 1) (hc : ‖p.2.2.2‖ ≤ C)
    (hz : ‖p.1‖ < R / (2 * (C + 1))) :
    ‖m • chartFactorDirection p‖ < R / 2 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hm.1]
  have hd := norm_chartFactorDirection_le hC hβ hc
  have hmul := mul_le_mul hm.2 hd (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hz' := (lt_div_iff₀ (show 0 < 2 * (C + 1) by positivity)).mp hz
  nlinarith [norm_nonneg p.1]

theorem exists_uniform_chart_increment_domain {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ)
    {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold}
    (hzero : ∀ y, Ψ (y, 0) = y) (x : Pt X)
    {A : CotangentCoord n} {δ R C : ℝ} (hδ : 0 < δ) (hR : 0 < R) (hC : 0 ≤ C)
    (hvalid : Metric.ball A (2 * δ) ⊆ cotangentTarget x)
    (hΨ : ContDiffOn ℂ ∞ (sprayCoordinate Ψ x) (Metric.ball A (2 * δ) ×ˢ Metric.ball 0 R))
    (hsource : ∀ u ∈ Metric.closedBall A δ, ∀ τ ∈ Metric.closedBall 0 (R / 2),
      (Ψ (NativeCotangentPoint.mk (cotangentChartInv x u), τ)).val ∈ cotangentSource x) :
    ∃ r : ℝ, 0 < r ∧ r < R / (2 * (C + 1)) ∧
      ∀ z ∈ Metric.ball 0 r, ∀ u ∈ Metric.ball A δ,
      ∀ β ∈ Metric.closedBall (0 : ℂ) 1, ∀ c ∈ Metric.closedBall (0 : Fin b → ℂ) C,
      (z, (u, (β, c))) ∈ nativeIncrementDomain d j a Ψ x A δ R := by
  let m : CotangentCoord n → ℝ := fun u => wallPower d j a (cotangentChartInv x u)
  have hm : ContDiffOn ℝ ∞ m (Metric.ball A (2 * δ)) :=
    (wallPower_chart_contDiffOn hd j a x).mono hvalid
  have hmb : ∀ u ∈ Metric.closedBall A δ, m u ∈ Set.Icc 0 1 :=
    fun _ _ => wallPower_mem_Icc hd j a _
  obtain ⟨rb, hrb, hrbR, hb⟩ := exists_uniform_chartSprayFactor hzero x hδ hR hC hvalid hΨ hsource
    (B := fun y => deltaBase d j y.1) (deltaBase_chart_contDiffOn hd j x) hm hmb
  obtain ⟨rf, hrf, _, hf⟩ := exists_uniform_chartSprayFactor hzero x hδ hR hC hvalid hΨ hsource
    (B := deltaFiber d j) (deltaFiber_chart_contDiffOn hd j x) hm hmb
  refine ⟨min rb rf, lt_min hrb hrf, (min_le_left _ _).trans_lt hrbR, ?_⟩
  intro z hz u hu β hβ c hc
  have hB := hb z (Metric.ball_subset_ball (min_le_left _ _) hz) u
    (Metric.ball_subset_closedBall hu) β hβ c hc
  have hF := hf z (Metric.ball_subset_ball (min_le_right _ _) hz) u
    (Metric.ball_subset_closedBall hu) β hβ c hc
  have hz' : ‖z‖ < R / (2 * (C + 1)) :=
    (show ‖z‖ < min rb rf by simpa only [Metric.mem_ball, dist_zero_right] using hz).trans
      ((min_le_left _ _).trans_lt hrbR)
  have hβ' : ‖β‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hβ
  have hc' : ‖c‖ ≤ C := by simpa only [Metric.mem_closedBall, dist_zero_right] using hc
  have hτ := norm_scaled_chartFactorDirection_lt (n := n)
    (p := (z, (u, (β, c)))) (wallPower_mem_Icc hd j a (cotangentChartInv x u)) hC hβ' hc' hz'
  have hτ' : m u • chartFactorDirection (z, (u, (β, c))) ∈ Metric.closedBall (0 : Fin b → ℂ) (R / 2) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hτ.le
  exact ⟨mem_chartFactorDomain_of_time_bound hδ hR hsource (Metric.ball_subset_closedBall hu) hτ',
    hu, hτ, hB.1, hF.1⟩

end Yau.Blueprint.V02WallTaylorProof
