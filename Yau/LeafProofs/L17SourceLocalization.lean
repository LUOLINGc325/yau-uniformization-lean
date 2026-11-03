import Yau.LeafProofs.L17SourceLocalizationRescaled

/-! Actual whole-space forcing localization for the original geometric
partition. The cutoff Holder elements are constructed from the proved BG
partition budget; no cutoff or source membership is an input to this result. -/

open Set Metric
noncomputable section
namespace Yau.LeafProofs.L17SourceLocalizationAux
open L17Aux L17HolderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem rescaledSource_tsupport_slice (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (f : HolderSpace P T γ) (p : P.centers) (τ : ℝ) :
    tsupport (fun z => rescaledSource P T hT f p (z,τ)) ⊆ closedBall (0 : ComplexVector n) (1 / 2 : ℝ) := by
  apply closure_minimal ?_ isClosed_closedBall
  intro z hz
  by_contra hn
  have hScaled : P.radius • z ∉ closedBall (0 : ComplexVector n) (P.radius / 2) := by
    intro hh
    have hNorm : P.radius * ‖z‖ ≤ P.radius / 2 := by
      simpa only [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos P.radius_pos] using hh
    have hHalf : ‖z‖ ≤ (1 / 2 : ℝ) := by nlinarith [P.radius_pos]
    exact hn (by simpa only [mem_closedBall, dist_zero_right] using hHalf)
  exact hz (localizedSource_eq_zero_outside_half P T hT f p _ _ hScaled)

theorem rescaledSource_formula (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (f : HolderSpace P T γ) (p : P.centers) {z : ComplexVector n} {τ : ℝ}
    (hz : z ∈ ball (0 : ComplexVector n) 1) (hτ : P.radius ^ 2 * τ ∈ Icc (0 : ℝ) T) :
    rescaledSource P T hT f p (z,τ) = P.weight p (P.charts.chart p (P.radius • z)) *
      holderFun f (P.charts.chart p (P.radius • z),⟨P.radius ^ 2 * τ,hτ⟩) := by
  have hNorm : ‖z‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hz
  have hScaled : P.radius • z ∈ ball (0 : ComplexVector n) P.radius := by
    simpa only [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos P.radius_pos, mul_one]
      using mul_lt_mul_of_pos_left hNorm P.radius_pos
  exact localizedSource_formula P T hT f p hScaled hτ

theorem parabolicHolderBound_mono {γ C D : ℝ} {f : Yau.Parabolic.Point n → ℝ}
    (hf : Yau.Parabolic.HolderBound γ Set.univ f C) (hCD : C ≤ D) :
    Yau.Parabolic.HolderBound γ Set.univ f D := by
  refine ⟨hf.1.trans hCD, fun q hq => (hf.2.1 q hq).trans hCD, ?_⟩
  intro q hq r hr
  have hw : 0 ≤ Yau.Parabolic.holderWeight γ q r :=
    add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (abs_nonneg _) _)
  exact (hf.2.2 q hq r hr).trans (mul_le_mul_of_nonneg_right hCD hw)

theorem BoundedChartFamily.exists_uniform_source_localization
    (A : BoundedChartFamily g) (hg : MetricSmooth g) :
    ∃ N : ℕ, ∃ B : ℕ → ℝ, ∃ C : ℝ, (∀ k, 0 < B k) ∧ 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ∃ P : UniformChartPartition g,
        P.charts = A ∧ P.radius < ε ∧ P.radius ≤ 1 ∧ 2 * P.radius < A.radius ∧
        P.overlapBudget = N ∧
        (∀ k (p : P.centers) q z, z ∈ ball (0 : ComplexVector n) (2 * P.radius) →
          ‖iteratedFDeriv ℝ k (fun w => P.weight p (P.charts.chart q w)) z‖ ≤ B k * (P.radius⁻¹) ^ k ∧
          ‖iteratedFDeriv ℝ k (fun w => P.localization p (P.charts.chart q w)) z‖ ≤ B k * (P.radius⁻¹) ^ k) ∧
        ∀ (T : ℝ) (hT : 0 < T), T ≤ P.radius ^ 2 → ∀ γ : ℝ, 0 < γ → γ ≤ 1 →
          ∀ (f : HolderSpace P T γ) (p : P.centers),
            Continuous (localizedSource P T hT.le f p) ∧
            (∀ τ, tsupport (fun z => localizedSource P T hT.le f p (z,τ)) ⊆ closedBall 0 (P.radius / 2)) ∧
            (∀ q, |localizedSource P T hT.le f p q| ≤ C * ‖f‖) ∧
            (∀ q r, |localizedSource P T hT.le f p r - localizedSource P T hT.le f p q| ≤
              C * ‖f‖ * (Yau.Parabolic.parabolicDistance q r / P.radius) ^ γ) ∧
            Continuous (rescaledSource P T hT.le f p) ∧
            (∀ τ, tsupport (fun z => rescaledSource P T hT.le f p (z,τ)) ⊆ closedBall 0 (1 / 2 : ℝ)) ∧
            (∀ q, |rescaledSource P T hT.le f p q| ≤ C * ‖f‖) ∧
            (∀ q r, |rescaledSource P T hT.le f p r - rescaledSource P T hT.le f p q| ≤
              C * ‖f‖ * Yau.Parabolic.parabolicDistance q r ^ γ) ∧
            Yau.Parabolic.HolderBound γ Set.univ (rescaledSource P T hT.le f p) (C * ‖f‖) := by
  obtain ⟨N, B, K, hB, hK, hPart⟩ := L17HolderAux.BoundedChartFamily.exists_uniform_partition_holder_budget A hg
  let C : ℝ := 8 * K + 4
  have hC : 0 < C := by dsimp [C]; positivity
  have hCOne : 1 ≤ C := by dsimp [C]; linarith
  refine ⟨N, B, C, hB, hC, ?_⟩
  intro ε hε
  obtain ⟨P, hA, hρε, hρ1, hρA, hN, hJets, hCutoffs⟩ := hPart ε hε
  refine ⟨P, hA, hρε, hρ1, hρA, hN, hJets, ?_⟩
  intro T hT hTR γ hγ hγ1 f p
  obtain ⟨η, χ, hη, hχ, hηK, hχK⟩ := hCutoffs T γ hTR hγ.le hγ1 p
  have hPowOne : (1 : ℝ) ≤ 2 ^ γ := Real.one_le_rpow (by norm_num) hγ.le
  have hPowTwo : (2 : ℝ) ^ γ ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hγ1
  have hPowSquare : ((2 : ℝ) ^ γ) ^ 2 ≤ 4 := by nlinarith
  have hUnit : sourceHolderConstant K γ * (2 : ℝ) ^ γ ≤ C := by
    calc
      _ = (2 * K + 1) * ((2 : ℝ) ^ γ) ^ 2 := by unfold sourceHolderConstant; ring
      _ ≤ (2 * K + 1) * 4 := mul_le_mul_of_nonneg_left hPowSquare (by positivity)
      _ = C := by dsimp [C]; ring
  have hRaw : sourceHolderConstant K γ ≤ C := by
    have hh : sourceHolderConstant K γ ≤ sourceHolderConstant K γ * (2 : ℝ) ^ γ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hPowOne (sourceHolderConstant_bounds hK.le hγ.le).1
    exact hh.trans hUnit
  have hScale : sourceHolderConstant K γ * ‖f‖ ≤ C * ‖f‖ :=
    mul_le_mul_of_nonneg_right hRaw (norm_nonneg f)
  have hSup : ‖f‖ ≤ C * ‖f‖ := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hCOne (norm_nonneg f)
  refine ⟨localizedSource_continuous P T hT.le f p, localizedSource_tsupport_slice P T hT.le f p,
    fun q => (localizedSource_abs_le_norm P T hT.le f p q).trans hSup, ?_,
    rescaledSource_continuous P T hT.le f p, rescaledSource_tsupport_slice P T hT.le f p,
    fun q => (rescaledSource_abs_le_norm P T hT.le f p q).trans hSup, ?_, ?_⟩
  · intro q r
    exact (localizedSource_global_difference P T hT.le hγ.le hK.le f η p hη hηK q r).trans
      (mul_le_mul_of_nonneg_right hScale (Real.rpow_nonneg
        (div_nonneg (add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) P.radius_pos.le) _))
  · intro q r
    exact (rescaledSource_difference P T hT.le hγ.le hK.le f η p hη hηK q r).trans
      (mul_le_mul_of_nonneg_right hScale (Real.rpow_nonneg
        (add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) _))
  · exact parabolicHolderBound_mono (rescaledSource_holderBound P T hT.le hγ.le hK.le f η p hη hηK)
      (mul_le_mul_of_nonneg_right hUnit (norm_nonneg f))

end Yau.LeafProofs.L17SourceLocalizationAux
