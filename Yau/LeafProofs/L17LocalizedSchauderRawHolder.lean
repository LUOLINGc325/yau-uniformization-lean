import Yau.LeafProofs.L17LocalizedSchauderRawDifference
import Yau.LeafProofs.L17LocalizedSchauderPairScaling

open Set Metric
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17LocalizedSchauderAux
open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17HolderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

/-- Already supported local scalar functions are transported without an
additional cutoff. The constant precedes the scale and the local data. -/
theorem exists_uniform_raw_transport_holder_budget (A : BoundedChartFamily g) (hg : MetricSmooth g)
    (gamma : ℝ) (hγ : 0 ≤ gamma) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : UniformChartPartition g), P.charts = A →
      ∀ (hρone : P.radius ≤ 1), 2*P.radius < A.radius → ∀ (T a b : ℝ), 0 ≤ a → 0 ≤ b →
      ∀ (p : P.centers) (v : ComplexVector n × Time T → ℝ),
      (∀ z, z ∉ closedBall (0 : ComplexVector n) P.radius → ∀ t, v (z,t) = 0) →
      (∀ z ∈ ball (0 : ComplexVector n) (2*P.radius), ∀ t, |v (z,t)| ≤ a) →
      (∀ z w, z ∈ ball (0 : ComplexVector n) (2*P.radius) → w ∈ ball 0 (2*P.radius) →
        ∀ t s : Time T, |v (z,t)-v (w,s)| ≤ b*(localScaledDistance P.radius (z,t) (w,s))^gamma) →
      (∀ (q : M.Carrier) (t s : Time T) (z w : ComplexVector n), z ∈ ball 0 1 → w ∈ ball 0 1 →
        |rawLocalizedTerm P T p v (P.charts.chart q (P.radius • z),t)-
          rawLocalizedTerm P T p v (P.charts.chart q (P.radius • w),s)| ≤
          C*(a+b)*(unitParabolicDistance P.radius (z,t) (w,s))^gamma) ∧
      ∀ i : ChartPairs P T,
        |pairWeight P T gamma i*(rawLocalizedTerm P T p v (chartRight P T i)-
          rawLocalizedTerm P T p v (chartLeft P T i))| ≤ C*(a+b) := by
  obtain ⟨D,hD,hNorm,hDiff⟩ := exists_scaled_transition_pair_budget A 0
  let C := 1+max (D^gamma) (2*((nearCoverRadius A)⁻¹)^gamma)
  have hDpow : 0 ≤ D^gamma := Real.rpow_nonneg (zero_le_one.trans hD) _
  have hFar0 : 0 ≤ 2*((nearCoverRadius A)⁻¹)^gamma :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg (inv_nonneg.mpr (nearCoverRadius_pos A).le) _)
  have hC : 0 < C := by dsimp only [C]; linarith [le_max_left (D^gamma) (2*((nearCoverRadius A)⁻¹)^gamma)]
  refine ⟨C,hC,?_⟩
  intro P hPA hρone hρr T a b ha hb p v hZero hSup hHolder
  have hρr' : 2*P.radius < P.charts.radius := by rwa [hPA]
  have hTrans : TransitionJetBounds P.charts 0 D := by rw [hPA]; exact ⟨hNorm,hDiff⟩
  have hCoefNear : D^gamma*b ≤ C*(a+b) := by
    have hDC : D^gamma ≤ C := by dsimp only [C]; linarith [le_max_left (D^gamma) (2*((nearCoverRadius A)⁻¹)^gamma)]
    exact mul_le_mul hDC (le_add_of_nonneg_left ha) hb hC.le
  have hCoefFar : (2*((nearCoverRadius P.charts)⁻¹)^gamma)*a ≤ C*(a+b) := by
    have hFC : 2*((nearCoverRadius P.charts)⁻¹)^gamma ≤ C := by
      rw [hPA]; dsimp only [C]; linarith [le_max_right (D^gamma) (2*((nearCoverRadius A)⁻¹)^gamma)]
    exact mul_le_mul hFC (le_add_of_nonneg_right hb) ha hC.le
  have hPair (q : M.Carrier) (t s : Time T) (z w : ComplexVector n)
      (hz : z ∈ ball 0 1) (hw : w ∈ ball 0 1) :
      |rawLocalizedTerm P T p v (P.charts.chart q (P.radius • z),t)-
        rawLocalizedTerm P T p v (P.charts.chart q (P.radius • w),s)| ≤
        C*(a+b)*(unitParabolicDistance P.radius (z,t) (w,s))^gamma := by
    have hd := unitParabolicDistance_nonneg P.radius_pos (z,t) (w,s)
    have hPower : 0 ≤ (unitParabolicDistance P.radius (z,t) (w,s))^gamma := Real.rpow_nonneg hd _
    by_cases hNear : unitParabolicDistance P.radius (z,t) (w,s) < nearCoverRadius P.charts
    · have hLocal : |rawLocalizedTerm P T p v (P.charts.chart q (P.radius • z),t)-
          rawLocalizedTerm P T p v (P.charts.chart q (P.radius • w),s)| ≤
          D^gamma*b*(unitParabolicDistance P.radius (z,t) (w,s))^gamma := by
        by_cases hx : P.charts.chart q (P.radius • z) ∈ P.charts.chart p '' closedBall 0 P.radius
        · exact rawLocalizedTerm_near_left P hg hρone hρr' p q v hZero hb hD hγ hHolder hTrans t s hz hw hx hNear
        · by_cases hy : P.charts.chart q (P.radius • w) ∈ P.charts.chart p '' closedBall 0 P.radius
          · rw [abs_sub_comm,unitParabolicDistance_symm P.radius (z,t) (w,s)]
            exact rawLocalizedTerm_near_left P hg hρone hρr' p q v hZero hb hD hγ hHolder hTrans s t hw hz hy
              (by rwa [unitParabolicDistance_symm])
          · rw [rawLocalizedTerm_zero_of_not_cover P T p v _ hx,
              rawLocalizedTerm_zero_of_not_cover P T p v _ hy,sub_self,abs_zero]
            exact mul_nonneg (mul_nonneg hDpow hb) hPower
      exact hLocal.trans (mul_le_mul_of_nonneg_right hCoefNear hPower)
    · have hFar := norm_sub_le_far_power
        (a := rawLocalizedTerm P T p v (P.charts.chart q (P.radius • z),t))
        (b := rawLocalizedTerm P T p v (P.charts.chart q (P.radius • w),s))
        ha (nearCoverRadius_pos P.charts) (le_of_not_gt hNear) hγ
        (by simpa only [Real.norm_eq_abs] using rawLocalizedTerm_abs_le P T p v ha hSup (P.charts.chart q (P.radius • z),t))
        (by simpa only [Real.norm_eq_abs] using rawLocalizedTerm_abs_le P T p v ha hSup (P.charts.chart q (P.radius • w),s))
      have hFar' : |rawLocalizedTerm P T p v (P.charts.chart q (P.radius • z),t)-
          rawLocalizedTerm P T p v (P.charts.chart q (P.radius • w),s)| ≤
          ((2*((nearCoverRadius P.charts)⁻¹)^gamma)*a)*(unitParabolicDistance P.radius (z,t) (w,s))^gamma := by
        simpa only [Real.norm_eq_abs,mul_assoc,mul_left_comm,mul_comm] using hFar
      exact hFar'.trans (mul_le_mul_of_nonneg_right hCoefFar hPower)
  refine ⟨hPair,?_⟩
  intro i
  have hh := hPair i.1 i.2.val.1.2 i.2.val.2.2
    (P.radius⁻¹ • (i.2.val.1.1 : ComplexVector n)) (P.radius⁻¹ • (i.2.val.2.1 : ComplexVector n))
    (inv_radius_smul_mem_unit_ball P i.2.val.1.1.property)
    (inv_radius_smul_mem_unit_ball P i.2.val.2.1.property)
  simp only [smul_smul,mul_inv_cancel₀ P.radius_pos.ne',one_smul] at hh
  rw [unitParabolicDistance_inv_radius P i.2.val.1 i.2.val.2,abs_sub_comm] at hh
  have hWeighted := norm_weighted_pair_le P T gamma i
    (rawLocalizedTerm P T p v (chartRight P T i)) (rawLocalizedTerm P T p v (chartLeft P T i))
    (by simpa only [Real.norm_eq_abs,chartRight,chartLeft,chartPoint] using hh)
  simpa only [Real.norm_eq_abs,smul_eq_mul] using hWeighted

end Yau.LeafProofs.L17LocalizedSchauderAux
