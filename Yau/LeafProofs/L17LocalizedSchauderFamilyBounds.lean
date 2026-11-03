import Yau.LeafProofs.L17LocalizedSchauderFamilyData

open Set Metric
open scoped ContDiff
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17LocalizedSchauderAux
open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17HolderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

def nearCoverRadius (A : BoundedChartFamily g) : ℝ :=
  min 1 (Real.sqrt (2*(A.bound 0)⁻¹)/(2*Real.sqrt (2*A.bound 0)))

theorem nearCoverRadius_pos (A : BoundedChartFamily g) : 0 < nearCoverRadius A := by
  have h := A.bound_pos 0
  unfold nearCoverRadius
  positivity

theorem cutoffUnitFamily_norm_le (P : UniformChartPartition g) (hg : MetricSmooth g)
    (hρone : P.radius ≤ 1) (hρr : 2*P.radius < P.charts.radius)
    {T : ℝ} {k : ℕ} (hk : k ≤ 2) {C D F gamma : ℝ}
    (hC : 0 ≤ C) (hD : 1 ≤ D) (hF : 0 ≤ F) (hγ : 0 < gamma) (hγone : gamma ≤ 1)
    (f : P.centers → Time T → ComplexVector n → ℝ)
    (hf : UnitLocalJetData P T k gamma F f) (hCut : CutoffJetBounds P k C)
    (hTransition : TransitionJetBounds P.charts k D)
    (p : P.centers) (q : M.Carrier) (t : Time T) {z : ComplexVector n} (hz : z ∈ ball 0 1)
    (j : ℕ) (hj : j ≤ k) :
    ‖iteratedFDeriv ℝ j (cutoffUnitFamily P hρone f p q t) z‖ ≤ transportJetBudget k C D gamma*F := by
  by_cases hx : P.charts.chart q (P.radius • z) ∈ P.charts.chart p '' closedBall 0 P.radius
  · have hδ := (nearCoverRadius_pos P.charts).trans_le (min_le_right _ _)
    obtain ⟨hSegment,-⟩ := scaled_transition_segment_of_left_in_cover P hg hρone hρr p q hz hz hx
      (by simpa only [sub_self,norm_zero] using hδ)
    have hPair := cutoff_composition_pair_bounds P T hρone hρr p q k hk hC hD hF hγ hγone
      (f p) (hf.1 p) (hf.2.1 p) (hf.2.2 p) (hCut p q)
      ⟨fun a ha l hl => hTransition.1 _ a ha l hl,
        fun a b hab l hl => hTransition.2 _ a b hab l hl⟩ hz hz hSegment t t
      (by simp only [unitParabolicDistance,sub_self,norm_zero,abs_zero,Real.sqrt_zero,zero_div,add_zero]; norm_num)
    exact (hPair j hj).1
  · rw [cutoffUnitFamily_iteratedFDeriv_zero P hρone f p q t hz hx,norm_zero]
    exact mul_nonneg (transportJetBudget_pos k hC (zero_le_one.trans hD)).le hF

theorem cutoffUnitFamily_near_left (P : UniformChartPartition g) (hg : MetricSmooth g)
    (hρone : P.radius ≤ 1) (hρr : 2*P.radius < P.charts.radius)
    {T : ℝ} {k : ℕ} (hk : k ≤ 2) {C D F gamma : ℝ}
    (hC : 0 ≤ C) (hD : 1 ≤ D) (hF : 0 ≤ F) (hγ : 0 < gamma) (hγone : gamma ≤ 1)
    (f : P.centers → Time T → ComplexVector n → ℝ)
    (hf : UnitLocalJetData P T k gamma F f) (hCut : CutoffJetBounds P k C)
    (hTransition : TransitionJetBounds P.charts k D)
    (p : P.centers) (q : M.Carrier) (t s : Time T) {z w : ComplexVector n}
    (hz : z ∈ ball 0 1) (hw : w ∈ ball 0 1)
    (hx : P.charts.chart q (P.radius • z) ∈ P.charts.chart p '' closedBall 0 P.radius)
    (hNear : unitParabolicDistance P.radius (z,t) (w,s) < nearCoverRadius P.charts)
    (j : ℕ) (hj : j ≤ k) :
    ‖iteratedFDeriv ℝ j (cutoffUnitFamily P hρone f p q t) z-
      iteratedFDeriv ℝ j (cutoffUnitFamily P hρone f p q s) w‖ ≤
      transportJetBudget k C D gamma*F*(unitParabolicDistance P.radius (z,t) (w,s))^gamma := by
  have hSpace := unitParabolicDistance_space_le P.radius_pos (z,t) (w,s)
  obtain ⟨hSegment,-⟩ := scaled_transition_segment_of_left_in_cover P hg hρone hρr p q hz hw hx
    (by rw [norm_sub_rev]; exact hSpace.trans_lt (hNear.trans_le (min_le_right _ _)))
  have hPair := cutoff_composition_pair_bounds P T hρone hρr p q k hk hC hD hF hγ hγone
    (f p) (hf.1 p) (hf.2.1 p) (hf.2.2 p) (hCut p q)
    ⟨fun a ha l hl => hTransition.1 _ a ha l hl,
      fun a b hab l hl => hTransition.2 _ a b hab l hl⟩ hz hw hSegment t s
    (hNear.le.trans (min_le_left _ _))
  exact (hPair j hj).2

variable {E : Type*} [NormedAddCommGroup E]

theorem norm_sub_le_far_power {a b : E} {S d delta gamma : ℝ}
    (hS : 0 ≤ S) (hDelta : 0 < delta) (hFar : delta ≤ d) (hγ : 0 ≤ gamma)
    (ha : ‖a‖ ≤ S) (hb : ‖b‖ ≤ S) :
    ‖a-b‖ ≤ (2*S*(delta⁻¹)^gamma)*d^gamma := by
  have hd : 0 ≤ d := (hDelta.trans_le hFar).le
  have hone : 1 ≤ delta⁻¹*d := by
    rw [← div_eq_inv_mul]
    exact (one_le_div hDelta).mpr hFar
  have hPower := Real.one_le_rpow hone hγ
  rw [Real.mul_rpow (inv_nonneg.mpr hDelta.le) hd] at hPower
  calc
    _ ≤ 2*S := (norm_sub_le _ _).trans (by linarith)
    _ ≤ (2*S)*((delta⁻¹)^gamma*d^gamma) :=
      le_mul_of_one_le_right (mul_nonneg (by norm_num) hS) hPower
    _ = _ := by ring

def completeTransportJetBudget (A : BoundedChartFamily g) (k : ℕ) (C D gamma : ℝ) : ℝ :=
  max (transportJetBudget k C D gamma)
    (2*transportJetBudget k C D gamma*((nearCoverRadius A)⁻¹)^gamma)

theorem cutoffUnitFamily_sub_le (P : UniformChartPartition g) (hg : MetricSmooth g)
    (hρone : P.radius ≤ 1) (hρr : 2*P.radius < P.charts.radius)
    {T : ℝ} {k : ℕ} (hk : k ≤ 2) {C D F gamma : ℝ}
    (hC : 0 ≤ C) (hD : 1 ≤ D) (hF : 0 ≤ F) (hγ : 0 < gamma) (hγone : gamma ≤ 1)
    (f : P.centers → Time T → ComplexVector n → ℝ)
    (hf : UnitLocalJetData P T k gamma F f) (hCut : CutoffJetBounds P k C)
    (hTransition : TransitionJetBounds P.charts k D)
    (p : P.centers) (q : M.Carrier) (t s : Time T) {z w : ComplexVector n}
    (hz : z ∈ ball 0 1) (hw : w ∈ ball 0 1) (j : ℕ) (hj : j ≤ k) :
    ‖iteratedFDeriv ℝ j (cutoffUnitFamily P hρone f p q t) z-
      iteratedFDeriv ℝ j (cutoffUnitFamily P hρone f p q s) w‖ ≤
      completeTransportJetBudget P.charts k C D gamma*F*(unitParabolicDistance P.radius (z,t) (w,s))^gamma := by
  have hK : 0 ≤ transportJetBudget k C D gamma :=
    (transportJetBudget_pos k hC (zero_le_one.trans hD)).le
  have hd : 0 ≤ unitParabolicDistance P.radius (z,t) (w,s) :=
    unitParabolicDistance_nonneg P.radius_pos (z,t) (w,s)
  by_cases hNear : unitParabolicDistance P.radius (z,t) (w,s) < nearCoverRadius P.charts
  · have hh : ‖iteratedFDeriv ℝ j (cutoffUnitFamily P hρone f p q t) z-
        iteratedFDeriv ℝ j (cutoffUnitFamily P hρone f p q s) w‖ ≤
        transportJetBudget k C D gamma*F*(unitParabolicDistance P.radius (z,t) (w,s))^gamma := by
      by_cases hx : P.charts.chart q (P.radius • z) ∈ P.charts.chart p '' closedBall 0 P.radius
      · exact cutoffUnitFamily_near_left P hg hρone hρr hk hC hD hF hγ hγone f hf hCut hTransition p q t s hz hw hx hNear j hj
      · by_cases hy : P.charts.chart q (P.radius • w) ∈ P.charts.chart p '' closedBall 0 P.radius
        · rw [norm_sub_rev,unitParabolicDistance_symm P.radius (z,t) (w,s)]
          exact cutoffUnitFamily_near_left P hg hρone hρr hk hC hD hF hγ hγone f hf hCut hTransition p q s t hw hz hy
            (by rwa [unitParabolicDistance_symm]) j hj
        · rw [cutoffUnitFamily_iteratedFDeriv_zero P hρone f p q t hz hx,
            cutoffUnitFamily_iteratedFDeriv_zero P hρone f p q s hw hy,sub_self,norm_zero]
          exact mul_nonneg (mul_nonneg hK hF) (Real.rpow_nonneg hd _)
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hF) (Real.rpow_nonneg hd _))
  · have hh := norm_sub_le_far_power (mul_nonneg hK hF) (nearCoverRadius_pos P.charts)
      (le_of_not_gt hNear) hγ.le
      (cutoffUnitFamily_norm_le P hg hρone hρr hk hC hD hF hγ hγone f hf hCut hTransition p q t hz j hj)
      (cutoffUnitFamily_norm_le P hg hρone hρr hk hC hD hF hγ hγone f hf hCut hTransition p q s hw j hj)
    calc
      _ ≤ (2*(transportJetBudget k C D gamma*F)*((nearCoverRadius P.charts)⁻¹)^gamma)*
          (unitParabolicDistance P.radius (z,t) (w,s))^gamma := hh
      _ = (2*transportJetBudget k C D gamma*((nearCoverRadius P.charts)⁻¹)^gamma)*F*
          (unitParabolicDistance P.radius (z,t) (w,s))^gamma := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hF) (Real.rpow_nonneg hd _)

end Yau.LeafProofs.L17LocalizedSchauderAux
