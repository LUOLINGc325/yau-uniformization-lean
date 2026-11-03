import Yau.Proofs.F01AProperWeightLevi
import Yau.Proofs.F01ASmoothComparison
import Yau.Proofs.F01ACoreHeatIdentity
import Yau.Proofs.F01ExhaustionSquareLevi
import Yau.Proofs.F01MajorantComparisonQuadratic
import Yau.Proofs.F01ComparisonHeatIdentity

/-! A positive proper supercaloric barrier for the same actual flow and
potential pair. The half-epsilon comparison supplies its quadratic growth. -/
noncomputable section
open Set
open scoped Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.F01Aux
open Yau Yau.Blueprint
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false

theorem properSupercaloric_of_smooth_comparison
    (X : KahlerManifold n) (o : Pt X) (u : Pt X → ℝ)
    (hu : ControlledExhaustion X o u) (h : Flow X) (U P ρ : STF X)
    (hcore : LocalizedFlowCore X h U P ρ) {η : ℝ} (hη : 0 < η)
    (hcomparison : SmoothRicciWeightComparison X u U P η)
    (Ξ : Pt X → ℝ) (hΞ : SmoothFn Ξ)
    (hRic : ∀ x, HermLE (ricci X.metric.form x) (levi Ξ x))
    (hΞgrowth : ∃ c : ℝ, ∀ x,
      Ξ x ≤ c * (1 + distFrom X.metric.form o x ^ ((3 : ℝ) / 2))) :
    ProperSupercaloric X o h := by
  have hheat (T : ℝ) (hT : 0 < T) (x : Pt X) (t : ℝ) (ht : t ∈ Icc 0 T) :=
    localizedFlowCore_logdet_heat_identity hcore hT x ht
  rcases hcore with ⟨_, hU, hP, _, _, hpot, _, hUtime, _, _, hPtime⟩
  obtain ⟨K, hK, hcontrolled⟩ := hu.2.2.2
  obtain ⟨B, hB, hsquare⟩ := controlled_exhaustion_square_levi X o u hu
  obtain ⟨c₀, hgrowth₀⟩ := hΞgrowth
  let c := max c₀ 0
  have hc : 0 ≤ c := le_max_right _ _
  have hr (x : Pt X) : 0 ≤ distFrom X.metric.form o x :=
    X.metric.induced_distance_nonneg o x
  have hgrowth (x : Pt X) : Ξ x ≤ c * (1 + distFrom X.metric.form o x ^ ((3 : ℝ) / 2)) :=
    (hgrowth₀ x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (add_nonneg zero_le_one (Real.rpow_nonneg (hr x) _)))
  have hcompare (x : Pt X) : 1 + distFrom X.metric.form o x ≤ K * u x := by
    calc
      _ = K * (K⁻¹ * (1 + distFrom X.metric.form o x)) := by
        rw [← mul_assoc, mul_inv_cancel₀ hK.ne', one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hcontrolled x).1 hK.le
  have hweightSmooth (ε : ℝ) : SmoothFn (penalizedMajorantWeight Ξ u c K ε) :=
    fun a => ((hΞ a).sub (contDiffOn_const.mul ((hu.1 a).pow 2))).sub contDiffOn_const
  intro T hT
  let D := 2 * (T + 1)
  have hD : 0 < D := by dsimp only [D]; linarith
  obtain ⟨ε, hε, _, hhalfadm, hbudget⟩ := exists_proper_weight_parameter hD hB hη
  have hhalfpos : 0 < ε / 2 := by positivity
  have hsub : Icc (0 : ℝ) T ⊆ Ici 0 := fun _ ht => ht.1
  have hUcc : SmoothSpaceTime U (Icc 0 T) :=
    fun a => (hU a).mono (prod_mono Subset.rfl hsub)
  have hPcc : SmoothSpaceTime P (Icc 0 T) :=
    fun a => (hP a).mono (prod_mono Subset.rfl hsub)
  have hhalf (x : Pt X) (t : ℝ) (ht : t ∈ Icc 0 T) :
      0 ≤ comparisonFunction D n U P (penalizedMajorantWeight Ξ u c K (ε / 2)) x t := by
    have htD : t ∈ Icc 0 (D / 2) := ⟨ht.1, by dsimp only [D]; linarith [ht.2]⟩
    have hsign (y : Pt X) :
        Ξ y - ε / 2 * u y ^ 2 - majorantGrowthShift c K (ε / 2) ≤ 0 :=
      majorantGrowthShift_controls hc hK hhalfpos (hr y) (hcompare y) (hgrowth y)
    exact hcomparison D hD Ξ hΞ hRic (ε / 2) hhalfpos hhalfadm
      (majorantGrowthShift c K (ε / 2)) hsign x t htD
  let Q : STF X := shiftedMajorantComparison D n U P Ξ u c K ε
  let cQ := min (1 / 2) (D * ε / (2 * K ^ 2))
  have hcQ : 0 < cQ := lt_min (by norm_num) (by positivity)
  refine ⟨Q, cQ, hcQ,
    shifted_majorant_comparison_smooth hUcc hPcc hΞ hu.1 D c K ε, ?_⟩
  intro x t ht
  have hhalfxt := hhalf x t ht
  have hpos : 0 < Q x t := (shifted_majorant_comparison_positive D n U P Ξ u c K ε
    hD.le hε.le x t hhalfxt).1
  have hulower : (1 + distFrom X.metric.form o x) / K ≤ u x := by
    simpa only [div_eq_mul_inv, mul_comm] using (hcontrolled x).1
  have hquad : (D * ε / (2 * K ^ 2)) * (1 + distFrom X.metric.form o x ^ 2) + 1 ≤ Q x t :=
    shifted_majorant_comparison_distance_lower D n U P Ξ u c K ε
      hD hε hK x t (distFrom X.metric.form o x) (hr x) hulower hhalfxt
  have hcQquad : cQ ≤ D * ε / (2 * K ^ 2) := min_le_right _ _
  have hproper : cQ * (1 + distFrom X.metric.form o x ^ 2) ≤ Q x t := by
    have hm := mul_le_mul_of_nonneg_right hcQquad
      (show 0 ≤ 1 + distFrom X.metric.form o x ^ 2 by positivity)
    linarith
  refine ⟨hpos, hproper, ?_⟩
  have hUnique := (uniqueDiffOn_Icc hT) t ht
  have hφ := hweightSmooth ε
  have hweight : (gMat X.metric.form x - (D : ℂ) • ricci X.metric.form x +
      (D : ℂ) • levi (penalizedMajorantWeight Ξ u c K ε) x -
      ((1 / 2 : ℝ) : ℂ) • gMat X.metric.form x).PosSemidef :=
    penalized_original_majorant_levi X.metric.form Ξ u hΞ hu.1
      (A := majorantGrowthShift c K ε)
      hD.le hε.le hbudget hRic (fun y => (hsquare y).2) x
  have hlow := comparisonFunction_heat_lower X.metric.form h U P
    (penalizedMajorantWeight Ξ u c K ε) D x hUnique
    ((hPtime x t ht.1).1.mono hsub) ((hUtime x t ht.1).mono hsub)
    (smoothSpaceTime_slice hUcc ht) (smoothSpaceTime_slice hPcc ht) hφ
    (hpot t ht.1) (hheat T hT x t ht) hweight
  have htr : 0 ≤ traceWith (gMat (h t) x) (gMat X.metric.form x) :=
    traceWith_posSemidef_nonneg
      (LeafProofs.L12Aux.hMat_posDef (h t) x (chartPt x x) (mem_extChartAt_target x))
      (LeafProofs.L12Aux.hMat_posDef X.metric.form x (chartPt x x)
        (mem_extChartAt_target x)).posSemidef
  change cQ * traceWith (gMat (h t) x) (gMat X.metric.form x) ≤
    fieldHeatWithin h (Icc 0 T)
      (fun s y => shiftedMajorantComparison D n U P Ξ u c K ε y s) x t
  rw [shifted_majorant_comparison_heat h hUcc hPcc hΞ hu.1 D c K ε x ht hUnique]
  exact (mul_le_mul_of_nonneg_right (min_le_left _ _) htr).trans hlow

end Yau.NodeProofs.F01Aux
