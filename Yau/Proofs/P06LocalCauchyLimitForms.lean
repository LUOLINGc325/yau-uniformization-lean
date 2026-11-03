import Yau.Proofs.P06LocalCauchyLimitFunctions
import Yau.LeafProofs.L03
import Yau.Blueprint.HodgeContracts

noncomputable section
open Filter Set
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.LocalCauchyLimit
open Yau Yau.LeafProofs.L03
variable {n k : ℕ} {M : ComplexManifold n}

def JointJetCauchy (Us : ℕ → ℝ → RealForm M k) : Prop :=
  ∀ x (K : Set (ComplexVector n)), IsCompact K → K ⊆ chartTarget x →
    ∀ eps T, 0 < eps → eps < T → ∀ (m : ℕ) (I : Fin k → RIdx n) η, 0 < η →
      ∃ N, ∀ j, N ≤ j → ∀ l, N ≤ l → ∀ z ∈ K, ∀ t ∈ Icc eps T,
        ‖iteratedFDeriv ℝ m (fun p : ComplexVector n × ℝ =>
          formComponents (Us j p.2) x p.1 I - formComponents (Us l p.2) x p.1 I) (z,t)‖ < η

def JointJetLimit (Us : ℕ → ℝ → RealForm M k) (U : ℝ → RealForm M k) : Prop :=
  ∀ x (K : Set (ComplexVector n)), IsCompact K → K ⊆ chartTarget x →
    ∀ eps T, 0 < eps → eps < T → ∀ (m : ℕ) (I : Fin k → RIdx n) η, 0 < η →
      ∃ N, ∀ j, N ≤ j → ∀ z ∈ K, ∀ t ∈ Icc eps T,
        ‖iteratedFDeriv ℝ m (fun p : ComplexVector n × ℝ =>
          formComponents (Us j p.2) x p.1 I - formComponents (U p.2) x p.1 I) (z,t)‖ < η

theorem chart_fullJet_cauchy (Us : ℕ → ℝ → RealForm M k)
    (hUs : ∀ j, SmoothFormTime (Us j) (Ioi 0)) (hc : JointJetCauchy Us)
    (x : M.Carrier) (I : Fin k → RIdx n) :
    FullJetCauchyOn (fun (j : ℕ) (p : ComplexVector n × ℝ) => formComponents (Us j p.2) x p.1 I)
      (chartTarget x ×ˢ Ioi 0) := by
  intro m C hC hCS η hη
  by_cases hne : C.Nonempty
  · obtain ⟨p,hp,hmin⟩ := hC.exists_isMinOn hne continuous_snd.continuousOn
    obtain ⟨q,hq,hmax⟩ := hC.exists_isMaxOn hne continuous_snd.continuousOn
    let eps := p.2/2
    let T := max q.2 eps + 1
    have heps : 0 < eps := half_pos (hCS hp).2
    have heT : eps < T := by dsimp only [T]; linarith [le_max_right q.2 eps]
    have hK : IsCompact (Prod.fst '' C) := hC.image continuous_fst
    have hKx : Prod.fst '' C ⊆ chartTarget x := by
      rintro z ⟨a,ha,rfl⟩
      exact (hCS ha).1
    obtain ⟨N,hN⟩ := hc x _ hK hKx eps T heps heT m I η hη
    refine ⟨N,fun j hj l hl a ha => ?_⟩
    have hat : a.2 ∈ Icc eps T := by
      refine ⟨?_,?_⟩
      · have h : p.2 ≤ a.2 := hmin ha
        dsimp only [eps]
        linarith [show 0 < p.2 from (hCS hp).2]
      · exact (hmax ha).trans (by dsimp only [T]; linarith [le_max_left q.2 eps])
    have hb := hN j hj l hl a.1 ⟨a,ha,rfl⟩ a.2 hat
    change ‖iteratedFDeriv ℝ m
      ((fun p : ComplexVector n × ℝ => formComponents (Us j p.2) x p.1 I) -
       (fun p : ComplexVector n × ℝ => formComponents (Us l p.2) x p.1 I)) a‖ < η at hb
    rw [iteratedFDeriv_sub_apply (i := m)
      (((hUs j x I).contDiffAt
        (((isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_Ioi).mem_nhds (hCS ha))).of_le (by simp))
      (((hUs l x I).contDiffAt
        (((isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_Ioi).mem_nhds (hCS ha))).of_le (by simp))] at hb
    exact hb
  · exact ⟨0,fun _ _ _ _ a ha => (hne ⟨a,ha⟩).elim⟩

theorem coefficient_cauchy (Us : ℕ → ℝ → RealForm M k) (hc : JointJetCauchy Us)
    (x : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget x)
    (t : ℝ) (ht : 0 < t) (I : Fin k → RIdx n) :
    CauchySeq (fun j => formComponents (Us j t) x z I) := by
  apply Metric.cauchySeq_iff.mpr
  intro η hη
  obtain ⟨N,hN⟩ := hc x {z} isCompact_singleton (by simpa using hz)
    (t/2) (t+1) (half_pos ht) (by linarith) 0 I η hη
  refine ⟨N,fun j hj l hl => ?_⟩
  have hb := hN j hj l hl z (mem_singleton z) t ⟨by linarith,by linarith⟩
  simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,Real.dist_eq] using hb

def fiberPullback (y : M.Carrier) :
    ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] (TangentVector M y) [⋀^Fin k]→L[ℝ] ℝ := by
  letI : ContinuousSMul ℝ (TangentVector M y) := IsScalarTower.continuousSMul ℂ
  exact ContinuousAlternatingMap.compContinuousLinearMapCLM (tangentCoordsRealContinuousLinearMap y y)

theorem fiberPullback_chartForm (A : RealForm M k) (y : M.Carrier) :
    fiberPullback y (chartForm A y (chartPt y y)) = A y := by
  apply ContinuousAlternatingMap.ext
  intro v
  change (chartForm A y (chartPt y y)) (fun r => tangentCoords y y (v r)) = A y v
  simp only [chartForm,ContinuousAlternatingMap.compContinuousLinearMap_apply,
    chartRealContinuousLinearMap_apply,Function.comp_def]
  have hy : y ∈ (extChartAt (ComplexModel n) y).source := mem_extChartAt_source y
  have hid : chartInv y (chartPt y y) = y := (extChartAt (ComplexModel n) y).left_inv hy
  rw [hid]
  congr 1
  funext r
  exact Yau.LeafProofs.L12Aux.chartVec_tangentCoords y y hy (v r)

/-- The actual pointwise form limit is constructed in each actual tangent
fiber from the same sequence; every other chart functional commutes with it. -/
theorem exists_actual_pointwise_limit (Us : ℕ → ℝ → RealForm M k)
    (hc : JointJetCauchy Us) (A : RealForm M k) :
    ∃ U : ℝ → RealForm M k, U 0 = A ∧
      ∀ x z, z ∈ chartTarget x → ∀ t, 0 < t → ∀ I,
        Tendsto (fun j => formComponents (Us j t) x z I) atTop
          (𝓝 (formComponents (U t) x z I)) := by
  classical
  have hex (t : ℝ) (y : M.Carrier) (I : Fin k → RIdx n) :
      ∃ a : ℝ, 0 < t → Tendsto (fun j => formComponents (Us j t) y (chartPt y y) I) atTop (𝓝 a) := by
    by_cases ht : 0 < t
    · obtain ⟨a,ha⟩ := cauchySeq_tendsto_of_complete
        (coefficient_cauchy Us hc y (chartPt y y) (mem_extChartAt_target y) t ht I)
      exact ⟨a,fun _ => ha⟩
    · exact ⟨0,fun h => (ht h).elim⟩
  choose a ha using hex
  let P (t : ℝ) (y : M.Carrier) := modelFormReconstruction n k (fun I => a t y I)
  let U : ℝ → RealForm M k := fun t y => if 0 < t then fiberPullback y (P t y) else A y
  refine ⟨U,by funext y; simp only [U,lt_self_iff_false,ite_false],?_⟩
  intro x z hz t ht I
  let y := chartInv x z
  have hcoef : Tendsto (fun j I => formComponents (Us j t) y (chartPt y y) I)
      atTop (𝓝 (fun I => a t y I)) := tendsto_pi_nhds.mpr (fun I => ha t y I ht)
  have hmodel : Tendsto (fun j => chartForm (Us j t) y (chartPt y y)) atTop (𝓝 (P t y)) := by
    have h := ((modelFormReconstruction n k).continuous.tendsto (fun I => a t y I)).comp hcoef
    convert h using 1
    funext j
    exact (modelFormReconstruction_coefficient (chartForm (Us j t) y (chartPt y y))).symm
  letI : ContinuousSMul ℝ (TangentVector M y) := IsScalarTower.continuousSMul ℂ
  let C := (ContinuousAlternatingMap.apply ℝ (TangentVector M y) ℝ
    (fun r => chartVec x y (realVec (I r)))).comp (fiberPullback y)
  have h := (C.continuous.tendsto (P t y)).comp hmodel
  convert h using 1
  · funext j
    change _ = (fiberPullback y (chartForm (Us j t) y (chartPt y y))) _
    rw [fiberPullback_chartForm]
    rfl
  · change 𝓝 ((U t y) _) = _
    simp only [U,ht,ite_true]
    rfl

/-- Generic actual smooth reconstruction from the literal full-jet Cauchy
input. The value at zero is assigned independently of positive-time limits. -/
theorem exists_smooth_limit (Us : ℕ → ℝ → RealForm M k)
    (hUs : ∀ j, SmoothFormTime (Us j) (Ioi 0)) (hc : JointJetCauchy Us) (A : RealForm M k) :
    ∃ U : ℝ → RealForm M k, U 0 = A ∧ SmoothFormTime U (Ioi 0) ∧ JointJetLimit Us U := by
  obtain ⟨U,hU0,hpoint⟩ := exists_actual_pointwise_limit Us hc A
  have hchart (x : M.Carrier) (I : Fin k → RIdx n) :=
    smooth_fullJet_of_pointwise ((isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_Ioi)
      (fun j => hUs j x I) (chart_fullJet_cauchy Us hUs hc x I)
      (fun p hp => hpoint x p.1 hp.1 p.2 hp.2 I)
  refine ⟨U,hU0,fun x I => (hchart x I).1,?_⟩
  intro x K hK hKx eps T heps heT m I η hη
  have hKS : K ×ˢ Icc eps T ⊆ chartTarget x ×ˢ Ioi 0 :=
    fun p hp => ⟨hKx hp.1,lt_of_lt_of_le heps hp.2.1⟩
  have hl := uniform_fullJet_difference
    ((isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_Ioi)
    (fun j => hUs j x I) (hchart x I).1 hKS m
    ((hchart x I).2 m _ (hK.prod isCompact_Icc) hKS) η hη
  obtain ⟨N,hN⟩ := hl
  exact ⟨N,fun j hj z hz t ht => hN j hj (z,t) ⟨hz,ht⟩⟩

theorem exists_formHeatLocalSmoothLimit (Us : ℕ → ℝ → RealForm M 2)
    (hUs : ∀ j, SmoothFormTime (Us j) (Ioi 0)) (hc : JointJetCauchy Us) (A : RealForm M 2) :
    ∃ U : ℝ → RealForm M 2, U 0 = A ∧ SmoothFormTime U (Ioi 0) ∧
      Blueprint.FormHeatLocalSmoothLimit Us U := exists_smooth_limit Us hUs hc A

end Yau.NodeProofs.P06Aux.LocalCauchyLimit
