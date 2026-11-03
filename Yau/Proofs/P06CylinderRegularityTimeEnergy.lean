import Yau.Proofs.P06CylinderRegularityChartData
import Yau.Proofs.P06ChartLocalL2

/-! The actual local Hilbert indicator controls the space-time chart
value energy. No global norm of the heat path appears. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
open MeasureTheory Filter Module
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.CylinderReg
open Yau Yau.Parabolic Yau.LeafProofs.L03 Yau.LeafProofs

theorem chartValue_integrableOn {n k : ℕ} {M : ComplexManifold n}
    (U : ℝ → RealForm M k) (hU : SmoothFormTime U (Set.Ioi 0))
    (x : M.Carrier) {α : Type} [Fintype α] (b : Basis α ℝ (HodgeJets.Fiber n k))
    {Q : Set (Point n)} (hQ : IsCompact (closure Q))
    (hSub : closure Q ⊆ chartTarget x ×ˢ Set.Ioi 0) :
    IntegrableOn (valueSquare (fun p r => hodgeRegularityCoord b (U p.2) x p.1 r)) Q := by
  have hC : ContDiffOn ℝ ∞ (valueSquare (fun p r => hodgeRegularityCoord b (U p.2) x p.1 r))
      (chartTarget x ×ˢ Set.Ioi 0) :=
    ContDiffOn.sum fun r _ => (hodgeCoordinate_joint_contDiffOn U hU x b r).pow 2
  exact ((hC.continuousOn.mono hSub).integrableOn_compact hQ).mono_set subset_closure

theorem exists_chart_time_energy_constant {n k : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (x : M.Carrier) {α : Type} [Fintype α] (b : Basis α ℝ (HodgeJets.Fiber n k))
    (φ : ComplexVector n → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ chartTarget x)
    (O : Set (ComplexVector n)) (hO : MeasurableSet O) (hone : ∀ z ∈ O, φ z = 1)
    (a btime : ℝ) (hab : a < btime) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ → RealForm M k,
      IntegrableOn (valueSquare (fun p r => hodgeRegularityCoord b (U p.2) x p.1 r))
        (O ×ˢ Set.Ioo a btime) →
      ∀ hL2 : ∀ t ∈ Set.Ioo a btime, L2RealForm g.form μ (U t),
      ∀ L : ℝ, 0 ≤ L →
      (∀ t (ht : t ∈ Set.Ioo a btime),
        ‖Davies.indicator g μ (CylinderChartL2.physicalSupport x φ)
          (CylinderChartL2.physicalSupport_measurable x φ hcφ hφO)
          (realizeActualForm g μ (U t) (hL2 t ht))‖ ≤ L) →
      (∫ p in O ×ˢ Set.Ioo a btime,
        valueSquare (fun p r => hodgeRegularityCoord b (U p.2) x p.1 r) p) ≤ C * L^2 := by
  classical
  choose C hC hLP using fun r : α => CylinderChartL2.chartCoefficient_integral_volume_local_bound
    g μ hμ x φ hφ hcφ hφO (b.coord r).toContinuousLinearMap O hO hone
  let S : ℝ := ∑ r, C r
  have hS : 0 ≤ S := Finset.sum_nonneg fun r _ => (hC r).le
  have hba : 0 < btime-a := sub_pos.mpr hab
  refine ⟨1+(btime-a)*S,by positivity,?_⟩
  intro U hInt hL2 L hL hBound
  let f : Point n → ℝ := valueSquare (fun p r => hodgeRegularityCoord b (U p.2) x p.1 r)
  change Integrable f (volume.restrict (O ×ˢ Set.Ioo a btime)) at hInt
  have hIntProd : Integrable f ((volume.restrict O).prod (volume.restrict (Set.Ioo a btime))) := by
    simpa only [Measure.prod_restrict, ← Measure.volume_eq_prod, f] using hInt
  have hSlice (t : ℝ) (ht : t ∈ Set.Ioo a btime) : (∫ z in O, f (z,t)) ≤ S * L^2 := by
    have hEachInt (r : α) : IntegrableOn (fun z => (hodgeRegularityCoord b (U t) x z r)^2) O := by
      have h := (chartFunctional_memLp g μ hμ x φ hφ hcφ hφO
        (b.coord r).toContinuousLinearMap (U t) (hL2 t ht)).integrable_sq
      rw [lebesgueC_eq_volume] at h
      apply h.integrableOn.congr_fun ?_ hO
      intro z hz
      simp only [chartFunctional,hone z hz,one_mul,hodgeRegularityCoord]
      rfl
    have hEach (r : α) : (∫ z in O, (hodgeRegularityCoord b (U t) x z r)^2) ≤ C r*L^2 := by
      have h := hLP r (U t) (hL2 t ht)
      have hN := pow_le_pow_left₀ (norm_nonneg _) (hBound t ht) 2
      exact h.trans (mul_le_mul_of_nonneg_left hN (hC r).le)
    change (∫ z in O, ∑ r, (hodgeRegularityCoord b (U t) x z r)^2) ≤ _
    rw [integral_finsetSum Finset.univ (fun r _ => hEachInt r)]
    simpa only [← Finset.sum_mul,S] using Finset.sum_le_sum (s := Finset.univ) (fun r _ => hEach r)
  have hTimeInt := hIntProd.integral_prod_right
  letI : IsFiniteMeasure (volume.restrict (Set.Ioo a btime)) :=
    ⟨by simp [Real.volume_Ioo]⟩
  have hConstInt : Integrable (fun _ : ℝ => S*L^2) (volume.restrict (Set.Ioo a btime)) := by
    exact integrable_const _
  have hTime := setIntegral_mono_on hTimeInt hConstInt measurableSet_Ioo hSlice
  have hConst : (∫ _t in Set.Ioo a btime, S*L^2) = (btime-a)*S*L^2 := by
    simp only [integral_const,Measure.real,Measure.restrict_apply_univ,Real.volume_Ioo,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le),smul_eq_mul]
    ring
  rw [hConst] at hTime
  have hFubini : (∫ p in O ×ˢ Set.Ioo a btime, f p) =
      ∫ t in Set.Ioo a btime, ∫ z in O, f (z,t) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact integral_prod_symm f hIntProd
  rw [hFubini]
  nlinarith [sq_nonneg L]

end Yau.NodeProofs.P06Aux.CylinderReg
