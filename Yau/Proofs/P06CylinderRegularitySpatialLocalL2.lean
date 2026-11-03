import Yau.Proofs.P06CylinderRegularityTimeEnergy

/-! Uniform-in-time chart value energy is controlled by one fixed
physical compact restriction, with constants independent of the form. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
open MeasureTheory Filter Module
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.CylinderReg
open Yau Yau.Parabolic Yau.LeafProofs.L03 Yau.LeafProofs

theorem exists_chart_spatial_energy_constant {n k : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (x : M.Carrier) {α : Type} [Fintype α] (b : Basis α ℝ (HodgeJets.Fiber n k))
    (φ : ComplexVector n → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ chartTarget x)
    (O : Set (ComplexVector n)) (hO : MeasurableSet O) (hone : ∀ z ∈ O, φ z = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : RealForm M k) (hA : L2RealForm g.form μ A),
      (∫ z in O, ∑ r, (hodgeRegularityCoord b A x z r)^2) ≤
        C * ‖Davies.indicator g μ (CylinderChartL2.physicalSupport x φ)
          (CylinderChartL2.physicalSupport_measurable x φ hcφ hφO)
          (realizeActualForm g μ A hA)‖^2 := by
  classical
  choose C hC hLP using fun r : α => CylinderChartL2.chartCoefficient_integral_volume_local_bound
    g μ hμ x φ hφ hcφ hφO (b.coord r).toContinuousLinearMap O hO hone
  have hSum : 0 ≤ ∑ r, C r := Finset.sum_nonneg fun r _ => (hC r).le
  refine ⟨1+∑ r, C r,by positivity,?_⟩
  intro A hA
  have hEachInt (r : α) : IntegrableOn (fun z => (hodgeRegularityCoord b A x z r)^2) O := by
    have h := (chartFunctional_memLp g μ hμ x φ hφ hcφ hφO
      (b.coord r).toContinuousLinearMap A hA).integrable_sq
    rw [lebesgueC_eq_volume] at h
    apply h.integrableOn.congr_fun ?_ hO
    intro z hz
    simp only [chartFunctional,hone z hz,one_mul,hodgeRegularityCoord]
    rfl
  rw [integral_finsetSum Finset.univ (fun r _ => hEachInt r)]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun r _ => hLP r A hA)
  rw [← Finset.sum_mul] at h
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _))

end Yau.NodeProofs.P06Aux.CylinderReg
