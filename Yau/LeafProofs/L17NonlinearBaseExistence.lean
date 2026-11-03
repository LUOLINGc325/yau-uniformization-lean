import Yau.LeafProofs.L17NonlinearBaseData
import Yau.LeafProofs.L17ScalarLinearIsomorphismPartition

open Set Metric
open scoped ContDiff
noncomputable section
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux
open L17HolderAux L17SchauderAux L17ParabolicOperatorAux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem BoundedChartFamily.exists_nonlinear_base (A : BoundedChartFamily g) (hg : MetricSmooth g) :
    ∃ N : ℕ, ∃ B : ℕ → ℝ, (∀ k,0<B k) ∧
      ∀ ε : ℝ,0<ε → ∃ P : UniformChartPartition g,
        P.charts=A ∧ P.radius<ε ∧ P.overlapBudget=N ∧
        (∀ k (p : P.centers) q z,z∈ball (0 : ComplexVector n) (2*P.radius) →
          ‖iteratedFDeriv ℝ k (fun w => P.weight p (P.charts.chart q w)) z‖≤B k*(P.radius⁻¹)^k ∧
          ‖iteratedFDeriv ℝ k (fun w => P.localization p (P.charts.chart q w)) z‖≤B k*(P.radius⁻¹)^k) ∧
        ∃ hr : P.radius≤1,2*P.radius<A.radius ∧
          ∃ T : ℝ,∃ hT : 0<T,∃ hTime : T≤P.radius^2,NonlinearBaseAt P T hT hTime hr := by
  obtain ⟨N,B,Ca,Cb,S,hB,hCa,hCb,hS,hS1,hAll⟩ :=
    A.exists_two_exponent_scalar_isomorphisms_with_partition hg
  refine ⟨N,B,hB,?_⟩
  intro ε hε
  obtain ⟨P,hPA,hρε,hN,hJets,hr,hρ,hIso⟩ := hAll ε hε
  let Cw := max (1:ℝ) (B 1)
  have hCw : 1≤Cw := le_max_left _ _
  have hD (p : P.centers) (q : M.Carrier) z (hz : z∈ball (0 : ComplexVector n) (2*P.radius)) :
      ‖fderiv ℝ (fun w => P.weight p (P.charts.chart q w)) z‖≤Cw/P.radius := by
    have h := (hJets 1 p q z hz).1
    rw [norm_iteratedFDeriv_one,pow_one] at h
    apply h.trans
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (le_max_right (1:ℝ) (B 1)) (inv_nonneg.mpr P.radius_pos.le)
  have hρP : 2*P.radius<P.charts.radius := by rw [hPA]; exact hρ
  obtain ⟨T,hT,hTS,hTime,hBase⟩ := exists_nonlinear_base_of_scalar_isomorphisms
    P hg hr hρP Cw hCw hD Ca Cb (P.radius^2*S)
      (mul_pos (sq_pos_of_pos P.radius_pos) hS) hIso
  exact ⟨P,hPA,hρε,hN,hJets,hr,hρ,T,hT,hTime,hBase⟩

end Yau.LeafProofs.L17Aux
