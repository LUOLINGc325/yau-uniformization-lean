import Yau.LeafProofs.L17BootstrapCompactCoefficientsSpike

/-! Compact ordinary coefficient bounds give genuine Hölder and Banach smooth lifts. -/

noncomputable section
open Set Metric
open scoped Classical Topology ContDiff
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Yau.LeafProofs.L17BootstrapCompactCoefficientsAux
open L17Aux L17HolderAux L17SchauderAux L17BootstrapHolderTaylorAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {Param F : Type*} [NormedAddCommGroup Param] [NormedSpace ℝ Param]
  [ProperSpace Param] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

section Lifts
variable (P : UniformChartPartition g) (p : P.centers) {R Rout T beta : ℝ}
variable (hR : 0 < R) (hRRout : R < Rout) (hT0 : 0 < T) (hT : T ≤ P.radius^2)
  (hb0 : 0 < beta) (hb : beta < 1)
variable (special : Param → ComplexVector n → ℝ → F)
  (base : P.centers → ComplexVector n → ℝ → F)
variable (hSpecial : ContDiffOn ℝ ∞
  (fun a : Param × (ComplexVector n × ℝ) => special a.1 a.2.1 a.2.2)
  (ball 0 Rout ×ˢ (ball 0 (2*P.radius) ×ˢ Set.univ)))
variable (hBaseSmooth : ∀ q, ContDiffOn ℝ ∞
  (fun b : ComplexVector n × ℝ => base q b.1 b.2)
  (ball 0 (2*P.radius) ×ˢ Set.univ))
variable {A Z U : ℝ} (hA : 0 ≤ A) (hZ : 0 ≤ Z) (hU : 0 ≤ U)
variable (hBase : ∀ q z, z ∈ ball 0 P.radius → ∀ t ∈ Icc (0:ℝ) T,
  ‖base q z t‖ ≤ A ∧ ‖fderiv ℝ (fun w => base q w t) z‖ ≤ Z ∧
  ‖deriv (fun s => base q z s) t‖ ≤ U)

include hR hRRout hT0 hT hb0 hb hSpecial hBaseSmooth hA hZ hU hBase

/-- The same parameter radius and time interval work for all derivative orders. -/
theorem exists_holder_spike_lift :
    ∃ cHat : Param → LocalHolderSpace F P T beta,
      ContDiffOn ℝ ∞ cHat (ball 0 R) ∧
      ∀ theta ∈ ball 0 R, ∀ q : LocalCylinder P T,
        localFun F (cHat theta) q =
          if q.1 = p then special theta q.2.1 q.2.2 else base q.1 q.2.1 q.2.2 := by
  classical
  obtain ⟨B,hB,hMixed⟩ := exists_spike_mixed_budgets P p hRRout special base hSpecial hA hZ hU hBase
  have hSmooth := spike_contDiffOn P p hRRout.le special base hSpecial hBaseSmooth
  simpa only [spikeCoefficient] using
    exists_holder_parameter_lift P (spikeCoefficient p special base) hSmooth hT hb
      B B B hB hB hB hMixed hR hT0 hb0

theorem exists_banach_spike_lift :
    ∃ cHat : Param → L17LocalHolderBanachAlgebraAux.LocalHolderBanach F P T beta,
      ContDiffOn ℝ ∞ cHat (ball 0 R) ∧
      ∀ theta ∈ ball 0 R, ∀ q : LocalCylinder P T,
        localFun F (cHat theta).value q =
          if q.1 = p then special theta q.2.1 q.2.2 else base q.1 q.2.1 q.2.2 := by
  classical
  obtain ⟨B,hB,hMixed⟩ := exists_spike_mixed_budgets P p hRRout special base hSpecial hA hZ hU hBase
  have hSmooth := spike_contDiffOn P p hRRout.le special base hSpecial hBaseSmooth
  simpa only [spikeCoefficient] using
    exists_banach_parameter_lift P (spikeCoefficient p special base) hSmooth hT hb
      B B B hB hB hB hMixed hR hT0 hb0

end Lifts
end Yau.LeafProofs.L17BootstrapCompactCoefficientsAux
