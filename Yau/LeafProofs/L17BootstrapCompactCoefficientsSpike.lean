import Yau.LeafProofs.L17BootstrapCompactCoefficientsJets

/-! A distinguished varying coefficient and a parameter-independent background. -/

noncomputable section
open Set Metric
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Yau.LeafProofs.L17BootstrapCompactCoefficientsAux
open L17Aux L17BootstrapHolderTaylorAux

variable {Param E F : Type*}
  [NormedAddCommGroup Param] [NormedSpace ℝ Param]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem background_zero_jet_norm (b : E → ℝ → F) (theta : Param) (z : E) (t : ℝ) :
    ‖singleParamJet (fun (_ : Param) => b) 0 theta z t‖ = ‖b z t‖ := by
  exact norm_iteratedFDeriv_zero

theorem background_zero_space_norm (b : E → ℝ → F) (theta : Param) (z : E) (t : ℝ) :
    ‖fderiv ℝ (fun w => singleParamJet (fun (_ : Param) => b) 0 theta w t) z‖ =
      ‖fderiv ℝ (fun w => b w t) z‖ := by
  change ‖fderiv ℝ ((continuousMultilinearCurryFin0 ℝ Param F).symm ∘ (fun w => b w t)) z‖ = _
  rw [LinearIsometryEquiv.comp_fderiv]
  exact (continuousMultilinearCurryFin0 ℝ Param F).symm.toLinearIsometry.norm_toContinuousLinearMap_comp

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem background_zero_time_norm (b : E → ℝ → F) (theta : Param) (z : E) (t : ℝ) :
    ‖deriv (fun s => singleParamJet (fun (_ : Param) => b) 0 theta z s) t‖ =
      ‖deriv (fun s => b z s) t‖ := by
  change ‖fderiv ℝ ((continuousMultilinearCurryFin0 ℝ Param F).symm ∘ (fun s => b z s)) t 1‖ =
    ‖fderiv ℝ (fun s => b z s) t 1‖
  rw [LinearIsometryEquiv.comp_fderiv]
  exact (continuousMultilinearCurryFin0 ℝ Param F).symm.norm_map _

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem background_pos_jet (b : E → ℝ → F) {k : ℕ} (hk : k ≠ 0)
    (theta : Param) (z : E) (t : ℝ) :
    singleParamJet (fun (_ : Param) => b) k theta z t = 0 := by
  exact congrFun (iteratedFDeriv_const_of_ne hk (b z t)) theta

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

def spikeCoefficient {P : UniformChartPartition g} (p : P.centers)
    (special : Param → ComplexVector n → ℝ → F)
    (base : P.centers → ComplexVector n → ℝ → F)
    (theta : Param) (q : P.centers) (z : ComplexVector n) (t : ℝ) : F := by
  classical
  exact if q = p then special theta z t else base q z t

theorem spike_jet_at {P : UniformChartPartition g} (p : P.centers)
    (special : Param → ComplexVector n → ℝ → F)
    (base : P.centers → ComplexVector n → ℝ → F)
    (k : ℕ) (theta : Param) (z : ComplexVector n) (t : ℝ) :
    coeffParamJet (spikeCoefficient p special base) k theta p z t =
      singleParamJet special k theta z t := by
  classical
  simp only [coeffParamJet, spikeCoefficient, ite_true, singleParamJet]

theorem spike_jet_away {P : UniformChartPartition g} (p : P.centers)
    (special : Param → ComplexVector n → ℝ → F)
    (base : P.centers → ComplexVector n → ℝ → F)
    {q : P.centers} (hq : q ≠ p) (k : ℕ) (theta : Param) (z : ComplexVector n) (t : ℝ) :
    coeffParamJet (spikeCoefficient p special base) k theta q z t =
      singleParamJet (fun (_ : Param) => base q) k theta z t := by
  classical
  simp only [coeffParamJet, spikeCoefficient, ite_eq_right hq, singleParamJet]

/-- One common budget works at every center and at every parameter order. -/
theorem exists_spike_mixed_budgets [ProperSpace Param]
    (P : UniformChartPartition g) (p : P.centers) {R Rout T : ℝ} (hRRout : R < Rout)
    (special : Param → ComplexVector n → ℝ → F)
    (base : P.centers → ComplexVector n → ℝ → F)
    (hSpecial : ContDiffOn ℝ ∞
      (fun a : Param × (ComplexVector n × ℝ) => special a.1 a.2.1 a.2.2)
      (ball 0 Rout ×ˢ (ball 0 (2*P.radius) ×ˢ Set.univ)))
    {A Z U : ℝ} (_hA : 0 ≤ A) (_hZ : 0 ≤ Z) (_hU : 0 ≤ U)
    (hBase : ∀ q z, z ∈ ball 0 P.radius → ∀ t ∈ Icc (0:ℝ) T,
      ‖base q z t‖ ≤ A ∧ ‖fderiv ℝ (fun w => base q w t) z‖ ≤ Z ∧
      ‖deriv (fun s => base q z s) t‖ ≤ U) :
    ∃ B : ℕ → ℝ, (∀ k, 0 ≤ B k) ∧
      ∀ k theta, theta ∈ ball 0 R → ∀ q z, z ∈ ball 0 P.radius → ∀ t ∈ Icc (0:ℝ) T,
        ‖coeffParamJet (spikeCoefficient p special base) k theta q z t‖ ≤ B k ∧
        ‖fderiv ℝ (fun w => coeffParamJet (spikeCoefficient p special base) k theta q w t) z‖ ≤ B k ∧
        ‖deriv (fun s => coeffParamJet (spikeCoefficient p special base) k theta q z s) t‖ ≤ B k := by
  classical
  obtain ⟨C,hC⟩ := exists_compact_mixed_budgets P hRRout special hSpecial
  let B := fun k => max (C k) (max A (max Z U))
  have hCB : ∀ k, C k ≤ B k := fun k => le_max_left _ _
  have hAB : ∀ k, A ≤ B k := fun k => (le_max_left _ _).trans (le_max_right _ _)
  have hZB : ∀ k, Z ≤ B k := fun k => (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hUB : ∀ k, U ≤ B k := fun k => (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hB : ∀ k, 0 ≤ B k := fun k => (hC k).1.trans (hCB k)
  refine ⟨B,hB,?_⟩
  intro k theta htheta q z hz t ht
  by_cases hq : q = p
  · subst q
    have hc := (hC k).2 theta (ball_subset_closedBall htheta) z (ball_subset_closedBall hz) t ht
    simp only [spike_jet_at]
    exact ⟨hc.1.trans (hCB k),hc.2.1.trans (hCB k),hc.2.2.trans (hCB k)⟩
  · simp only [spike_jet_away p special base hq]
    by_cases hk : k = 0
    · subst k
      rw [background_zero_jet_norm,background_zero_space_norm,background_zero_time_norm]
      have hb := hBase q z hz t ht
      exact ⟨hb.1.trans (hAB 0),hb.2.1.trans (hZB 0),hb.2.2.trans (hUB 0)⟩
    · simp only [background_pos_jet (base q) hk, fderiv_const_apply, deriv_const, norm_zero]
      exact ⟨hB k,hB k,hB k⟩

theorem spike_contDiffOn (P : UniformChartPartition g) (p : P.centers)
    {R Rout : ℝ} (hRRout : R ≤ Rout)
    (special : Param → ComplexVector n → ℝ → F)
    (base : P.centers → ComplexVector n → ℝ → F)
    (hSpecial : ContDiffOn ℝ ∞
      (fun a : Param × (ComplexVector n × ℝ) => special a.1 a.2.1 a.2.2)
      (ball 0 Rout ×ˢ (ball 0 (2*P.radius) ×ˢ Set.univ)))
    (hBase : ∀ q, ContDiffOn ℝ ∞ (fun b : ComplexVector n × ℝ => base q b.1 b.2)
      (ball 0 (2*P.radius) ×ˢ Set.univ)) :
    ∀ q, ContDiffOn ℝ ∞
      (fun a : Param × (ComplexVector n × ℝ) => spikeCoefficient p special base a.1 q a.2.1 a.2.2)
      (ball 0 R ×ˢ (ball 0 (2*P.radius) ×ˢ Set.univ)) := by
  classical
  intro q
  by_cases hq : q = p
  · simp only [spikeCoefficient, ite_eq_left hq]
    exact hSpecial.mono (fun _ ha => ⟨ball_subset_ball hRRout ha.1,ha.2⟩)
  · simp only [spikeCoefficient, ite_eq_right hq]
    exact (hBase q).comp contDiffOn_snd (fun _ ha => ha.2)

end Yau.LeafProofs.L17BootstrapCompactCoefficientsAux
