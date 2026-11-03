import Yau.Proofs.P03DirectionalEvaluation

open scoped Manifold Topology
open Set Filter

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem continuousAt_directionalEvaluation (a : M.Carrier) (f : holomorphicFunctions M)
    (z v : ComplexVector n) (hz : z ∈ chartTarget a) :
    ContinuousAt (fun p : holomorphicFunctions M × ComplexVector n =>
      fderiv ℂ (inChart a (p.1.1 : M.Carrier → ℂ)) p.2 v) (f, z) := by
  obtain ⟨ρ, hρ, hsub⟩ := Yau.LeafProofs.L17Holomorphic.exists_closedBall_subset
    (isOpen_extChartAt_target a) hz
  let S : Set (holomorphicFunctions M × ComplexVector n) := univ ×ˢ Metric.ball z (ρ / 4)
  have hloc : ContinuousOn (fun p : holomorphicFunctions M × ComplexVector n =>
      fderiv ℂ (inChart a (p.1.1 : M.Carrier → ℂ)) p.2 v) S := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    let j : S → holomorphicFunctions M × Metric.ball z (ρ / 4) := fun p =>
      (p.1.1, ⟨p.1.2, p.2.2⟩)
    have hj : Continuous j := by fun_prop
    exact (continuous_directionalEvaluation_on_ball a z v hρ hsub).comp hj
  apply hloc.continuousAt
  exact (isOpen_univ.prod Metric.isOpen_ball).mem_nhds
    ⟨mem_univ _, Metric.mem_ball_self (by positivity)⟩

theorem continuousOn_chart_derivativeEvaluation (a : M.Carrier) :
    ContinuousOn (fun p : holomorphicFunctions M × ComplexVector n =>
      fderiv ℂ (inChart a (p.1.1 : M.Carrier → ℂ)) p.2) (univ ×ˢ chartTarget a) := by
  apply continuousOn_clm_apply.mpr
  intro v p hp
  exact (continuousAt_directionalEvaluation a p.1 p.2 v hp.2).continuousWithinAt

def tupleDerivativeCLM {N : ℕ} (a : M.Carrier) (f : Fin N → holomorphicFunctions M)
    (z : ComplexVector n) : ComplexVector n →L[ℂ] (Fin N → ℂ) :=
  ContinuousLinearMap.pi (fun i => fderiv ℂ (inChart a (f i).1) z)

theorem continuousOn_tupleDerivativeCLM {N : ℕ} (a : M.Carrier) :
    ContinuousOn (fun p : (Fin N → holomorphicFunctions M) × ComplexVector n =>
      tupleDerivativeCLM a p.1 p.2) (univ ×ˢ chartTarget a) := by
  apply continuousOn_clm_apply.mpr
  intro v
  apply continuousOn_pi.mpr
  intro i
  let φ : ((Fin N → holomorphicFunctions M) × ComplexVector n) →
      holomorphicFunctions M × ComplexVector n := fun p => (p.1 i, p.2)
  have hφ : Continuous φ := by fun_prop
  have hmap : MapsTo φ (univ ×ˢ chartTarget a) (univ ×ˢ chartTarget a) :=
    fun p hp => ⟨mem_univ _, hp.2⟩
  have hc := (continuousOn_chart_derivativeEvaluation a).comp
    hφ.continuousOn hmap
  exact hc.clm_apply continuousOn_const

end Yau.NodeProofs.P03Aux
