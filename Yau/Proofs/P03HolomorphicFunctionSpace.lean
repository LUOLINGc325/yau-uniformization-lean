import Yau.Proofs.P03CompactOpenAmbient
import Yau.Proofs.P03CompactCRTests
import Yau.Proofs.P03ContinuousCR

open scoped Manifold Topology Uniformity ContDiff
open Set TopologicalSpace

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ}

/-- Genuine holomorphic functions, inside continuous maps with compact
convergence. All operations retain their pointwise meaning. -/
def holomorphicFunctions (M : ComplexManifold n) : Submodule ℂ C(M.Carrier, ℂ) where
  carrier := {f | IsHolomorphicFn (f : M.Carrier → ℂ)}
  zero_mem' := mdifferentiable_const
  add_mem' hf hg := hf.add hg
  smul_mem' c f hf := MDifferentiable.const_smul c hf

theorem isClosed_holomorphicFunctions (M : ComplexManifold n) :
    IsClosed (holomorphicFunctions M : Set C(M.Carrier, ℂ)) := by
  have heq : (holomorphicFunctions M : Set C(M.Carrier, ℂ)) =
      {f | ∀ (a : M.Carrier) (i : Fin n) (ψ : ComplexVector n → ℂ)
        (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
        (hs : tsupport ψ ⊆ chartTarget a), scalarCRTestCLM a i ψ hψ hc hs f = 0} := by
    ext f
    change IsHolomorphicFn (f : M.Carrier → ℂ) ↔ _
    rw [IsHolomorphicFn, mdifferentiable_iff_chartDifferentiable]
    constructor
    · intro hf a i ψ hψ hc hs
      rw [scalarCRTestCLM_apply]
      exact (continuous_holomorphic_iff_weakCR (isOpen_extChartAt_target a)
        (hf a).continuousOn).mp (hf a) i ψ hψ hc hs
    · intro hf a
      apply (continuous_holomorphic_iff_weakCR (isOpen_extChartAt_target a)
        (f.continuous.comp_continuousOn
          (continuousOn_extChartAt_symm (I := ComplexModel n) a))).mpr
      intro i ψ hψ hc hs
      have ht := hf a i ψ hψ hc hs
      exact (scalarCRTestCLM_apply (M := M) a i ψ hψ hc hs f).symm.trans ht
  rw [heq]
  simp only [setOf_forall]
  apply isClosed_iInter
  intro a
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro ψ
  apply isClosed_iInter
  intro hψ
  apply isClosed_iInter
  intro hc
  apply isClosed_iInter
  intro hs
  exact isClosed_eq (scalarCRTestCLM a i ψ hψ hc hs).continuous continuous_const

theorem holomorphicFunctions_complete (M : ComplexManifold n) :
    CompleteSpace (holomorphicFunctions M) := by
  letI := continuousFunctions_complete M
  exact (isClosed_holomorphicFunctions M).isComplete.completeSpace_coe

theorem holomorphicFunctions_completelyMetrizable (M : ComplexManifold n) :
    IsCompletelyMetrizableSpace (holomorphicFunctions M) := by
  letI := continuousFunctions_completelyMetrizable M
  exact (isClosed_holomorphicFunctions M).isCompletelyMetrizableSpace

theorem holomorphicFunctions_baire (M : ComplexManifold n) :
    BaireSpace (holomorphicFunctions M) := by
  letI := holomorphicFunctions_completelyMetrizable M
  infer_instance

end Yau.NodeProofs.P03Aux
