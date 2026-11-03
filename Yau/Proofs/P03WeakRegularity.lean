import Yau.Proofs.P03Weyl
import Yau.Proofs.P03WeakTests

open scoped Manifold Topology ContDiff ENNReal
open MeasureTheory Bundle

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- Apply the proved local weak-CR theorem directly to coefficients of the
actual homogeneous distributional Dolbeault equation. -/
theorem weakDbar_zero_holomorphic_coefficients (u : NQForm E 0)
    (hu : WeakDbar (r := r) E u (zeroForm E 1)) (a : M.Carrier) (α : Fin r) :
    ∃ v : ComplexVector n → ℂ,
      DifferentiableOn ℂ v (localDomain (r := r) E a) ∧
      (fun z => coefficients (r := r) E u a z Fin.elim0 α)
        =ᵐ[(lebesgueC n).restrict (localDomain (r := r) E a)] v := by
  apply localCRWeyl (localDomain (r := r) E a)
    (fun z => coefficients (r := r) E u a z Fin.elim0 α) (localDomain_isOpen E a)
    (hu.1 a Fin.elim0 α).1
  · intro K hK hs
    exact locallyL2_coefficients_memLp E u hu.1 a Fin.elim0 α K hK hs
  · intro i ψ hψ hcψ hsψ
    exact weakDbar_zero_scalar_tests E u hu a i α ψ hψ hcψ hsψ

end Yau.NodeProofs.P03Aux
