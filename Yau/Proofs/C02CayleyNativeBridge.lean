import Yau.Proofs.C02OperatorMatrixJets
import Yau.LeafProofs.L21Integrability
import Yau.LeafProofs.L21Normalization

/-! Identifying the actual uniformly bounded Cayley expression with the
received native graph coefficients and their exact finite-jet predicate. -/

noncomputable section
open Set
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs
variable {n : ℕ}

theorem native_stdComplex_eq : L21Aux.stdComplex n = L12Aux.complexStructureCLM n := by
  apply ContinuousLinearMap.ext
  intro v
  rfl

theorem native_cayleyMap_eq (J : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n)
    (x : ComplexVector n) : L21Aux.cayleyMap (J x) = complexCayleyField J x := by
  simp only [L21Aux.cayleyMap, native_stdComplex_eq, complexCayleyField]

theorem native_graphMatrix_eq (J : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n) :
    L21Aux.graphMatrix (fun x => L21Aux.cayleyMap (J x)) = cayleyCoefficientMatrix J := by
  funext x
  ext i k
  simp only [L21Aux.graphMatrix, cayleyCoefficientMatrix, native_cayleyMap_eq]

theorem native_cayley_graph_properties {O : Set (ComplexVector n)} (hO : IsOpen O)
    {J : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n}
    (hJ : ContDiffOn ℝ ∞ J O)
    (hJ2 : ∀ x ∈ O, ∀ v, J x (J x v) = -v)
    (hN : ∀ x ∈ O, ∀ v w, LeafCandidates.nijenhuis J x v w = 0)
    (hClose : ∀ x ∈ O, ‖J x - L12Aux.complexStructureCLM n‖ ≤ 1 / 4) :
    L21Aux.MatrixSmoothOn (cayleyCoefficientMatrix J) O ∧
      L21Aux.CommutesOn (cayleyCoefficientMatrix J) O := by
  have hi (x : ComplexVector n) (hx : x ∈ O) : (J x + L21Aux.stdComplex n).IsInvertible := by
    rw [native_stdComplex_eq]
    exact (complex_sum_isInvertible_and_inverse_norm (J x) (hClose x hx)).1
  rw [← native_graphMatrix_eq]
  exact ⟨L21Aux.cayley_graph_matrix_smooth hO hJ hi,
    L21Aux.cayley_graph_commutes hO hJ hJ2 hN hi⟩

theorem native_graph_jetBound_of_operator_bound {O : Set (ComplexVector n)} (hO : IsOpen O)
    {J : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n}
    (hC : ContDiffOn ℝ ∞ (complexCayleyField J) O) (q : ℕ) (ε : ℝ)
    (hBound : ∀ k ≤ q, ∀ x ∈ O, ‖iteratedFDeriv ℝ k (complexCayleyField J) x‖ ≤ ε) :
    L21Aux.JetBound q ε (cayleyCoefficientMatrix J) O := by
  intro k hk x hx i j
  exact (operator_entry_jet_norm_le hO hC hx k i j).trans (hBound k hk x hx)

end Yau.Blueprint.C02Proof
