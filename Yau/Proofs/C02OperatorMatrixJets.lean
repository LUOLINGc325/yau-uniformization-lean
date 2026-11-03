import Yau.Proofs.C02UniformCayleyJets

/-! Each graph-matrix entry is a fixed contraction of the actual Cayley
operator. The contraction has norm at most one in every dimension. -/

noncomputable section
open Set
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
variable {n : ℕ}
local instance op_entry_group : NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance op_entry_space : NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance

def complexOperatorEntry (i k : Fin n) :
    (ComplexVector n →L[ℝ] ComplexVector n) →L[ℝ] ℂ :=
  ((EuclideanSpace.proj k : ComplexVector n →L[ℂ] ℂ).restrictScalars ℝ).comp
    (ContinuousLinearMap.apply ℝ (ComplexVector n) (stdVec i))

theorem complexOperatorEntry_norm_le_one (i k : Fin n) : ‖complexOperatorEntry i k‖ ≤ 1 := by
  apply (complexOperatorEntry i k).opNorm_le_bound (by norm_num)
  intro C
  have hStd : ‖stdVec i‖ = 1 := EuclideanSpace.orthonormal_single.norm_eq_one i
  change ‖C (stdVec i) k‖ ≤ 1 * ‖C‖
  simpa only [one_mul, hStd, mul_one] using
    (PiLp.norm_apply_le (C (stdVec i)) k).trans (C.le_opNorm (stdVec i))

def cayleyCoefficientMatrix
    (J : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n)
    (x : ComplexVector n) : Matrix (Fin n) (Fin n) ℂ :=
  fun i k => complexCayleyField J x (stdVec i) k

theorem operator_entry_jet_norm_le {O : Set (ComplexVector n)} (hO : IsOpen O)
    {C : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n}
    (hC : ContDiffOn ℝ ∞ C O) {x : ComplexVector n} (hx : x ∈ O)
    (m : ℕ) (i k : Fin n) :
    ‖iteratedFDeriv ℝ m (fun y => C y (stdVec i) k) x‖ ≤ ‖iteratedFDeriv ℝ m C x‖ := by
  let L := complexOperatorEntry i k
  have hh := L.norm_iteratedFDeriv_comp_left
    ((hC x hx).contDiffAt (hO.mem_nhds hx)) (show (m : ℕ∞ω) ≤ ∞ by simp)
  exact hh.trans (by simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (complexOperatorEntry_norm_le_one i k) (norm_nonneg _))

theorem cayleyCoefficientMatrix_zero
    {J : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n}
    (hJ : J 0 = Yau.LeafProofs.L12Aux.complexStructureCLM n) : cayleyCoefficientMatrix J 0 = 0 := by
  ext i k
  simp [cayleyCoefficientMatrix, complexCayleyField, hJ]

end Yau.Blueprint.C02Proof
