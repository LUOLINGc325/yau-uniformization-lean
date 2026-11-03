import Yau.LeafProofs.L05InverseRange

noncomputable section

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic Yau.ParabolicCandidates

theorem slopeSet_tracePair_bounds {n : ℕ} {ell L : ℝ} {A P : Sym n}
    (hA : A ∈ slopeSet n ell L) (hP : (P : Mat n).PosSemidef) :
    ell*Matrix.trace (P : Mat n) ≤ tracePair A P ∧
      tracePair A P ≤ L*Matrix.trace (P : Mat n) := by
  have hl := posSemidef_trace_mul_nonneg hA.1 hP
  have hu := posSemidef_trace_mul_nonneg hA.2 hP
  simp only [Matrix.sub_mul,Matrix.smul_mul,Matrix.one_mul,Matrix.trace_sub,
    Matrix.trace_smul,smul_eq_mul] at hl hu
  unfold tracePair
  constructor <;> linarith only [hl,hu]

theorem rankOne_coe {n : ℕ} (v : RIdx n → ℝ) :
    (rankOne v : Mat n)=fun i j => v i*v j := by
  apply IsSelfAdjoint.coe_selfAdjointPart_apply
  apply Matrix.isHermitian_iff_isSelfAdjoint.mp
  apply Matrix.IsHermitian.ext
  intro i j
  change v j*v i=v i*v j
  exact mul_comm _ _

theorem rankOne_posSemidef {n : ℕ} (v : RIdx n → ℝ) :
    (rankOne v : Mat n).PosSemidef := by
  rw [rankOne_coe]
  convert! Matrix.posSemidef_vecMulVec_self_star v using 1

theorem rankOne_trace {n : ℕ} (v : RIdx n → ℝ) :
    Matrix.trace (rankOne v : Mat n)=∑ i, (v i)^2 := by
  rw [rankOne_coe]
  change (∑ i, v i*v i)=∑ i, (v i)^2
  simp only [pow_two]

theorem logDetReal_rankOne_elliptic {n : ℕ} {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) {A : Sym n} (hA : A ∈ slopeSet n ell L)
    (v : RIdx n → ℝ) :
    ((1/2:ℝ)*L⁻¹)*(∑ i, (v i)^2) ≤ fderiv ℝ (@logDetReal n) A (rankOne v) ∧
      fderiv ℝ (@logDetReal n) A (rankOne v) ≤ ((1/2:ℝ)*ell⁻¹)*(∑ i, (v i)^2) := by
  have hh := slopeSet_tracePair_bounds (symInverse_mem_slopeSet hell hL hA) (rankOne_posSemidef v)
  rw [rankOne_trace] at hh
  unfold tracePair at hh
  change L⁻¹*(∑ i, (v i)^2) ≤ Matrix.trace ((A : Mat n)⁻¹*(rankOne v : Mat n)) ∧
    Matrix.trace ((A : Mat n)⁻¹*(rankOne v : Mat n)) ≤ ell⁻¹*(∑ i, (v i)^2) at hh
  rw [logDetReal_fderiv (slopeSet_subset_logDetDomain hell hA)]
  constructor <;> linarith only [hh.1,hh.2]

end Yau.LeafProofs.L05Aux
