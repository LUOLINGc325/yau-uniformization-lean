import Yau.Proofs.P04CompactQuadratic

noncomputable section
open Set
open scoped Topology InnerProductSpace Matrix ComplexOrder

namespace Yau.Proofs.P04Aux
open Yau
variable {n : ℕ}

/-- A continuous compact matrix family has one quadratic bound, with no
pointwise constant or eigenvector chosen as an additional input. -/
theorem compact_matrix_uniform_quadratic_bound {α : Type*} [TopologicalSpace α] [CompactSpace α]
    (A : α → Matrix (Fin n) (Fin n) ℂ) (hA : Continuous A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a v, |matrixQuadratic (A a) v| ≤ C*‖v‖^2 := by
  let K : Set (α × ComplexVector n) := univ ×ˢ Metric.sphere 0 1
  have hK : IsCompact K := isCompact_univ.prod (isCompact_sphere 0 1)
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn (matrixQuadratic_continuous hA).continuousOn
  refine ⟨max B 0,le_max_right _ _,fun a v => ?_⟩
  by_cases hv : v=0
  · simp [hv,matrixQuadratic,Matrix.mulVec,dotProduct]
  · have hn : ‖‖v‖⁻¹ • v‖=1 := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
    have hmem : (a,‖v‖⁻¹ • v) ∈ K :=
      ⟨mem_univ a,by simpa only [Metric.mem_sphere,dist_zero_right] using hn⟩
    have HH := hB _ hmem
    change ‖matrixQuadratic (A a) (‖v‖⁻¹ • v)‖ ≤ B at HH
    rw [matrixQuadratic_real_smul,Real.norm_eq_abs,abs_mul,
      abs_of_nonneg (sq_nonneg ‖v‖⁻¹)] at HH
    have Hmul := mul_le_mul_of_nonneg_right HH (sq_nonneg ‖v‖)
    have hcancel : (‖v‖⁻¹)^2*‖v‖^2=1 := by
      rw [← mul_pow,inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv),one_pow]
    have heq : (‖v‖⁻¹)^2*|matrixQuadratic (A a) v| *‖v‖^2 = |matrixQuadratic (A a) v| := by
      calc
        _ = |matrixQuadratic (A a) v| *((‖v‖⁻¹)^2*‖v‖^2) := by ring
        _ = _ := by rw [hcancel,mul_one]
    rw [heq] at Hmul
    exact Hmul.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg ‖v‖))

end Yau.Proofs.P04Aux
