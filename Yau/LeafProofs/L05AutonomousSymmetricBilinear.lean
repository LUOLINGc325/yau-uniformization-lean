import Yau.Blueprint.ParabolicSpaces
import Mathlib.Analysis.Normed.Operator.Bilinear

noncomputable section
open scoped Topology
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux

/-- Symmetric continuous real bilinear forms are determined by their values
on unit diagonals, including the zero-dimensional real space. -/
theorem auto_symmetric_bilinear_eq_of_unit_diagonal {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (B C : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v z, B v z=B z v) (hC : ∀ v z, C v z=C z v)
    (hUnit : ∀ v : E, ‖v‖=1 → B v v=C v v) : B=C := by
  have hDiag (v : E) : B v v=C v v := by
    by_cases hv : v=0
    · simp [hv]
    have hnorm : ‖v‖≠0 := norm_ne_zero_iff.mpr hv
    have hu : ‖‖v‖⁻¹ • v‖=1 := by
      rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg v),inv_mul_cancel₀ hnorm]
    have h := congrArg (fun r : ℝ => ‖v‖*(‖v‖*r)) (hUnit (‖v‖⁻¹ • v) hu)
    simp only [map_smul,_root_.smul_apply,smul_eq_mul] at h
    field_simp [hnorm] at h
    exact h
  ext v z
  have h := hDiag (v+z)
  simp only [map_add,_root_.add_apply] at h
  rw [hB z v,hC z v,hDiag v,hDiag z] at h
  linarith only [h]

end Yau.LeafProofs.L05AutonomousAux
