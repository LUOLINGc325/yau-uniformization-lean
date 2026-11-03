import Yau.Proofs.Y03CoordinateProjection

/-! Restrict a larger coordinate graph without increasing its inverse-projection bound. -/

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

theorem coordinateSubspace_mono {s t : Finset (Fin n)} (hst : s ⊆ t) :
    coordinateSubspace s ≤ coordinateSubspace t := by
  intro v hv i hi
  exact hv i (fun his => hi (hst his))

def coordinateInclusion {s t : Finset (Fin n)} (hst : s ⊆ t) :
    coordinateSubspace s →L[ℂ] coordinateSubspace t :=
  (Submodule.inclusion (coordinateSubspace_mono hst)).toContinuousLinearMap

theorem coordinateInclusion_opNorm_le {s t : Finset (Fin n)} (hst : s ⊆ t) :
    ‖coordinateInclusion hst‖ ≤ 1 := by
  refine (coordinateInclusion hst).opNorm_le_bound zero_le_one ?_
  intro v
  simp only [one_mul]
  rfl

theorem restrict_coordinate_graph_right_inverse {s t : Finset (Fin n)} (hst : s ⊆ t)
    (T : coordinateSubspace t →L[ℂ] ComplexVector n)
    (hT : (coordinateProjectionOnto t).comp T = ContinuousLinearMap.id ℂ (coordinateSubspace t)) :
    (coordinateProjectionOnto s).comp (T.comp (coordinateInclusion hst)) =
      ContinuousLinearMap.id ℂ (coordinateSubspace s) := by
  apply ContinuousLinearMap.ext
  intro v
  apply Subtype.ext
  have ht : coordinateProjection t (T (coordinateInclusion hst v)) = (v : ComplexVector n) :=
    congrArg Subtype.val (congrArg (fun L : coordinateSubspace t →L[ℂ] coordinateSubspace t =>
      L (coordinateInclusion hst v)) hT)
  calc
    coordinateProjection s (T (coordinateInclusion hst v)) =
        coordinateProjection s (coordinateProjection t (T (coordinateInclusion hst v))) :=
      (congrArg (fun L : ComplexVector n →L[ℂ] ComplexVector n => L (T (coordinateInclusion hst v)))
        (coordinateProjection_comp hst)).symm
    _ = coordinateProjection s (v : ComplexVector n) := congrArg (coordinateProjection s) ht
    _ = (v : ComplexVector n) := coordinateProjection_eq_self v.property

theorem restrict_coordinate_graph_norm_le {s t : Finset (Fin n)} (hst : s ⊆ t)
    (T : coordinateSubspace t →L[ℂ] ComplexVector n) :
    ‖T.comp (coordinateInclusion hst)‖ ≤ ‖T‖ := by
  exact (T.opNorm_comp_le _).trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (coordinateInclusion_opNorm_le hst) (norm_nonneg T))

end Yau.Blueprint.Alignment.Y03Proof
