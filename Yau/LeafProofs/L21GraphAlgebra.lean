import spec.CHAIN.LeafCandidates

/-! Algebraic identities for the original real-coordinate Nijenhuis tensor.
The sign convention is the one in `LeafCandidates.bracket`. -/

open scoped ContDiff
noncomputable section

namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}
abbrev X (n : ℕ) := Yau.ComplexVector n

theorem fderiv_structure_apply_const
    {J : X n → X n →L[ℝ] X n} {x : X n}
    (hJ : DifferentiableAt ℝ J x) (v : X n) :
    fderiv ℝ (fun y => J y v) x = (fderiv ℝ J x).flip v := by
  simpa using fderiv_clm_apply hJ (differentiableAt_const v)

/-- Literal expansion of the frozen, constant-vector definition. -/
theorem nijenhuis_eq_tensor
    {J : X n → X n →L[ℝ] X n} {x : X n}
    (hJ : DifferentiableAt ℝ J x) (v w : X n) :
    Yau.LeafCandidates.nijenhuis J x v w =
      fderiv ℝ J x (J x v) w - fderiv ℝ J x (J x w) v +
        J x (fderiv ℝ J x w v) - J x (fderiv ℝ J x v w) := by
  simp only [Yau.LeafCandidates.nijenhuis, Yau.LeafCandidates.bracket,
    fderiv_structure_apply_const hJ, fderiv_const_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.zero_apply,
    zero_sub, sub_zero, map_neg, sub_neg_eq_add]

/-- Tensoriality: derivatives of the two auxiliary vector fields cancel.
This is the bridge from the original constant-vector input to eigenfields. -/
theorem nijenhuis_vector_fields
    {J : X n → X n →L[ℝ] X n} {V W : X n → X n} {x : X n}
    (hJ : DifferentiableAt ℝ J x)
    (hV : DifferentiableAt ℝ V x) (hW : DifferentiableAt ℝ W x)
    (hJ2 : ∀ v, J x (J x v) = -v) :
    Yau.LeafCandidates.nijenhuis J x (V x) (W x) =
      Yau.LeafCandidates.bracket (fun y => J y (V y)) (fun y => J y (W y)) x -
        J x (Yau.LeafCandidates.bracket (fun y => J y (V y)) W x) -
        J x (Yau.LeafCandidates.bracket V (fun y => J y (W y)) x) -
        Yau.LeafCandidates.bracket V W x := by
  rw [nijenhuis_eq_tensor hJ]
  simp only [Yau.LeafCandidates.bracket, fderiv_clm_apply hJ hV,
    fderiv_clm_apply hJ hW, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    map_sub, map_add, hJ2]
  abel

end Yau.LeafProofs.L21Aux
