import Yau.Blueprint.Alignment

/-! The explicit additive extension of one required graph inside the next graph. -/

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

variable {𝕜 H E Y : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup H] [NormedSpace 𝕜 H]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

def nestedGraphLift (R : Y →L[𝕜] H) (T : E →L[𝕜] H)
    (C : Y →L[𝕜] E) (P : E →L[𝕜] Y) : E →L[𝕜] H :=
  R.comp P + T.comp (ContinuousLinearMap.id 𝕜 E - C.comp P)

theorem nestedGraphLift_right_inverse (R : Y →L[𝕜] H) (T : E →L[𝕜] H)
    (C : Y →L[𝕜] E) (P : E →L[𝕜] Y) (π : H →L[𝕜] E)
    (hR : π.comp R = C) (hT : π.comp T = ContinuousLinearMap.id 𝕜 E) :
    π.comp (nestedGraphLift R T C P) = ContinuousLinearMap.id 𝕜 E := by
  ext e
  have hRe (y : Y) : π (R y) = C y := congrArg (fun L : Y →L[𝕜] E => L y) hR
  have hTe (x : E) : π (T x) = x := congrArg (fun L : E →L[𝕜] E => L x) hT
  simp only [nestedGraphLift, ContinuousLinearMap.comp_apply, add_apply,
    sub_apply, ContinuousLinearMap.id_apply, map_add, hRe, hTe]
  abel

theorem nestedGraphLift_extends (R : Y →L[𝕜] H) (T : E →L[𝕜] H)
    (C : Y →L[𝕜] E) (P : E →L[𝕜] Y)
    (hPC : P.comp C = ContinuousLinearMap.id 𝕜 Y) :
    (nestedGraphLift R T C P).comp C = R := by
  ext y
  have hPCe : P (C y) = y := congrArg (fun L : Y →L[𝕜] Y => L y) hPC
  simp only [nestedGraphLift, ContinuousLinearMap.comp_apply, add_apply,
    sub_apply, ContinuousLinearMap.id_apply, hPCe, sub_self, map_zero, add_zero]

theorem nestedGraphLift_range_le (R : Y →L[𝕜] H) (T : E →L[𝕜] H)
    (C : Y →L[𝕜] E) (P : E →L[𝕜] Y) (V : Submodule 𝕜 H)
    (hR : LinearMap.range R.toLinearMap ≤ V) (hT : LinearMap.range T.toLinearMap ≤ V) :
    LinearMap.range (nestedGraphLift R T C P).toLinearMap ≤ V := by
  rintro z ⟨e, rfl⟩
  exact V.add_mem (hR ⟨P e, rfl⟩) (hT ⟨e - C (P e), rfl⟩)

theorem nestedGraphLift_norm_le (R : Y →L[𝕜] H) (T : E →L[𝕜] H)
    (C : Y →L[𝕜] E) (P : E →L[𝕜] Y)
    (hP : ‖P‖ ≤ 1) (hperp : ‖ContinuousLinearMap.id 𝕜 E - C.comp P‖ ≤ 1) :
    ‖nestedGraphLift R T C P‖ ≤ ‖R‖ + ‖T‖ := by
  unfold nestedGraphLift
  calc
    _ ≤ ‖R.comp P‖ + ‖T.comp (ContinuousLinearMap.id 𝕜 E - C.comp P)‖ := norm_add_le _ _
    _ ≤ ‖R‖ * ‖P‖ + ‖T‖ * ‖ContinuousLinearMap.id 𝕜 E - C.comp P‖ :=
      add_le_add (R.opNorm_comp_le P) (T.opNorm_comp_le _)
    _ ≤ ‖R‖ * 1 + ‖T‖ * 1 := add_le_add
      (mul_le_mul_of_nonneg_left hP (norm_nonneg R))
      (mul_le_mul_of_nonneg_left hperp (norm_nonneg T))
    _ = _ := by ring

end Yau.Blueprint.Alignment.Y03Proof
