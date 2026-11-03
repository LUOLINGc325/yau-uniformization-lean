import Yau.Proofs.Y03ProjectedInverse

/-! Build the required graph extension on the actual projected image with an additive norm bound. -/

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

variable {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem exists_nested_graph_extension (A V : Submodule ℂ H) (p : H →L[ℂ] E)
    (T : E →L[ℂ] H) {C : ℝ} (hC : 0 ≤ C)
    (hA : A ≤ V) (hpT : p.comp T = ContinuousLinearMap.id ℂ E)
    (hT : LinearMap.range T.toLinearMap ≤ V)
    (hbound : ∀ a : A, ‖a‖ ≤ C * ‖p a‖) :
    ∃ L : E →L[ℂ] H, p.comp L = ContinuousLinearMap.id ℂ E ∧
      A ≤ LinearMap.range L.toLinearMap ∧ LinearMap.range L.toLinearMap ≤ V ∧
      ‖L‖ ≤ C + ‖T‖ := by
  obtain ⟨R, hpR, hrangeR, hnormR⟩ := exists_projected_inverse A p hC hbound
  let Y := LinearMap.range (p.toLinearMap.comp A.subtype)
  let P := Y.orthogonalProjectionOnto
  let C₀ := Y.subtypeL
  have hPC : P.comp C₀ = ContinuousLinearMap.id ℂ Y := by
    apply ContinuousLinearMap.ext
    intro y
    exact Y.orthogonalProjectionOnto_mem_subspace_eq_self y
  have hP : ‖P‖ ≤ 1 := Y.orthogonalProjectionOnto_norm_le
  have hperp : ‖ContinuousLinearMap.id ℂ E - C₀.comp P‖ ≤ 1 := by
    change ‖ContinuousLinearMap.id ℂ E - Y.starProjection‖ ≤ 1
    rw [← Y.starProjection_orthogonal]
    exact Yᗮ.starProjection_norm_le
  let L := nestedGraphLift R T C₀ P
  have hext : L.comp C₀ = R := nestedGraphLift_extends R T C₀ P hPC
  refine ⟨L, nestedGraphLift_right_inverse R T C₀ P p hpR hpT, ?_, ?_, ?_⟩
  · intro a ha
    have hRa : a ∈ LinearMap.range R.toLinearMap := by rw [hrangeR]; exact ha
    obtain ⟨y, hy⟩ := hRa
    refine ⟨C₀ y, ?_⟩
    exact (congrArg (fun F : Y →L[ℂ] H => F y) hext).trans hy
  · apply nestedGraphLift_range_le R T C₀ P V _ hT
    rw [hrangeR]
    exact hA
  · exact (nestedGraphLift_norm_le R T C₀ P hP hperp).trans (add_le_add hnormR le_rfl)

end Yau.Blueprint.Alignment.Y03Proof
