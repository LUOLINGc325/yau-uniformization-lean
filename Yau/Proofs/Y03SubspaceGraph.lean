import Yau.Proofs.Y03NestedGraph

/-! Specialize the graph extension to a Hilbert subspace while retaining its inherited structures. -/

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

theorem exists_subspace_graph_extension (S A V : Submodule ℂ H) (p : H →L[ℂ] S)
    (T : S →L[ℂ] H) {C : ℝ} (hC : 0 ≤ C)
    (hA : A ≤ V) (hpT : p.comp T = ContinuousLinearMap.id ℂ S)
    (hT : LinearMap.range T.toLinearMap ≤ V)
    (hbound : ∀ a : A, ‖a‖ ≤ C * ‖p a‖) :
    ∃ L : S →L[ℂ] H, p.comp L = ContinuousLinearMap.id ℂ S ∧
      A ≤ LinearMap.range L.toLinearMap ∧ LinearMap.range L.toLinearMap ≤ V ∧
      ‖L‖ ≤ C + ‖T‖ := by
  exact exists_nested_graph_extension A V p T hC hA hpT hT hbound

end Yau.Blueprint.Alignment.Y03Proof
