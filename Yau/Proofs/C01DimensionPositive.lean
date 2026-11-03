import spec.CHAIN.CONTRACTS

/-! The original manifold data rule out dimension zero internally.
This is the elementary topological argument of canonical L12:385–392,
proved here without importing its geometric calculus cluster. -/

noncomputable section

namespace Yau.NodeProofs.C01Aux

open Yau

theorem original_manifold_dimension_pos {n : ℕ} (M : ComplexManifold n) : 0 < n := by
  by_contra hn
  have hn0 := Nat.eq_zero_of_not_pos hn
  subst n
  letI : DiscreteTopology M.Carrier :=
    ChartedSpace.discreteTopology (ComplexVector 0) M.Carrier
  letI : Subsingleton M.Carrier := subsingleton_of_preconnected_totallyDisconnected
  exact (not_compactSpace_iff.mpr (inferInstance : NoncompactSpace M.Carrier))
    (inferInstance : CompactSpace M.Carrier)

end Yau.NodeProofs.C01Aux
