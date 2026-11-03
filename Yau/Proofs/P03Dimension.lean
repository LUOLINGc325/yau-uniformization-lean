import Yau.Blueprint.Analytic

open scoped Manifold Topology

namespace Yau.NodeProofs.P03Aux

/-- The original manifold data exclude dimension zero: a connected manifold
over the one-point model is a singleton and hence compact. -/
theorem dimension_pos {n : ℕ} (M : ComplexManifold n) : 0 < n := by
  by_contra hn
  have hz : n = 0 := Nat.eq_zero_of_not_pos hn
  subst n
  letI : DiscreteTopology M.Carrier :=
    ChartedSpace.discreteTopology (ComplexVector 0) M.Carrier
  letI : Subsingleton M.Carrier := subsingleton_of_preconnected_totallyDisconnected
  exact noncompact_univ M.Carrier Set.subsingleton_univ.isCompact

theorem dimension_one_le {n : ℕ} (M : ComplexManifold n) : 1 ≤ n :=
  dimension_pos M

theorem no_zero_dimensional_manifold (M : ComplexManifold 0) : False := by
  have h := dimension_pos M
  exact Nat.not_lt_zero 0 h

end Yau.NodeProofs.P03Aux
