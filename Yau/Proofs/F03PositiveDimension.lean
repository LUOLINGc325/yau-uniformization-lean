import Yau.Geometry.Basic

/-! The frozen connected noncompact manifold structure excludes dimension zero. -/

noncomputable section

namespace Yau.Proofs.F03Aux
open Yau

theorem complexManifold_zero_false (M : ComplexManifold 0) : False := by
  have : DiscreteTopology M.Carrier :=
    ChartedSpace.discreteTopology (ComplexVector 0) M.Carrier
  have : Subsingleton M.Carrier := subsingleton_of_preconnected_totallyDisconnected
  exact (not_compactSpace_iff.mpr (inferInstance : NoncompactSpace M.Carrier))
    (inferInstance : CompactSpace M.Carrier)

theorem complexManifold_dimension_pos {n : ℕ} (M : ComplexManifold n) : 0 < n := by
  cases n with
  | zero => exact (complexManifold_zero_false M).elim
  | succ n => exact Nat.zero_lt_succ n

end Yau.Proofs.F03Aux
