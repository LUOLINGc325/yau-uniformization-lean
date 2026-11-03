import Yau.Proofs.D02CotangentCompact

/-! The zero-dimensional branch of the original noncompact connected
manifold hypotheses is impossible. No dimension hypothesis is added to D02. -/

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau

/-- A connected zero-dimensional manifold is discrete and a singleton,
contradicting the original noncompactness requirement. -/
theorem no_zero_dimensional_complexManifold (M : ComplexManifold 0) : False := by
  letI : DiscreteTopology M.Carrier :=
    ChartedSpace.discreteTopology (H := ComplexVector 0) (M := M.Carrier)
  letI : Subsingleton M.Carrier := subsingleton_of_preconnected_totallyDisconnected
  exact noncompact_univ M.Carrier (Set.toFinite Set.univ).isCompact

theorem complexDimension_pos {n : ℕ} (M : ComplexManifold n) : 0 < n := by
  cases n with
  | zero => exact (no_zero_dimensional_complexManifold M).elim
  | succ n => exact Nat.succ_pos n

end Yau.NodeProofs.D02Aux
