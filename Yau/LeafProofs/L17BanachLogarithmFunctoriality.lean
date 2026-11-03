import Yau.LeafProofs.L17BanachLogarithmRemainder
import Mathlib.Topology.Algebra.Algebra

noncomputable section
namespace Yau.LeafProofs.L17BanachLogarithmAux

variable {A B : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    [NormedRing B] [NormedAlgebra ℝ B]

theorem logIncrement_map (φ : A →A[ℝ] B) {z : A} (hz : ‖z‖ < 1) :
    φ (logIncrement A z)=logIncrement B (φ z) := by
  calc
    φ (logIncrement A z) = ∑' k : ℕ, φ (logCoefficient k • z^k) :=
      φ.toContinuousLinearMap.map_tsum (logIncrement_summable A hz)
    _ = logIncrement B (φ z) := by
      unfold logIncrement
      apply tsum_congr
      intro k
      simp only [map_smul,map_pow]

theorem logRemainder_map (φ : A →A[ℝ] B) {z : A} (hz : ‖z‖ < 1) :
    φ (logRemainder A z)=logRemainder B (φ z) := by
  simp only [logRemainder,map_sub,logIncrement_map φ hz]

end Yau.LeafProofs.L17BanachLogarithmAux
