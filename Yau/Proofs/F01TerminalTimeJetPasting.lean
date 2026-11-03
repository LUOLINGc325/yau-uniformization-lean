import spec.CHAIN.CONTRACTS
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-! Actual interior time derivatives with genuine endpoint limits
give the original one-sided terminal derivative. Matching left and
right jets then give a genuine two-sided time derivative. -/
noncomputable section
open Set Filter
open scoped Topology
namespace Yau.NodeProofs.F01Aux
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem terminal_left_time_jet
    (f P : ℝ → F) {l T : ℝ} (hlT : l < T)
    (hCont : ContinuousWithinAt f (Ioo l T) T)
    (hJet : ∀ s ∈ Ioo l T, HasDerivAt f (P s) s)
    (hP : Tendsto P (𝓝[<] T) (𝓝 (P T))) :
    HasDerivWithinAt f (P T) (Iic T) T := by
  have hInterval : Ioo l T ∈ 𝓝[<] T := Ioo_mem_nhdsLT hlT
  have hDiff : DifferentiableOn ℝ f (Ioo l T) :=
    fun s hs => (hJet s hs).differentiableAt.differentiableWithinAt
  have hEq : (fun s => deriv f s) =ᶠ[𝓝[<] T] P := by
    filter_upwards [hInterval] with s hs
    exact (hJet s hs).deriv
  apply hasDerivWithinAt_Iic_of_tendsto_deriv hDiff hCont hInterval
  exact hP.congr' hEq.symm

theorem time_jet_of_matching_closed_faces
    (f : ℝ → F) (v : F) (T : ℝ)
    (hLeft : HasDerivWithinAt f v (Iic T) T)
    (hRight : HasDerivWithinAt f v (Ici T) T) : HasDerivAt f v T := by
  have hh := hLeft.union hRight
  simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hh

end Yau.NodeProofs.F01Aux
