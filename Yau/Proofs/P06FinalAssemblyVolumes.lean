import Yau.Blueprint.HodgeContracts
import Yau.LeafProofs.L12

/-! The original Riemannian chart law fixes the volume, so one original
cutoff construction supplies the same construction for every allowed volume. -/
noncomputable section
open MeasureTheory

namespace Yau.NodeProofs.P06Aux.FinalAssembly
open Yau Yau.Blueprint
variable {n : ℕ} {M : ComplexManifold n}

theorem cutoffConstruction_all_volumes (g : HermitianField M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g μ)
    (hc : HodgeCutoffConstruction g μ) :
    ∀ ν, IsRiemannianVolume g ν → HodgeCutoffConstruction g ν := by
  intro ν hν
  rw [Yau.LeafProofs.L12Aux.riemannianVolume_unique g hν hμ]
  exact hc

end Yau.NodeProofs.P06Aux.FinalAssembly
