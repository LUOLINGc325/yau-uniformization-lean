import Yau.LeafProofs.L16LocalSmoothRepresentative
import Yau.LeafProofs.L16WeakToClassical

open MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Interior
open Yau.Parabolic Yau.ParabolicCandidates
open Yau.LeafProofs.L16Aux

/-- The exact frozen homogeneous weak interior smoothing component. -/
theorem homogeneousInteriorSmoothing : HomogeneousInteriorSmoothing := by
  intro n _hn O l r lam upper hO _hlr a b u G hSmooth hEll hE hEq
  have hQ : IsOpen (O ×ˢ Set.Ioo l r) := hO.prod isOpen_Ioo
  rw [productVolume_eq_restrict]
  apply smooth_solution_of_local_ae (f := fun _ => 0) hQ
  intro p hp
  have hK : IsCompact ({p} : Set (Point n)) := isCompact_singleton
  obtain ⟨W,hW,hpW,hWQ,hWC⟩ := exists_open_between_and_isCompact_closure hK hQ
    (Set.singleton_subset_iff.mpr hp)
  have hpW' : p ∈ W := hpW (Set.mem_singleton p)
  obtain ⟨v,hv,hAE⟩ := localEnergy_homogeneous_local_smooth_representative
    hO hSmooth hEll hE hEq hW hWC hWQ
  have hClass := (localEnergy_weakEquation_smooth_representative_classical
    hO hSmooth hE hEq hW hWC hWQ hv hAE).2
  exact ⟨W,hW,hpW',subset_closure.trans hWQ,v,hv.contDiffOn,hAE,hClass⟩

end Yau.LeafProofs.L16Interior
