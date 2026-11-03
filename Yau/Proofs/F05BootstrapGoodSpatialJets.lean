import Yau.Proofs.F05BootstrapJetCommutation
import Yau.Proofs.F05BootstrapSpatialSymmetry

/-! Good coordinate values and first Hessian slots are identified with
the actual relative spatial jets before any joint higher derivative is used. -/

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic
variable {n : ℕ}

theorem F05_good_gradient_component_eq {ν : Option (RIdx n)} {i : RIdx n} {T α : ℝ}
    (hi : F05GoodLetter ν (some i)) {u : Point n → ℝ} (hu : F05LocalSchauder α ν T u) :
    EqOn (fun z => F05RelD (F05PosSpace ν) u z (realVec i))
      (F05GoodPartial T (some i) u) (F05PosPatch ν T) := by
  have hU := F05_local_schauder_to_relative hu
  intro z hz
  have hLine : ∀ᶠ a : ℝ in 𝓝 0, z.1+a • realVec i ∈ F05PosSpace ν := by
    filter_upwards [F05_good_line_mem_posPatch hi hz] with a ha
    exact ha.1
  exact (F05_good_spatial_partial_eq_relD (T := T) i
    ((hU.2.2.2.2.1 z.2 hz.2 z.1 hz.1).differentiableWithinAt (by norm_num)) hLine).symm

theorem F05_good_hessian_first_eq {ν : Option (RIdx n)} {i : RIdx n} {T α : ℝ}
    (hi : F05GoodLetter ν (some i)) {u : Point n → ℝ} (hu : F05LocalSchauder α ν T u)
    (hiu : F05LocalSchauder α ν T (F05GoodPartial T (some i) u)) :
    EqOn (fun z => F05RelDD (F05PosSpace ν) u z (realVec i))
      (F05RelD (F05PosSpace ν) (F05GoodPartial T (some i) u)) (F05PosPatch ν T) := by
  have hU := F05_local_schauder_to_relative hu
  have hX := F05_posSpace_uniqueDiffOn ν
  have hJets := F05_good_relative_jet_calculus hi hu hiu
  intro z hz
  have hDiff := (((hU.2.2.2.2.1 z.2 hz.2).fderivWithin hX (m := 1)
    (by norm_num)).differentiableOn (by norm_num) z.1 hz.1)
  have hLine : ∀ᶠ a : ℝ in 𝓝 0, z.1+a • realVec i ∈ F05PosSpace ν := by
    filter_upwards [F05_good_line_mem_posPatch hi hz] with a ha
    exact ha.1
  have hPartial := F05_good_spatial_partial_eq_relD (T := T)
    (f := F05RelD (F05PosSpace ν) u) i hDiff hLine
  exact hPartial.symm.trans (hJets.1.2 hz)

end Yau.Proofs.F05Aux
