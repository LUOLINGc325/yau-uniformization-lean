import Yau.Proofs.F05EventualNonlinearSchauderLimit
import Yau.Proofs.F05BootstrapRelativeRestriction

/-! Actual relative jets identify the same nonlinear equation after
restriction to a smaller genuine receiving cylinder. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport
variable {n : ℕ}

theorem F05_relative_nonlinear_equation_restrict (ν : Option (RIdx n))
    {r R s t S T : ℝ} (hr : 0 < r) (hR : 0 < R) (hrR : r ≤ R)
    (hst : s < t) (hSs : S ≤ s) (htT : t ≤ T)
    {a : Point n → Mat n} {b : Point n → RIdx n → ℝ} {F u : Point n → ℝ}
    (hu : F05RelC2 (region ν R) (Icc S T) u)
    (hEq : F05RelativeNonlinearEquation ν R S T a b F u) :
    F05RelativeNonlinearEquation ν r s t a b F u := by
  have hSpace := F05_region_mono hrR (k := ν)
  have hTime : Icc s t ⊆ Icc S T := fun z hz => ⟨hSs.trans hz.1,hz.2.trans htT⟩
  intro z hz
  have hJets := F05_relative_restriction_jets (F05_region_uniqueDiffOn ν hR)
    (F05_region_uniqueDiffOn ν hr) (uniqueDiffOn_Icc hst) hSpace hTime hu hz
  rw [hJets.1,hJets.2.1,hJets.2.2]
  exact hEq z ⟨hSpace hz.1,hTime hz.2⟩

end Yau.Proofs.F05Aux
