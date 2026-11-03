import Yau.Proofs.F05BootstrapTimeCommutation
import Yau.Proofs.F05BootstrapTangentCommutation

/-! Both good directions commute with the computed first and second
spatial jets. The differentiability assertions are conclusions of the
rectangle proof, and require only the two displayed Schauder fields. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic
variable {n : ℕ}

theorem F05_good_relative_jet_calculus {ν d : Option (RIdx n)} {T α : ℝ}
    (hd : F05GoodLetter ν d) {u : Point n → ℝ}
    (hu : F05LocalSchauder α ν T u)
    (hw : F05LocalSchauder α ν T (F05GoodPartial T d u)) :
    (F05GoodDiffOn T d (F05RelD (F05PosSpace ν) u) (F05PosPatch ν T) ∧
      EqOn (F05GoodPartial T d (F05RelD (F05PosSpace ν) u))
        (F05RelD (F05PosSpace ν) (F05GoodPartial T d u)) (F05PosPatch ν T)) ∧
    (F05GoodDiffOn T d (F05RelDD (F05PosSpace ν) u) (F05PosPatch ν T) ∧
      EqOn (F05GoodPartial T d (F05RelDD (F05PosSpace ν) u))
        (F05RelDD (F05PosSpace ν) (F05GoodPartial T d u)) (F05PosPatch ν T)) := by
  cases d with
  | none =>
    refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
    · intro z hz
      exact (F05_good_time_spatial_jets hu hw hz).1.differentiableWithinAt
    · intro z hz
      exact (F05_good_time_spatial_jets hu hw hz).1.derivWithin (uniqueDiffOn_Ioc 0 T z.2 hz.2)
    · intro z hz
      exact HasDerivWithinAt.differentiableWithinAt
        (F := Space n →L[ℝ] Space n →L[ℝ] ℝ) (F05_good_time_spatial_jets hu hw hz).2
    · intro z hz
      exact HasDerivWithinAt.derivWithin (F := Space n →L[ℝ] Space n →L[ℝ] ℝ)
        (F05_good_time_spatial_jets hu hw hz).2 (uniqueDiffOn_Ioc 0 T z.2 hz.2)
  | some k =>
    refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
    · intro z hz
      exact (F05_good_tangent_spatial_jets hd hu hw hz).1.differentiableAt
    · intro z hz
      exact (F05_good_tangent_spatial_jets hd hu hw hz).1.deriv
    · intro z hz
      exact HasDerivAt.differentiableAt (F := Space n →L[ℝ] Space n →L[ℝ] ℝ)
        (F05_good_tangent_spatial_jets hd hu hw hz).2
    · intro z hz
      exact HasDerivAt.deriv (F := Space n →L[ℝ] Space n →L[ℝ] ℝ)
        (F05_good_tangent_spatial_jets hd hu hw hz).2

end Yau.Proofs.F05Aux
