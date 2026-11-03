import Yau.Proofs.C03ScalarForms

/-! The intrinsic scalar seed tensors have their actual expected
coefficients in the unchanged global source chart. -/

noncomputable section
open Set
open scoped Topology ContDiff Manifold

namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs L14Aux Yau.Proofs.P04Aux BundleDbar
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem scalarSeedTop_coefficient (hn : 1 ≤ n) (f : ComplexVector n → ℂ)
    (z : ComplexVector n) :
    coefficients (r := 1) (CanonicalCoefficients (ComplexEuclideanManifold n hn))
      (scalarSeedTop hn f) (0 : ComplexVector n) z Fin.elim0 0 = f z := by
  have hz : z ∈ localDomain (r := 1) (CanonicalCoefficients (ComplexEuclideanManifold n hn))
      (0 : ComplexVector n) := by rw [coefficient_source_localDomain hn]; trivial
  have H := congrArg (fun v : ComplexVector 1 => v 0)
    (topFormPushforward_coefficients (CanonicalCoefficients (ComplexEuclideanManifold n hn))
      (0 : ComplexVector n) (scalarSeedCoefficient f) z hz)
  exact H.trans (scalarToCoefficient_apply _ _)

theorem scalarSeedDbar_coefficient (hn : 1 ≤ n) (f : ComplexVector n → ℂ)
    (z : ComplexVector n) (i : Fin n) :
    coefficients (r := 1) (CanonicalCoefficients (ComplexEuclideanManifold n hn))
      (scalarSeedDbar hn f) (0 : ComplexVector n) z (fun _ => i) 0 = wirtBar f z (stdVec i) := by
  have hz : z ∈ localDomain (r := 1) (CanonicalCoefficients (ComplexEuclideanManifold n hn))
      (0 : ComplexVector n) := by rw [coefficient_source_localDomain hn]; trivial
  have heq : (fun w => scalarSeedCoefficient f w (0 : Fin 1)) = f := by
    funext w
    exact scalarToCoefficient_apply _ _
  change coefficients (r := 1) (CanonicalCoefficients (ComplexEuclideanManifold n hn))
    (oneFormPushforward _ (0 : ComplexVector n) (modelTopDbar (scalarSeedCoefficient f)))
    (0 : ComplexVector n) z (fun _ => i) 0 = _
  rw [oneFormPushforward_coefficients _ _ _ _ hz]
  change wirtBar (fun w => scalarSeedCoefficient f w (0 : Fin 1)) z (stdVec i) = _
  rw [heq]

end Yau.Proofs.C03Aux
