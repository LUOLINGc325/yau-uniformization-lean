import Yau.Proofs.E02ProductDomain
import Yau.Proofs.E02WeightedColumnLevi

open Matrix Set
open scoped Topology Matrix ComplexOrder
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

/-- The fixed projector's diagonal preserves the original contact
normalization on every tuple in the ENTIRE equality orbit. -/
theorem contactOrbit_qform_one {n m : ℕ}
    (a : ComplexVector n × ℝ) (α : Fin m → ℝ) (hα : ∀ j, 0 < α j)
    (η₀ : Fin m → ComplexVector n) (B : Herm n) (hB : B.PosDef)
    (hGram₀ : weightedColumns α η₀*(weightedColumns α η₀)ᴴ = B⁻¹)
    (hq₀ : ∀ j, qform B (η₀ j) = 1)
    (Q : ProductPoint n m)
    (hQ : Q ∈ contactOrbit a α B (rowProjector (weightedColumns α η₀))) :
    ∀ j, qform B (Q.2.2 j) = 1 := by
  have hProj : rowProjector (weightedColumns α Q.2.2) = rowProjector (weightedColumns α η₀) := by
    change (weightedColumns α Q.2.2)ᴴ*
      (weightedColumns α Q.2.2*(weightedColumns α Q.2.2)ᴴ)⁻¹*
        weightedColumns α Q.2.2 = _
    rw [hQ.2.1,Matrix.nonsing_inv_nonsing_inv _ (hB.isUnit.map Matrix.detMonoidHom)]
    exact hQ.2.2
  intro j
  have hDiag := congrArg (fun P : Herm m => (P j j).re) hProj
  rw [rowProjector_weighted_diag α Q.2.2 (fun i => (hα i).le),
    rowProjector_weighted_diag α η₀ (fun i => (hα i).le),hQ.2.1,hGram₀,
    Matrix.nonsing_inv_nonsing_inv _ (hB.isUnit.map Matrix.detMonoidHom),hq₀ j] at hDiag
  exact mul_left_cancel₀ (hα j).ne' hDiag

end Yau.NodeProofs.E02Aux
