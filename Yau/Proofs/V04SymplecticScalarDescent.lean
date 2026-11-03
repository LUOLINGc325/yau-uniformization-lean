import Yau.Proofs.V04PositiveReplacementAlgebra
import Yau.Proofs.V04CotangentSymplectic
import Yau.Proofs.V03BoundaryHermitian
import Yau.Proofs.V03BoundaryTensorTransport

/-! The actual symplectic Hessian scalar is independent of a valid fixed
cotangent chart. Only the genuine symplectic transition is used. -/

open scoped Matrix Topology ContDiff ComplexOrder Manifold
noncomputable section
namespace Yau.Blueprint.V04Proof.ClockErrorAux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof Yau.Blueprint.V04Proof
open PositiveReplacementAux

variable {n q : ℕ} {X : KahlerManifold n}

theorem frameBivector_of_symplectic (K : CotangentMatrix n) (hK : IsUnit K.det)
    (hJ : K * canonicalBivector * Kᵀ = canonicalBivector) :
    frameBivector K = canonicalBivector := by
  have hleft := Matrix.nonsing_inv_mul K hK
  have htrans : Kᵀ * K⁻¹ᵀ = 1 := by
    rw [← Matrix.transpose_mul, hleft, Matrix.transpose_one]
  calc
    frameBivector K = K⁻¹ * (K * canonicalBivector * Kᵀ) * K⁻¹ᵀ := by
      rw [hJ]
      rfl
    _ = (K⁻¹ * K) * canonicalBivector * (Kᵀ * K⁻¹ᵀ) := by simp only [Matrix.mul_assoc]
    _ = canonicalBivector := by rw [hleft, htrans, Matrix.one_mul, Matrix.mul_one]

theorem symplecticP_congruence (A K : CotangentMatrix n) (hA : A.IsHermitian)
    (hK : IsUnit K.det) (hJ : K * canonicalBivector * Kᵀ = canonicalBivector) :
    symplecticP (Kᴴ * A * K) = symplecticP A := by
  have heq := bivectorCost_congruence A canonicalBivector K hK
  change bivectorCost (Kᴴ * A * K) (frameBivector K) = bivectorCost A canonicalBivector at heq
  rw [frameBivector_of_symplectic K hK hJ,
    bivectorCost_canonical _ (Matrix.isHermitian_conjTranspose_mul_mul K hA),
    bivectorCost_canonical _ hA] at heq
  exact heq

theorem boundarySymplectic_fixed_chart {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F)
    (θ : ℝ) (x : X.manifold.Carrier) (hy : F.f (circlePoint θ) ∈ cotangentSource x) :
    symplecticP (boundaryHessian d j F (circlePoint θ)) =
      symplecticP (leviMatrix (fun z => let y := cotangentChartInv x z
        dualNorm (d.h (discTime F (circlePoint θ))) y.1 y.2 +
          wallCost d j y (discTime F (circlePoint θ)) F.s)
            (cotangentChart x (F.f (circlePoint θ))) cotangentDir) := by
  let y := F.f (circlePoint θ)
  have hself : y ∈ cotangentSource y.1 := mem_extChartAt_source _
  have hround := cotangentChart_left_inv x hy
  have hz := cotangentChart_mapsTo x hy
  have hregion := hF.2.2.2.2.2.2.2.1 θ
  have ht := admissible_discTime_mem hF (circlePoint_mem_closedBall θ)
  have hcost := boundaryCost_fixed_chart_contDiffAt hd j x hz
    ⟨ht.1.le, ht.2.le.trans hd.2.1.le⟩ F.s
    (by rw [hround]; exact (deltaBase_pos (setup_wallProfiles hd) (setup_index_bounds hd j).1 hregion.1).ne')
    (by rw [hround]; exact (deltaFiber_pos (setup_wallProfiles hd) (setup_index_bounds hd j).2 hregion.2).ne')
  have hH := spatialHessian_in_fixed_chart
    (fun u => dualNorm (d.h (discTime F (circlePoint θ))) u.1 u.2 +
      wallCost d j u (discTime F (circlePoint θ)) F.s) x hy hcost
  have hK : IsUnit (cotangentTransition y.1 x y).det :=
    (Matrix.mulVec_injective_iff_isUnit.mp
      (cotangentTransition_mulVec_injective y.1 x y hself hy)).map Matrix.detMonoidHom
  change symplecticP (spatialHessian _ y) = _
  rw [hH]
  exact symplecticP_congruence _ _ (leviMatrix_isHermitian hcost cotangentDir) hK
    (cotangentTransition_preserves_canonicalBivector y.1 x y hself hy)

end Yau.Blueprint.V04Proof.ClockErrorAux
