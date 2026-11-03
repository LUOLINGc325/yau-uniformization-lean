import Yau.LeafProofs.L17HermitianMatrixAssemblyCoordinates
import Yau.LeafProofs.L14MatrixIMS

noncomputable section
open scoped Manifold Matrix ComplexOrder

namespace Yau.LeafProofs.L17HermitianMatrixAssemblyAux

variable {n : ℕ} {M : ComplexManifold n}

/-- Positive matrices in each point's canonical differential frame define an actual field. -/
def hermitianFieldOfMatrices (H : M.Carrier → Matrix (Fin n) (Fin n) ℂ)
    (hH : ∀ x, (H x).PosDef) : HermitianField M := fun x =>
  pullbackHermitianInnerProduct (L14Aux.matrixHermitianMetric (H x) (hH x))
    (canonicalRawTangentCoordinates x).toLinearMap (canonicalRawTangentCoordinates x).injective

/-- The constructor uses the actual chart differential, not a supplied frame. -/
theorem hermitianFieldOfMatrices_apply (H : M.Carrier → Matrix (Fin n) (Fin n) ℂ)
    (hH : ∀ x, (H x).PosDef) (x : M.Carrier) (u v : TangentVector M x) :
    (hermitianFieldOfMatrices H hH x).toFun u v =
      star (WithLp.ofLp (tangentCoords x x u)) ⬝ᵥ
        ((H x) *ᵥ WithLp.ofLp (tangentCoords x x v)) := rfl

/-- The Gram matrix of the constructed field is precisely the prescribed matrix. -/
theorem gMat_hermitianFieldOfMatrices (H : M.Carrier → Matrix (Fin n) (Fin n) ℂ)
    (hH : ∀ x, (H x).PosDef) (x : M.Carrier) :
    gMat (hermitianFieldOfMatrices H hH) x = H x := by
  classical
  have he : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  ext i j
  change (hermitianFieldOfMatrices H hH (chartInv x (chartPt x x))).toFun
    (chartVec x (chartInv x (chartPt x x)) (stdVec i))
    (chartVec x (chartInv x (chartPt x x)) (stdVec j)) = H x i j
  rw [he, hermitianFieldOfMatrices_apply,
    L12Aux.tangentCoords_chartVec x x (mem_extChartAt_source x),
    L12Aux.tangentCoords_chartVec x x (mem_extChartAt_source x)]
  simp [stdVec, EuclideanSpace.single, Matrix.mulVec, dotProduct, Pi.single_apply]

/-- Every tangent vector has its actual finite canonical-frame expansion. -/
theorem canonicalTangentVector_basis_sum (x : M.Carrier) (u : TangentVector M x) :
    (∑ i, (tangentCoords x x u) i • chartVec x x (stdVec i)) = u := by
  rw [L17Aux.chartVec_basis_sum, L12Aux.chartVec_tangentCoords x x (mem_extChartAt_source x)]

/-- The finite canonical Gram matrix determines every actual tangent pairing. -/
theorem hermitianField_pairing_eq_gMat (g : HermitianField M) (x : M.Carrier)
    (u v : TangentVector M x) :
    (g x).toFun u v =
      star (WithLp.ofLp (tangentCoords x x u)) ⬝ᵥ
        ((gMat g x) *ᵥ WithLp.ofLp (tangentCoords x x v)) := by
  have he : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  calc
    _ = (g x).toFun
        (∑ i, (tangentCoords x x u) i • chartVec x x (stdVec i))
        (∑ i, (tangentCoords x x v) i • chartVec x x (stdVec i)) :=
      congrArg₂ (g x).toFun (canonicalTangentVector_basis_sum x u).symm
        (canonicalTangentVector_basis_sum x v).symm
    _ = _ := by
      rw [L12Aux.hermitian_sum_left]
      simp only [L12Aux.hermitian_sum_right, HermitianInnerProduct.map_smul_left,
        HermitianInnerProduct.map_smul_right, dotProduct, Matrix.mulVec,
        Pi.star_apply, Finset.mul_sum, gMat, hMat]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [he]
      ring

/-- Equality of actual canonical metric matrices implies equality of the fields. -/
theorem hermitianField_ext {h k : HermitianField M}
    (heq : ∀ x, gMat h x = gMat k x) : h = k := by
  funext x
  apply hermitianInnerProduct_ext
  intro u v
  rw [hermitianField_pairing_eq_gMat h, hermitianField_pairing_eq_gMat k, heq x]

theorem gMat_injective : Function.Injective (fun g : HermitianField M => gMat g) := by
  intro h k heq
  exact hermitianField_ext fun x => congrFun heq x

/-- Positivity comes from the actual canonical inverse-chart frame. -/
theorem canonical_gMat_posDef (g : HermitianField M) (x : M.Carrier) : (gMat g x).PosDef :=
  L12Aux.hMat_posDef g x (chartPt x x) (mem_extChartAt_target x)

/-- Reconstruction is independent of the chosen positivity proof. -/
theorem hermitianFieldOfMatrices_gMat_with_witness (g : HermitianField M)
    (hH : ∀ x, (gMat g x).PosDef) : hermitianFieldOfMatrices (gMat g) hH = g := by
  apply hermitianField_ext
  intro x
  exact gMat_hermitianFieldOfMatrices (gMat g) hH x

/-- The original Hermitian field is recovered without extra data or hypotheses. -/
theorem hermitianFieldOfMatrices_gMat (g : HermitianField M) :
    hermitianFieldOfMatrices (gMat g) (canonical_gMat_posDef g) = g :=
  hermitianFieldOfMatrices_gMat_with_witness g (canonical_gMat_posDef g)

end Yau.LeafProofs.L17HermitianMatrixAssemblyAux
