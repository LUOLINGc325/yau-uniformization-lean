import Yau.Proofs.P06WeitzenbockFiberEnergy
import Yau.Proofs.P06WeitzenbockPairing

noncomputable section
open scoped Matrix ComplexOrder Manifold Topology ContDiff
namespace Yau.NodeProofs.P06Weitzenbock
open Yau G01Aux Yau.LeafProofs
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem curvaturePair_spectral_of_symmetries
    (g : SmoothMetric M) (hk : IsKahler g) (A : RealForm M 2) (h11 : RealOneOne A)
    (x : M.Carrier) (E : Matrix (Fin n) (Fin n) ℂ) (eig : Fin n → ℝ)
    (hE : Eᴴ * gMat g.form x * E = 1)
    (hA : formHermitianMatrix A x =
      gMat g.form x * E * Matrix.diagonal (fun i => (eig i : ℂ)) * Eᴴ * gMat g.form x)
    (hstar : ∀ i j k l, star (chernCurvature g.form x i j k l) =
      chernCurvature g.form x j i l k)
    (hpair : ∀ i j k l, chernCurvature g.form x i j k l =
      chernCurvature g.form x k l i j)
    (hRic : ricci g.form x = finiteCurvatureAction (chernCurvature g.form x) (gMat g.form x)⁻¹) :
    curvaturePair g.form A A x =
      diagonalCurvatureEnergy (fun i j =>
        (frameCurvatureCoefficient (chernCurvature g.form x) E i j).re) eig := by
  rw [curvaturePair_eq_hermitian_trace_of_symmetries g hk A A h11 h11 x hstar hpair]
  have hH : (gMat g.form x).PosDef :=
    L12Aux.hMat_posDef g.form x (chartPt x x) (mem_extChartAt_target x)
  simp only [hermitianCurvatureReaction, hRic, chernActionMatrix, raisedFormMatrix]
  change (Matrix.trace ((gMat g.form x)⁻¹ *
    (finiteCurvatureAction (chernCurvature g.form x) (gMat g.form x)⁻¹ *
        (gMat g.form x)⁻¹ * formHermitianMatrix A x +
      formHermitianMatrix A x * (gMat g.form x)⁻¹ *
        finiteCurvatureAction (chernCurvature g.form x) (gMat g.form x)⁻¹ -
      (2 : ℂ) • finiteCurvatureAction (chernCurvature g.form x)
        ((gMat g.form x)⁻¹ * formHermitianMatrix A x * (gMat g.form x)⁻¹)) *
      (gMat g.form x)⁻¹ * formHermitianMatrix A x)).re = _
  rw [hA]
  exact relativeReactionEnergy_spectral (chernCurvature g.form x) hpair
    (gMat g.form x) E hH hE eig

theorem curvaturePair_hbc_spectral_of_symmetries
    (g : SmoothMetric M) (hk : IsKahler g) (A : RealForm M 2) (h11 : RealOneOne A)
    (x : M.Carrier) (E : Matrix (Fin n) (Fin n) ℂ) (eig : Fin n → ℝ)
    (hE : Eᴴ * gMat g.form x * E = 1)
    (hA : formHermitianMatrix A x =
      gMat g.form x * E * Matrix.diagonal (fun i => (eig i : ℂ)) * Eᴴ * gMat g.form x)
    (hunit : ∀ i, hermitianNormSq (g.form x) (chartVec x x (matrixColumn E i)) = 1)
    (hstar : ∀ i j k l, star (chernCurvature g.form x i j k l) =
      chernCurvature g.form x j i l k)
    (hpair : ∀ i j k l, chernCurvature g.form x i j k l =
      chernCurvature g.form x k l i j)
    (hRic : ricci g.form x = finiteCurvatureAction (chernCurvature g.form x) (gMat g.form x)⁻¹) :
    curvaturePair g.form A A x = ∑ i, ∑ j,
      paperHolomorphicBisectionalCurvature g.form x (chartVec x x (matrixColumn E i))
        (chartVec x x (matrixColumn E j)) * (eig i - eig j) ^ 2 := by
  rw [curvaturePair_spectral_of_symmetries g hk A h11 x E eig hE hA hstar hpair hRic]
  unfold diagonalCurvatureEnergy
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp only
  rw [frameCurvatureCoefficient_eq_paperHBC g.form (L12Aux.metricSmooth_of_smoothMetric g)
    hk x E hunit i j]

end Yau.NodeProofs.P06Weitzenbock
