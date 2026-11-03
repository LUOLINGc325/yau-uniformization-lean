import Yau.Proofs.P06WeitzenbockCurvatureEnergy
import Yau.Proofs.P06WeitzenbockComputedReaction
import Yau.Proofs.P06WeitzenbockEigenframe

noncomputable section
open MeasureTheory
open scoped Matrix ComplexOrder Manifold Topology ContDiff
namespace Yau.NodeProofs.P06Weitzenbock
open Yau G01Aux Yau.LeafProofs
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

/-- Curvature energy of the original computed Hodge operator in an arbitrary
pointwise unitary eigenframe. The coefficient is the paper's actual HBC. -/
theorem curvaturePair_eq_hbc_spectral
    (g : SmoothMetric M) (hk : IsKahler g) (A : RealForm M 2) (h11 : RealOneOne A)
    (x : M.Carrier) (E : Matrix (Fin n) (Fin n) ℂ) (eig : Fin n → ℝ)
    (hE : Eᴴ * gMat g.form x * E = 1)
    (hA : formHermitianMatrix A x =
      gMat g.form x * E * Matrix.diagonal (fun i => (eig i : ℂ)) * Eᴴ * gMat g.form x) :
    curvaturePair g.form A A x = ∑ i, ∑ j,
      paperHolomorphicBisectionalCurvature g.form x (chartVec x x (matrixColumn E i))
        (chartVec x x (matrixColumn E j)) * (eig i - eig j) ^ 2 :=
  curvaturePair_hbc_spectral_of_symmetries g hk A h11 x E eig hE hA
    (unitary_frame_column_norm g.form x E hE)
    (computedChern_star g.form (L12Aux.metricSmooth_of_smoothMetric g) x)
    (computedChern_pair g.form (L12Aux.metricSmooth_of_smoothMetric g) hk x)
    (computedRicci_eq_curvatureAction g.form (L12Aux.metricSmooth_of_smoothMetric g) hk x)

theorem curvaturePair_nonneg (g : SmoothMetric M) (hk : IsKahler g)
    (hHBC : ∀ x u v, 0 ≤ paperHolomorphicBisectionalCurvature g.form x u v)
    (A : RealForm M 2) (h11 : RealOneOne A) (x : M.Carrier) :
    0 ≤ curvaturePair g.form A A x := by
  have hH : (gMat g.form x).PosDef :=
    L12Aux.hMat_posDef g.form x (chartPt x x) (mem_extChartAt_target x)
  have hA : (formHermitianMatrix A x).IsHermitian := (G04Aux.representsSelf A h11).2 x
  obtain ⟨E, eig, hE, hspec⟩ := exists_relative_unitary_eigenframe _ _ hH hA
  rw [curvaturePair_eq_hbc_spectral g hk A h11 x E eig hE hspec]
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
    (fun j _ => mul_nonneg (hHBC x _ _) (sq_nonneg _)))

/-- Sharp curvature-energy contraction for two arbitrary signed forms with
a common pointwise eigenframe. In particular this applies to every scalar
polynomial contraction without differentiating eigenvectors. -/
theorem curvaturePair_contraction (g : SmoothMetric M) (hk : IsKahler g)
    (hHBC : ∀ x u v, 0 ≤ paperHolomorphicBisectionalCurvature g.form x u v)
    (A B : RealForm M 2) (hA : RealOneOne A) (hB : RealOneOne B) (x : M.Carrier)
    (E : Matrix (Fin n) (Fin n) ℂ) (eig mu : Fin n → ℝ)
    (hE : Eᴴ * gMat g.form x * E = 1)
    (hsA : formHermitianMatrix A x =
      gMat g.form x * E * Matrix.diagonal (fun i => (eig i : ℂ)) * Eᴴ * gMat g.form x)
    (hsB : formHermitianMatrix B x =
      gMat g.form x * E * Matrix.diagonal (fun i => (mu i : ℂ)) * Eᴴ * gMat g.form x)
    (hLip : ∀ i j, |mu i - mu j| ≤ |eig i - eig j|) :
    curvaturePair g.form B B x ≤ curvaturePair g.form A A x := by
  rw [curvaturePair_eq_hbc_spectral g hk B hB x E mu hE hsB,
    curvaturePair_eq_hbc_spectral g hk A hA x E eig hE hsA]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left (sq_le_sq.mpr (hLip i j)) (hHBC x _ _)

theorem integral_gradient_le_hodge_energy (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (hHBC : ∀ x u v, 0 ≤ paperHolomorphicBisectionalCurvature g.form x u v)
    (A : RealForm M 2) (hA : SmoothRealForm A) (h11 : RealOneOne A)
    (hcA : CompactlySupportedRealForm A) :
    (∫ x, gradientPair g.form A A x ∂μ) ≤
      (∫ x, formNormSq g.form (L03.exteriorRealForm A) x ∂μ) +
        (∫ x, formNormSq g.form (L03.codifferentialRealForm g.form A) x ∂μ) := by
  rw [hodge_energy_quadratic g μ hμ A hA hcA]
  exact le_add_of_nonneg_right (integral_nonneg (curvaturePair_nonneg g hk hHBC A h11))

end Yau.NodeProofs.P06Weitzenbock
