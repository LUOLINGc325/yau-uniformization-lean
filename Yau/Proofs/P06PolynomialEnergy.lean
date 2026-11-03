import Yau.Proofs.P06RelativePolynomialFrame
import Yau.Proofs.P06GradientPolynomial
import Yau.Proofs.P06WeitzenbockComputedEnergy
import Yau.Proofs.P06HodgeEnergySpace

noncomputable section
open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder InnerProductSpace

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs.L03
variable {n : ℕ} {M : ComplexManifold n}

theorem polynomialForm_curvaturePair_le (g : SmoothMetric M) (hk : IsKahler g)
    (hHBC : ∀ x u v, 0 ≤ paperHolomorphicBisectionalCurvature g.form x u v)
    (A : RealForm M 2) (h11 : RealOneOne A) (p : Polynomial ℝ) (x : M.Carrier) {R : ℝ}
    (hnorm : ‖Clip.pointFormHS g.form A x‖ ≤ R)
    (hder : ∀ r ∈ Set.Icc (-R) R, |p.derivative.eval r| ≤ 1) :
    P06Weitzenbock.curvaturePair g.form (FiberPoly.polynomialForm g.form A h11 p)
      (FiberPoly.polynomialForm g.form A h11 p) x ≤ P06Weitzenbock.curvaturePair g.form A A x := by
  have hH := Yau.LeafProofs.L12Aux.hMat_posDef g.form x (chartPt x x) (mem_extChartAt_target x)
  obtain ⟨E, eig, hE, hsA⟩ := P06Weitzenbock.exists_relative_unitary_eigenframe
    (gMat g.form x) (formHermitianMatrix A x) hH ((G04Aux.representsSelf A h11).2 x)
  have heig (i : Fin n) : eig i ∈ Set.Icc (-R) R := by
    apply abs_le.mp
    exact (Clip.relativeUnitary_eigenvalue_bound _ _ E hH eig hE hsA i).trans hnorm
  apply P06Weitzenbock.curvaturePair_contraction g hk hHBC A
    (FiberPoly.polynomialForm g.form A h11 p) h11
    (FiberPoly.polynomialForm_oneOne g.form A h11 p) x E eig (fun i => p.eval (eig i)) hE hsA
  · rw [FiberPoly.polynomialForm_matrix, FiberPoly.fiberMatrix]
    exact Clip.weightedPolynomial_spectral _ _ E hH eig hE hsA p
  · intro i j
    exact sq_le_sq.mp (Clip.polynomial_difference_sq_le p hder (heig i) (heig j))

/-- The true original Hodge q-energy contracts under every zero-fixed
polynomial whose derivative is bounded by one on the actual fiber spectra. -/
theorem polynomialForm_hodgeEnergy_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (hHBC : ∀ x u v, 0 ≤ paperHolomorphicBisectionalCurvature g.form x u v)
    (A : RealForm M 2) (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A)
    (h11 : RealOneOne A) (p : Polynomial ℝ) (hp : p.eval 0 = 0) {R : ℝ}
    (hnorm : ∀ x, ‖Clip.pointFormHS g.form A x‖ ≤ R)
    (hder : ∀ r ∈ Set.Icc (-R) R, |p.derivative.eval r| ≤ 1) :
    hodgeEnergy g μ hμ (hodgeEnergyCore g μ hμ (FiberPoly.polynomialForm g.form A h11 p)
      (FiberPoly.polynomialForm_smooth g A hA h11 p)
      (FiberPoly.polynomialForm_compactlySupported g.form A h11 p hp hcA)) ≤
        hodgeEnergy g μ hμ (hodgeEnergyCore g μ hμ A hA hcA) := by
  have hsP := FiberPoly.polynomialForm_smooth g A hA h11 p
  have hcP := FiberPoly.polynomialForm_compactlySupported g.form A h11 p hp hcA
  rw [hodgeEnergyCore_energy, hodgeEnergyCore_energy,
    P06Weitzenbock.hodge_energy_quadratic g μ hμ _ hsP hcP,
    P06Weitzenbock.hodge_energy_quadratic g μ hμ A hA hcA]
  apply add_le_add
  · apply integral_mono
      (P06Weitzenbock.gradientPair_integrable g μ hμ _ _ hsP hsP hcP)
      (P06Weitzenbock.gradientPair_integrable g μ hμ A A hA hA hcA)
    intro x
    apply GradientPoly.polynomialForm_gradientPair_le g hk A hA h11 p x
    · intro i
      apply abs_le.mp
      exact (Clip.abs_eigenvalues_le_matrixToHS _ (Clip.metricWhiten_hermitian
        (gMat g.form x) (formHermitianMatrix A x) ((G04Aux.representsSelf A h11).2 x)) i).trans (hnorm x)
    · exact hder
  · apply integral_mono
      (P06Weitzenbock.curvaturePair_integrable g μ hμ _ _ hsP hsP hcP)
      (P06Weitzenbock.curvaturePair_integrable g μ hμ A A hA hA hcA)
    exact fun x => polynomialForm_curvaturePair_le g hk hHBC A h11 p x (hnorm x) hder

end Yau.NodeProofs.P06Aux
