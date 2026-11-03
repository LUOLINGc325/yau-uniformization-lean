import Yau.Proofs.G01Calculator

noncomputable section
open scoped Manifold Topology ContDiff Matrix
namespace Yau.NodeProofs.G01Aux
set_option backward.isDefEq.respectTransparency false
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

/-- The Basic curvature contraction is homogeneous in the second intrinsic tangent vector. -/
theorem bisectionalNumeratorOnTangent_smul_right (h : HermitianField M) (x : M.Carrier)
    (u v : TangentVector M x) (c : ℂ) :
    bisectionalNumeratorOnTangent h x u (c • v) =
      (Complex.normSq c : ℂ) * bisectionalNumeratorOnTangent h x u v := by
  have hc : c * star c = (Complex.normSq c : ℂ) := by
    simpa only [Complex.star_def] using Complex.mul_conj c
  have hv : tangentCoordinates x (c • v) = c • tangentCoordinates x v :=
    (mfderiv (ComplexModel n) (ComplexModel n) (extChartAt (ComplexModel n) x) x).map_smul c v
  unfold bisectionalNumeratorOnTangent
  rw [hv]
  unfold bisectionalNumerator
  simp only [PiLp.smul_apply, smul_eq_mul, star_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [← hc]
  ring

theorem bisectionalNumeratorOnTangent_re_smul_right (h : HermitianField M) (x : M.Carrier)
    (u v : TangentVector M x) (c : ℂ) :
    (bisectionalNumeratorOnTangent h x u (c • v)).re =
      Complex.normSq c * (bisectionalNumeratorOnTangent h x u v).re := by
  rw [bisectionalNumeratorOnTangent_smul_right]
  simp

/-- The two Chern contractions agree in the actual central frame. -/
theorem bisectionalNumeratorOnTangent_re_eq (h : HermitianField M)
    (hs : MetricSmooth h) (x : M.Carrier) (u v : TangentVector M x) :
    (bisectionalNumeratorOnTangent h x u v).re =
      bisectionalForm h x (tangentCoordinates x u) (tangentCoordinates x v) := by
  unfold bisectionalNumeratorOnTangent bisectionalNumerator bisectionalForm
  simp_rw [chernCalculatorCompatibility h hs x]

end Yau.NodeProofs.G01Aux
