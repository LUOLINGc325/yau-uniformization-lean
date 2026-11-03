import Yau.LeafProofs.L14AdjointMultiplier
import Yau.LeafProofs.L14IMS

noncomputable section
open scoped Manifold Topology ContDiff ComplexOrder ENNReal Matrix
open MeasureTheory Bundle Filter Module

namespace Yau.LeafProofs.L14Aux
open BundleDbar

theorem finite_square_wirtBar_zero {n : ℕ} {ι : Type*} [Fintype ι]
    (χ : ι → ComplexVector n → ℂ) (z v : ComplexVector n)
    (hχ : ∀ k, DifferentiableAt ℝ (χ k) z)
    (hnear : (fun y => ∑ k, χ k y * χ k y) =ᶠ[𝓝 z] (fun _ => 1)) :
    ∑ k, χ k z * wirtBar (χ k) z v = 0 := by
  have hd : wirtBar (fun y => ∑ k, χ k y * χ k y) z v = 0 := by
    unfold wirtBar
    rw [hnear.fderiv_eq]
    simp
  rw [wirtBar_sum_fun Finset.univ (fun k y => χ k y * χ k y) z v
    (fun k _ => (hχ k).mul (hχ k))] at hd
  simp_rw [wirtBar_mul_rule _ _ z v (hχ _) (hχ _)] at hd
  have he : (∑ k, (wirtBar (χ k) z v * χ k z + χ k z * wirtBar (χ k) z v)) =
      (2 : ℂ) * ∑ k, χ k z * wirtBar (χ k) z v := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he] at hd
  exact (mul_eq_zero.mp hd).resolve_left (by norm_num)

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem square_partition_chart_wirtBar_zero {ι : Type*} [Fintype ι]
    (χ : ι → M.Carrier → ℝ) (hχ : ∀ k, SmoothFn (χ k))
    (a : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget a)
    (hnear : ∀ᶠ x in 𝓝 (chartInv a z), ∑ k, χ k x ^ 2 = 1) (i : Fin n) :
    (∑ k, (χ k (chartInv a z) : ℂ) *
      wirtBar (fun w => Complex.ofReal (inChart a (χ k) w)) z (stdVec i)) = 0 := by
  apply finite_square_wirtBar_zero (fun k w => Complex.ofReal (inChart a (χ k) w)) z (stdVec i)
  · intro k
    exact (((hχ k a).continuousLinearMap_comp Complex.ofRealCLM).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) a).mem_nhds hz)).differentiableAt (by simp)
  · have ht : ContinuousAt (chartInv a) z :=
      (continuousOn_extChartAt_symm (I := ComplexModel n) a).continuousAt
        ((isOpen_extChartAt_target (I := ComplexModel n) a).mem_nhds hz)
    filter_upwards [ht.tendsto.eventually hnear] with w hw
    change (∑ k, (χ k (chartInv a w) : ℂ) * (χ k (chartInv a w) : ℂ)) = 1
    exact_mod_cast (by simpa only [pow_two] using hw)

theorem raisedOneCoefficientsMatrix_multiply (g : HermitianField M) (χ : M.Carrier → ℝ)
    (u : NQForm E 1) (a : M.Carrier) (z : ComplexVector n) :
    raisedOneCoefficientsMatrix (r := r) E g (multiplyForm E (fun x => (χ x : ℂ)) u) a z =
      (χ (chartInv a z) : ℂ) • raisedOneCoefficientsMatrix (r := r) E g u a z := by
  ext i α
  simp only [raisedOneCoefficientsMatrix, Matrix.mul_apply, oneCoefficientsMatrix,
    coefficients_multiplyForm, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem raisedBarTensor_multiply (g : Yau.SmoothMetric M) (χ : M.Carrier → ℝ)
    (hχ : SmoothFn χ) (u : NQForm E 1) (hu : SmoothForm (r := r) E u)
    (a : M.Carrier) (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a)
    (α : Fin r) (i j : Fin n) :
    raisedBarTensor (r := r) E g.form (multiplyForm E (fun x => (χ x : ℂ)) u) a z α i j =
      (χ (chartInv a z) : ℂ) * raisedBarTensor (r := r) E g.form u a z α i j +
      wirtBar (fun w => Complex.ofReal (inChart a χ w)) z (stdVec i) *
        raisedOneCoefficientsMatrix (r := r) E g.form u a z j α := by
  have hη : DifferentiableAt ℝ (fun w => Complex.ofReal (inChart a χ w)) z :=
    (((hχ a).continuousLinearMap_comp Complex.ofRealCLM).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) a).mem_nhds hz.1)).differentiableAt (by simp)
  have hU : DifferentiableAt ℝ (fun w => raisedOneCoefficientsMatrix (r := r) E g.form u a w j α) z :=
    ((raisedOneCoefficientsMatrix_contDiffOn E g u hu a j α).contDiffAt
      ((localDomain_isOpen E a).mem_nhds hz)).differentiableAt (by simp)
  change wirtBar (fun w => raisedOneCoefficientsMatrix (r := r) E g.form
    (multiplyForm E (fun x => (χ x : ℂ)) u) a w j α) z (stdVec i) = _
  simp_rw [raisedOneCoefficientsMatrix_multiply]
  rw [show (fun w => ((χ (chartInv a w) : ℂ) • raisedOneCoefficientsMatrix (r := r) E g.form u a w) j α) =
      (fun w => Complex.ofReal (inChart a χ w) * raisedOneCoefficientsMatrix (r := r) E g.form u a w j α) from rfl,
    wirtBar_mul_rule _ _ z (stdVec i) hη hU]
  simp only [raisedBarTensor, rectangularWirtBar, inChart]
  ring

theorem dbarCoefficients_one_multiply_real
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ) (u : NQForm E 1) (hu : SmoothForm (r := r) E u)
    (a : M.Carrier) (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a)
    (i j : Fin n) (α : Fin r) :
    dbarCoefficients (r := r) E (multiplyForm E (fun x => (χ x : ℂ)) u) a z ![i,j] α =
      (χ (chartInv a z) : ℂ) * dbarCoefficients (r := r) E u a z ![i,j] α +
      wirtBar (fun w => Complex.ofReal (inChart a χ w)) z (stdVec i) * coefficients (r := r) E u a z (fun _ => j) α -
      wirtBar (fun w => Complex.ofReal (inChart a χ w)) z (stdVec j) * coefficients (r := r) E u a z (fun _ => i) α := by
  have hη : DifferentiableAt ℝ (fun w => Complex.ofReal (inChart a χ w)) z :=
    (((hχ a).continuousLinearMap_comp Complex.ofRealCLM).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) a).mem_nhds hz.1)).differentiableAt (by simp)
  have hd (k : Fin n) : DifferentiableAt ℝ (fun w => coefficients (r := r) E u a w (fun _ => k) α) z :=
    ((hu a (fun _ => k) α).contDiffAt ((localDomain_isOpen E a).mem_nhds hz)).differentiableAt (by simp)
  rw [dbarCoefficients_one_eq_curl, dbarCoefficients_one_eq_curl]
  simp only [localCurlMatrix, coefficients_multiplyForm]
  rw [show (fun w => (χ (chartInv a w) : ℂ) * coefficients (r := r) E u a w (fun _ => j) α) =
      (fun w => Complex.ofReal (inChart a χ w) * coefficients (r := r) E u a w (fun _ => j) α) from rfl,
    show (fun w => (χ (chartInv a w) : ℂ) * coefficients (r := r) E u a w (fun _ => i) α) =
      (fun w => Complex.ofReal (inChart a χ w) * coefficients (r := r) E u a w (fun _ => i) α) from rfl,
    wirtBar_mul_rule _ _ z (stdVec i) hη (hd j),
    wirtBar_mul_rule _ _ z (stdVec j) hη (hd i)]
  simp only [inChart]
  ring

end Yau.LeafProofs.L14Aux
