import Yau.LeafProofs.L14Curvature

noncomputable section
open scoped Manifold Topology ContDiff ComplexOrder ENNReal Matrix
open Filter

namespace Yau.LeafProofs.L14Aux
open BundleDbar

def rectangularWirtBar {n m r : ℕ}
    (H : ComplexVector n → Matrix (Fin m) (Fin r) ℂ) (z : ComplexVector n) (i : Fin n) :
    Matrix (Fin m) (Fin r) ℂ := fun α β => wirtBar (fun w => H w α β) z (stdVec i)

theorem rectangularWirtBar_congr {n m r : ℕ}
    (H K : ComplexVector n → Matrix (Fin m) (Fin r) ℂ) (z : ComplexVector n)
    (hHK : H =ᶠ[𝓝 z] K) (i : Fin n) : rectangularWirtBar H z i = rectangularWirtBar K z i := by
  ext α β
  have he : (fun w => H w α β) =ᶠ[𝓝 z] (fun w => K w α β) :=
    hHK.mono (fun _ h => congrArg (fun A => A α β) h)
  unfold rectangularWirtBar wirtBar
  rw [he.fderiv_eq]

theorem rectangularWirtBar_mul {n m k r : ℕ}
    (A : ComplexVector n → Matrix (Fin m) (Fin k) ℂ)
    (B : ComplexVector n → Matrix (Fin k) (Fin r) ℂ) (z : ComplexVector n)
    (hA : ∀ α β, DifferentiableAt ℝ (fun w => A w α β) z)
    (hB : ∀ α β, DifferentiableAt ℝ (fun w => B w α β) z) (i : Fin n) :
    rectangularWirtBar (fun w => A w * B w) z i =
      rectangularWirtBar A z i * B z + A z * rectangularWirtBar B z i := by
  ext α β
  change wirtBar (fun w => ∑ γ, A w α γ * B w γ β) z (stdVec i) = _
  rw [wirtBar_sum_fun Finset.univ (fun γ w => A w α γ * B w γ β)
    z (stdVec i) (fun γ _ => (hA α γ).mul (hB γ β))]
  simp_rw [wirtBar_mul_rule _ _ z (stdVec i) (hA α _) (hB _ β)]
  simp only [Matrix.add_apply, Matrix.mul_apply, rectangularWirtBar, Finset.sum_add_distrib]

theorem rectangularWirtBar_smul {n m r : ℕ}
    (f : ComplexVector n → ℂ) (A : ComplexVector n → Matrix (Fin m) (Fin r) ℂ)
    (z : ComplexVector n) (hf : DifferentiableAt ℝ f z)
    (hA : ∀ α β, DifferentiableAt ℝ (fun w => A w α β) z) (i : Fin n) :
    rectangularWirtBar (fun w => f w • A w) z i =
      wirtBar f z (stdVec i) • A z + f z • rectangularWirtBar A z i := by
  ext α β
  change wirtBar (fun w => f w * A w α β) z (stdVec i) = _
  exact wirtBar_mul_rule f _ z (stdVec i) hf (hA α β)

theorem rectangularWirtBar_comp {n m r : ℕ}
    (H : ComplexVector n → Matrix (Fin m) (Fin r) ℂ)
    (T : ComplexVector n → ComplexVector n) (z : ComplexVector n)
    (hT : DifferentiableAt ℂ T z)
    (hH : ∀ α β, DifferentiableAt ℝ (fun w => H w α β) (T z)) (i : Fin n) :
    rectangularWirtBar (fun w => H (T w)) z i =
      ∑ p, star (fderiv ℂ T z (stdVec i) p) • rectangularWirtBar H (T z) p := by
  ext α β
  simp only [rectangularWirtBar, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [wirtBar_comp_complex_differentiable T _ z (stdVec i) hT (hH α β), wirtBar_direction_coordinates]

theorem rectangularWirtBar_holomorphic {n m r : ℕ}
    (A : ComplexVector n → Matrix (Fin m) (Fin r) ℂ) (z : ComplexVector n)
    (hA : ∀ α β, DifferentiableAt ℂ (fun w => A w α β) z) (i : Fin n) :
    rectangularWirtBar A z i = 0 := by
  ext α β
  exact wirtBar_eq_zero_of_complex_differentiable _ z (stdVec i) (hA α β)

theorem rectangular_mul_differentiableAt {n m k r : ℕ}
    (A : ComplexVector n → Matrix (Fin m) (Fin k) ℂ)
    (B : ComplexVector n → Matrix (Fin k) (Fin r) ℂ) (z : ComplexVector n)
    (hA : ∀ α β, DifferentiableAt ℝ (fun w => A w α β) z)
    (hB : ∀ α β, DifferentiableAt ℝ (fun w => B w α β) z) (α β) :
    DifferentiableAt ℝ (fun w => (A w * B w) α β) z := by
  simpa only [Matrix.mul_apply, Pi.mul_apply] using
    DifferentiableAt.fun_sum (u := Finset.univ) (fun γ _ => (hA α γ).mul (hB γ β))

theorem holomorphic_determinant_contDiffAt {n r : ℕ}
    (A : ComplexVector n → Matrix (Fin r) (Fin r) ℂ) (z : ComplexVector n)
    (hA : ∀ α β, ContDiffAt ℂ ∞ (fun w => A w α β) z) :
    ContDiffAt ℂ ∞ (fun w => (A w).det) z := by
  classical
  simp_rw [Matrix.det_apply']
  exact ContDiffAt.sum fun σ _ => contDiffAt_const.mul (contDiffAt_prod fun i _ => hA (σ i) i)

end Yau.LeafProofs.L14Aux
