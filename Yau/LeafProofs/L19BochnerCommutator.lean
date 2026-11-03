import Yau.LeafProofs.L19Bochner

/-! Covariant third derivatives of the actual scalar Hessian. -/

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff Manifold Matrix ComplexOrder

namespace Yau.LeafProofs.L19Aux

open L18Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem rDeriv_sub {f k : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : DifferentiableAt ℝ f z) (hk : DifferentiableAt ℝ k z) (i : RIdx n) :
    rDeriv (fun w => f w - k w) z i = rDeriv f z i - rDeriv k z i := by
  unfold rDeriv
  rw [fderiv_fun_sub hf hk]
  rfl

theorem chartCovHessian_contDiffOn (g : SmoothMetric M) (a : M.Carrier)
    {f : ComplexVector n → ℝ} (hf : ContDiffOn ℝ ∞ f (chartTarget a))
    (i j : RIdx n) :
    ContDiffOn ℝ ∞ (fun z => chartCovHessian g.form a f z i j) (chartTarget a) := by
  have hO := isOpen_extChartAt_target (I := ComplexModel n) a
  have hdf (k : RIdx n) := rDeriv_contDiffOn hO hf k
  apply (rDeriv_contDiffOn hO (hdf j) i).sub
  apply ContDiffOn.sum
  intro k hk
  exact (L12Aux.christoffel_contDiffOn g a k i j).mul (hdf k)

theorem rDeriv_chartCovHessian (g : SmoothMetric M) (a : M.Carrier)
    {f : ComplexVector n → ℝ} (hf : ContDiffOn ℝ ∞ f (chartTarget a))
    {z : ComplexVector n} (hz : z ∈ chartTarget a) (l i j : RIdx n) :
    rDeriv (fun w => chartCovHessian g.form a f w i j) z l =
      rDeriv (fun w => rDeriv (fun v => rDeriv f v j) w i) z l -
        ∑ p, (rDeriv (fun w => christoffel g.form a w p i j) z l * rDeriv f z p +
          christoffel g.form a z p i j * rDeriv (fun w => rDeriv f w p) z l) := by
  have hO := isOpen_extChartAt_target (I := ComplexModel n) a
  have hdf (k : RIdx n) := rDeriv_contDiffOn hO hf k
  have hprod (p : RIdx n) := (L12Aux.christoffel_contDiffOn g a p i j).mul (hdf p)
  have hsum : ContDiffOn ℝ ∞ (fun w => ∑ p,
      christoffel g.form a w p i j * rDeriv f w p) (chartTarget a) := by
    apply ContDiffOn.sum
    intro p hp
    exact hprod p
  have hsecond := rDeriv_contDiffOn hO (hdf j) i
  unfold chartCovHessian
  rw [rDeriv_sub
    ((hsecond.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp))
    ((hsum.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)),
    rDeriv_sum _ (fun p => ((hprod p).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp))]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  exact rDeriv_mul
    (((L12Aux.christoffel_contDiffOn g a p i j).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp))
    (((hdf p).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)) l

def chartCovThird (h : HermitianField M) (a : M.Carrier)
    (f : ComplexVector n → ℝ) (z : ComplexVector n) (l i j : RIdx n) : ℝ :=
  rDeriv (fun w => chartCovHessian h a f w i j) z l -
    (∑ p, christoffel h a z p l i * chartCovHessian h a f z p j) -
    ∑ p, christoffel h a z p l j * chartCovHessian h a f z i p

/-- The coefficient cancellation for a torsion-free covector derivative.
The sign matches the project's existing `riemannCoeff` convention. -/
theorem covariant_commutator_algebra {ι : Type*} [Fintype ι]
    (Γ : ι → ι → ι → ℝ) (dΓ : ι → ι → ι → ι → ℝ)
    (f₁ : ι → ℝ) (f₂ : ι → ι → ℝ) (f₃ : ι → ι → ι → ℝ)
    (hΓ : ∀ p l i, Γ p l i = Γ p i l)
    (l i k : ι) (hthird : f₃ l i k = f₃ i l k) :
    let H := fun i j => f₂ i j - ∑ p, Γ p i j * f₁ p
    let T := fun l i j => f₃ l i j -
      (∑ p, (dΓ l p i j * f₁ p + Γ p i j * f₂ l p)) -
      (∑ p, Γ p l i * H p j) - ∑ p, Γ p l j * H i p
    T l i k - T i l k =
      -∑ p, (dΓ l p i k - dΓ i p l k +
        ∑ q, (Γ q i k * Γ p l q - Γ q l k * Γ p i q)) * f₁ p := by
  dsimp only
  rw [hthird]
  simp_rw [hΓ (l := l) (i := i)]
  have hprod : (∑ p, (∑ q, (Γ q i k * Γ p l q - Γ q l k * Γ p i q)) * f₁ p) =
      (∑ p, ∑ q, Γ p i k * Γ q l p * f₁ q) -
        ∑ p, ∑ q, Γ p l k * Γ q i p * f₁ q := by
    simp only [Finset.sum_sub_distrib, Finset.sum_mul, sub_mul]
    congr 1 <;> exact Finset.sum_comm
  have hcurv : (∑ p, (dΓ l p i k - dΓ i p l k +
      ∑ q, (Γ q i k * Γ p l q - Γ q l k * Γ p i q)) * f₁ p) =
      ((∑ p, dΓ l p i k * f₁ p) - ∑ p, dΓ i p l k * f₁ p) +
        ((∑ p, ∑ q, Γ p i k * (Γ q l p * f₁ q)) -
          ∑ p, ∑ q, Γ p l k * (Γ q i p * f₁ q)) := by
    calc
      _ = ((∑ p, dΓ l p i k * f₁ p) - ∑ p, dΓ i p l k * f₁ p) +
          ∑ p, (∑ q, (Γ q i k * Γ p l q - Γ q l k * Γ p i q)) * f₁ p := by
        simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = _ := by rw [hprod]; simp only [mul_assoc]
  rw [hcurv]
  simp only [mul_sub, Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  ring

/-- The actual third covariant scalar derivatives commute with the
negative of the pre-existing curvature calculator acting on df. -/
theorem chartCovHessian_commutator (g : SmoothMetric M) (a : M.Carrier)
    {f : ComplexVector n → ℝ} (hf : ContDiffOn ℝ ∞ f (chartTarget a))
    {z : ComplexVector n} (hz : z ∈ chartTarget a) (l i k : RIdx n) :
    chartCovThird g.form a f z l i k - chartCovThird g.form a f z i l k =
      -∑ p, riemannCoeff g.form a z l i k p * rDeriv f z p := by
  have hO := isOpen_extChartAt_target (I := ComplexModel n) a
  have hk : ContDiffAt ℝ 2 (fun w => rDeriv f w k) z :=
    ((rDeriv_contDiffOn hO hf k).contDiffAt (hO.mem_nhds hz)).of_le (by simp)
  have hthird : rDeriv (fun w => rDeriv (fun v => rDeriv f v k) w i) z l =
      rDeriv (fun w => rDeriv (fun v => rDeriv f v k) w l) z i := by
    rw [rDeriv_rDeriv_eq_hessian hk, rDeriv_rDeriv_eq_hessian hk]
    exact hk.isSymmSndFDerivAt (by norm_num) (realVec l) (realVec i)
  have halg := covariant_commutator_algebra
    (fun p l i => christoffel g.form a z p l i)
    (fun l p i j => rDeriv (fun w => christoffel g.form a w p i j) z l)
    (fun p => rDeriv f z p)
    (fun i j => rDeriv (fun w => rDeriv f w j) z i)
    (fun l i j => rDeriv (fun w => rDeriv (fun v => rDeriv f v j) w i) z l)
    (L12Aux.christoffel_symm_lower g.form a z) l i k hthird
  dsimp only at halg
  unfold chartCovThird
  rw [rDeriv_chartCovHessian g a hf hz, rDeriv_chartCovHessian g a hf hz]
  simpa only [chartCovHessian, riemannCoeff] using halg

end Yau.LeafProofs.L19Aux
