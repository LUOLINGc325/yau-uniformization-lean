import Yau.LeafProofs.L14
import Yau.LeafProofs.L14Calculus

noncomputable section
open scoped Manifold Topology ContDiff ComplexOrder ENNReal Matrix
open MeasureTheory Bundle Filter

namespace Yau.LeafProofs.L14Aux
open BundleDbar

theorem chernConnectionMatrix_congr_of_eventuallyEq {n r : ℕ}
    (H K : ComplexVector n → Matrix (Fin r) (Fin r) ℂ) (z : ComplexVector n)
    (hHK : H =ᶠ[𝓝 z] K) (i : Fin n) :
    chernConnectionMatrix H z i = chernConnectionMatrix K z i := by
  unfold chernConnectionMatrix
  rw [hHK.self_of_nhds]
  congr 1
  ext α β
  have he : (fun w => H w α β) =ᶠ[𝓝 z] (fun w => K w α β) :=
    hHK.mono (fun _ h => congrArg (fun A => A α β) h)
  simp only [Matrix.of_apply, wirt]
  rw [he.fderiv_eq]

theorem curvatureMatrix_congr_of_eqOn {n r : ℕ}
    (H K : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hHK : Set.EqOn H K O)
    (z : ComplexVector n) (hz : z ∈ O) : curvatureMatrix H z = curvatureMatrix K z := by
  have hΓ (w : ComplexVector n) (hw : w ∈ O) (i : Fin n) :
      chernConnectionMatrix H w i = chernConnectionMatrix K w i :=
    chernConnectionMatrix_congr_of_eventuallyEq H K w
      (Filter.eventuallyEq_of_mem (hO.mem_nhds hw) hHK) i
  funext i j
  unfold curvatureMatrix
  rw [hHK hz]
  congr 2
  ext α β
  have he : (fun w => chernConnectionMatrix H w i α β) =ᶠ[𝓝 z]
      (fun w => chernConnectionMatrix K w i α β) := by
    filter_upwards [hO.mem_nhds hz] with w hw
    exact congrArg (fun A => A α β) (hΓ w hw i)
  simp only [Matrix.of_apply, wirtBar]
  rw [he.fderiv_eq]

theorem wirt_comp_complex_differentiable {V U : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup U] [NormedSpace ℂ U]
    (T : V → U) (f : U → ℂ) (z v : V)
    (hT : DifferentiableAt ℂ T z) (hf : DifferentiableAt ℝ f (T z)) :
    wirt (fun x => f (T x)) z v = wirt f (T z) (fderiv ℂ T z v) := by
  unfold wirt
  have hd : fderiv ℝ (fun x => f (T x)) z = (fderiv ℝ f (T z)).comp (fderiv ℝ T z) :=
    fderiv_comp z hf (hT.restrictScalars ℝ)
  rw [hd, hT.fderiv_restrictScalars (𝕜 := ℝ)]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars']
  rw [map_smul]

theorem wirt_direction_coordinates {n : ℕ} (f : ComplexVector n → ℂ)
    (z v : ComplexVector n) :
    wirt f z v = ∑ i : Fin n, v i * wirt f z (stdVec i) := by
  have he := congrArg star (wirtBar_direction_coordinates (fun y => star (f y)) z v)
  simpa only [wirtBar_star, star_star, star_sum, star_mul, mul_comm] using he

def matrixWirt {n r : ℕ} (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (z : ComplexVector n) (i : Fin n) : Matrix (Fin r) (Fin r) ℂ :=
  fun α β => wirt (fun w => H w α β) z (stdVec i)

def matrixWirtBar {n r : ℕ} (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (z : ComplexVector n) (i : Fin n) : Matrix (Fin r) (Fin r) ℂ :=
  fun α β => wirtBar (fun w => H w α β) z (stdVec i)

theorem matrixWirt_mul {n r : ℕ}
    (A B : ComplexVector n → Matrix (Fin r) (Fin r) ℂ) (z : ComplexVector n)
    (hA : ∀ α β, DifferentiableAt ℝ (fun w => A w α β) z)
    (hB : ∀ α β, DifferentiableAt ℝ (fun w => B w α β) z) (i : Fin n) :
    matrixWirt (fun w => A w * B w) z i = matrixWirt A z i * B z + A z * matrixWirt B z i := by
  ext α β
  change wirt (fun w => ∑ γ, A w α γ * B w γ β) z (stdVec i) = _
  rw [wirt_sum_fun Finset.univ (fun γ w => A w α γ * B w γ β)
    z (stdVec i) (fun γ _ => (hA α γ).mul (hB γ β))]
  simp_rw [wirt_mul_rule _ _ z (stdVec i) (hA α _) (hB _ β)]
  simp only [Matrix.add_apply, Matrix.mul_apply, matrixWirt, Finset.sum_add_distrib]

theorem matrixWirtBar_mul {n r : ℕ}
    (A B : ComplexVector n → Matrix (Fin r) (Fin r) ℂ) (z : ComplexVector n)
    (hA : ∀ α β, DifferentiableAt ℝ (fun w => A w α β) z)
    (hB : ∀ α β, DifferentiableAt ℝ (fun w => B w α β) z) (i : Fin n) :
    matrixWirtBar (fun w => A w * B w) z i = matrixWirtBar A z i * B z + A z * matrixWirtBar B z i := by
  ext α β
  change wirtBar (fun w => ∑ γ, A w α γ * B w γ β) z (stdVec i) = _
  rw [wirtBar_sum_fun Finset.univ (fun γ w => A w α γ * B w γ β)
    z (stdVec i) (fun γ _ => (hA α γ).mul (hB γ β))]
  simp_rw [wirtBar_mul_rule _ _ z (stdVec i) (hA α _) (hB _ β)]
  simp only [Matrix.add_apply, Matrix.mul_apply, matrixWirtBar, Finset.sum_add_distrib]

theorem matrixWirt_comp {n r : ℕ}
    (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (T : ComplexVector n → ComplexVector n) (z : ComplexVector n)
    (hT : DifferentiableAt ℂ T z)
    (hH : ∀ α β, DifferentiableAt ℝ (fun w => H w α β) (T z)) (i : Fin n) :
    matrixWirt (fun w => H (T w)) z i =
      ∑ p, (fderiv ℂ T z (stdVec i) p) • matrixWirt H (T z) p := by
  ext α β
  simp only [matrixWirt, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [wirt_comp_complex_differentiable T _ z (stdVec i) hT (hH α β), wirt_direction_coordinates]

theorem matrixWirtBar_comp {n r : ℕ}
    (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (T : ComplexVector n → ComplexVector n) (z : ComplexVector n)
    (hT : DifferentiableAt ℂ T z)
    (hH : ∀ α β, DifferentiableAt ℝ (fun w => H w α β) (T z)) (i : Fin n) :
    matrixWirtBar (fun w => H (T w)) z i =
      ∑ p, star (fderiv ℂ T z (stdVec i) p) • matrixWirtBar H (T z) p := by
  ext α β
  simp only [matrixWirtBar, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [wirtBar_comp_complex_differentiable T _ z (stdVec i) hT (hH α β), wirtBar_direction_coordinates]

theorem matrixWirtBar_congr_of_eventuallyEq {n r : ℕ}
    (H K : ComplexVector n → Matrix (Fin r) (Fin r) ℂ) (z : ComplexVector n)
    (hHK : H =ᶠ[𝓝 z] K) (i : Fin n) : matrixWirtBar H z i = matrixWirtBar K z i := by
  ext α β
  have he : (fun w => H w α β) =ᶠ[𝓝 z] (fun w => K w α β) :=
    hHK.mono (fun _ h => congrArg (fun A => A α β) h)
  unfold matrixWirtBar wirtBar
  rw [he.fderiv_eq]

theorem matrixWirtBar_sum {n r : ℕ} {κ : Type*} [Fintype κ]
    (A : κ → ComplexVector n → Matrix (Fin r) (Fin r) ℂ) (z : ComplexVector n)
    (hA : ∀ k α β, DifferentiableAt ℝ (fun w => A k w α β) z) (i : Fin n) :
    matrixWirtBar (fun w => ∑ k, A k w) z i = ∑ k, matrixWirtBar (A k) z i := by
  ext α β
  simp only [matrixWirtBar, Matrix.sum_apply]
  rw [wirtBar_sum_fun Finset.univ (fun k w => A k w α β) z (stdVec i) (fun k _ => hA k α β)]

theorem matrixWirtBar_smul {n r : ℕ}
    (f : ComplexVector n → ℂ) (A : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (z : ComplexVector n) (hf : DifferentiableAt ℝ f z)
    (hA : ∀ α β, DifferentiableAt ℝ (fun w => A w α β) z) (i : Fin n) :
    matrixWirtBar (fun w => f w • A w) z i =
      wirtBar f z (stdVec i) • A z + f z • matrixWirtBar A z i := by
  ext α β
  change wirtBar (fun w => f w * A w α β) z (stdVec i) = _
  exact wirtBar_mul_rule f _ z (stdVec i) hf (hA α β)

theorem matrixWirtBar_holomorphic {n r : ℕ}
    (A : ComplexVector n → Matrix (Fin r) (Fin r) ℂ) (z : ComplexVector n)
    (hA : ∀ α β, DifferentiableAt ℂ (fun w => A w α β) z) (i : Fin n) :
    matrixWirtBar A z i = 0 := by
  ext α β
  exact wirtBar_eq_zero_of_complex_differentiable _ z (stdVec i) (hA α β)

theorem matrixWirt_conjTranspose_holomorphic {n r : ℕ}
    (A : ComplexVector n → Matrix (Fin r) (Fin r) ℂ) (z : ComplexVector n)
    (hA : ∀ α β, DifferentiableAt ℂ (fun w => A w α β) z) (i : Fin n) :
    matrixWirt (fun w => (A w)ᴴ) z i = 0 := by
  ext α β
  change wirt (fun w => star (A w β α)) z (stdVec i) = 0
  rw [wirt_star, wirtBar_eq_zero_of_complex_differentiable _ z (stdVec i) (hA β α), star_zero]

theorem chernConnectionMatrix_comp {n r : ℕ}
    (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (T : ComplexVector n → ComplexVector n) (z : ComplexVector n)
    (hT : DifferentiableAt ℂ T z)
    (hH : ∀ α β, DifferentiableAt ℝ (fun w => H w α β) (T z)) (i : Fin n) :
    chernConnectionMatrix (fun w => H (T w)) z i =
      ∑ p, (fderiv ℂ T z (stdVec i) p) • chernConnectionMatrix H (T z) p := by
  change (H (T z))⁻¹ * matrixWirt (fun w => H (T w)) z i = _
  rw [matrixWirt_comp H T z hT hH i]
  simp only [Matrix.mul_sum, Matrix.mul_smul, chernConnectionMatrix, matrixWirt]
  rfl

theorem curvatureMatrix_comp {n r : ℕ}
    {O U : Set (ComplexVector n)} (hO : IsOpen O) (hU : IsOpen U)
    (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (T : ComplexVector n → ComplexVector n)
    (hH : ∀ α β, ContDiffOn ℝ ∞ (fun w => H w α β) U)
    (hdet : ∀ w ∈ U, (H w).det ≠ 0) (hT : ContDiffOn ℂ ∞ T O)
    (hTU : Set.MapsTo T O U) (z : ComplexVector n) (hz : z ∈ O) (i j : Fin n) :
    curvatureMatrix (fun w => H (T w)) z i j =
      ∑ p, ∑ q, (fderiv ℂ T z (stdVec i) p * star (fderiv ℂ T z (stdVec j) q)) •
        curvatureMatrix H (T z) p q := by
  let J := fun w p => fderiv ℂ T w (stdVec i) p
  let Γ := fun p w => chernConnectionMatrix H (T w) p
  have hTz : ContDiffAt ℂ ∞ T z := hT.contDiffAt (hO.mem_nhds hz)
  have hTd : DifferentiableAt ℂ T z := hTz.differentiableAt (by simp)
  have hΓd (p : Fin n) (α β : Fin r) :
      DifferentiableAt ℝ (fun w => chernConnectionMatrix H w p α β) (T z) :=
    ((chernConnectionMatrix_contDiffOn hU H hH hdet p α β).contDiffAt
      (hU.mem_nhds (hTU hz))).differentiableAt (by simp)
  have hΓcomp (p : Fin n) (α β : Fin r) : DifferentiableAt ℝ (fun w => Γ p w α β) z :=
    (hΓd p α β).comp z (hTd.restrictScalars ℝ)
  have hJd (p : Fin n) : DifferentiableAt ℂ (fun w => J w p) z := by
    have hDT : ContDiffAt ℂ ∞ (fderiv ℂ T) z := hTz.fderiv_right (m := ∞) (by simp)
    exact ((contDiffAt_piLp 2).mp (hDT.clm_apply (show ContDiffAt ℂ ∞ (fun _ : ComplexVector n => stdVec i) z from
      contDiffAt_const)) p).differentiableAt (by simp)
  have hEq : (fun w => chernConnectionMatrix (fun t => H (T t)) w i) =ᶠ[𝓝 z]
      (fun w => ∑ p, J w p • Γ p w) := by
    filter_upwards [hO.mem_nhds hz] with w hw
    apply chernConnectionMatrix_comp H T w
      ((hT.contDiffAt (hO.mem_nhds hw)).differentiableAt (by simp))
    intro α β
    exact ((hH α β).contDiffAt (hU.mem_nhds (hTU hw))).differentiableAt (by simp)
  have hbar : matrixWirtBar (fun w => chernConnectionMatrix (fun t => H (T t)) w i) z j =
      ∑ p, ∑ q, (J z p * star (fderiv ℂ T z (stdVec j) q)) •
        matrixWirtBar (fun w => chernConnectionMatrix H w p) (T z) q := by
    rw [matrixWirtBar_congr_of_eventuallyEq _ _ z hEq j]
    rw [matrixWirtBar_sum (fun p w => J w p • Γ p w) z
      (fun p α β => ((hJd p).restrictScalars ℝ).mul (hΓcomp p α β)) j]
    apply Finset.sum_congr rfl
    intro p _
    rw [matrixWirtBar_smul (fun w => J w p) (Γ p) z ((hJd p).restrictScalars ℝ)
      (hΓcomp p) j, wirtBar_eq_zero_of_complex_differentiable _ z (stdVec j) (hJd p),
      zero_smul, zero_add]
    rw [matrixWirtBar_comp (fun w => chernConnectionMatrix H w p) T z hTd (hΓd p) j]
    simp only [Finset.smul_sum, smul_smul]
  change -(H (T z) * matrixWirtBar (fun w => chernConnectionMatrix (fun t => H (T t)) w i) z j) = _
  rw [hbar]
  simp only [Matrix.mul_sum, Matrix.mul_smul, Finset.sum_neg_distrib, smul_neg,
    curvatureMatrix, matrixWirtBar]
  rfl

end Yau.LeafProofs.L14Aux
