import Yau.LeafProofs.L14Curvature

/-! Holomorphic frame changes for the metric-lowered Chern curvature. -/

noncomputable section
open scoped Topology ContDiff Matrix
open Filter

namespace Yau.LeafProofs.L14Aux
open BundleDbar

private theorem matrix_mul_differentiableAt_real {n r : ℕ}
    (A B : ComplexVector n → Matrix (Fin r) (Fin r) ℂ) (z : ComplexVector n)
    (hA : ∀ α β, DifferentiableAt ℝ (fun w => A w α β) z)
    (hB : ∀ α β, DifferentiableAt ℝ (fun w => B w α β) z) (α β : Fin r) :
    DifferentiableAt ℝ (fun w => (A w * B w) α β) z := by
  simpa only [Matrix.mul_apply, Pi.mul_apply] using
    (DifferentiableAt.fun_sum (u := Finset.univ) (fun γ _ => (hA α γ).mul (hB γ β)))

theorem matrixWirtBar_add {n r : ℕ}
    (A B : ComplexVector n → Matrix (Fin r) (Fin r) ℂ) (z : ComplexVector n)
    (hA : ∀ α β, DifferentiableAt ℝ (fun w => A w α β) z)
    (hB : ∀ α β, DifferentiableAt ℝ (fun w => B w α β) z) (i : Fin n) :
    matrixWirtBar (fun w => A w + B w) z i = matrixWirtBar A z i + matrixWirtBar B z i := by
  ext α β
  exact wirtBar_add_rule _ _ z (stdVec i) (hA α β) (hB α β)

theorem matrixWirt_holomorphic_differentiableAt {n r : ℕ}
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    (A : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (hA : ∀ α β, ContDiffOn ℂ ∞ (fun w => A w α β) O)
    (z : ComplexVector n) (hz : z ∈ O) (i : Fin n) (α β : Fin r) :
    DifferentiableAt ℂ (fun w => matrixWirt A w i α β) z := by
  have hAt : ContDiffAt ℂ ∞ (fun w => A w α β) z :=
    (hA α β).contDiffAt (hO.mem_nhds hz)
  have hD : ContDiffAt ℂ ∞ (fderiv ℂ (fun w => A w α β)) z :=
    hAt.fderiv_right (m := ∞) (by simp)
  have hd : DifferentiableAt ℂ
      (fun w => fderiv ℂ (fun t => A t α β) w (stdVec i)) z :=
    (hD.clm_apply contDiffAt_const).differentiableAt (by simp)
  apply hd.congr_of_eventuallyEq
  filter_upwards [hO.mem_nhds hz] with w hw
  exact wirt_eq_fderiv_of_complex_differentiable _ w (stdVec i)
    (((hA α β).contDiffAt (hO.mem_nhds hw)).differentiableAt (by simp))

theorem gaugeMetric_det_isUnit {r : ℕ} (H A C : Matrix (Fin r) (Fin r) ℂ)
    (hH : IsUnit H.det) (hAC : A * C = 1) : IsUnit (Aᴴ * H * A).det := by
  have hA : IsUnit A.det := by
    apply isUnit_iff_ne_zero.mpr
    intro hAz
    have he := congrArg Matrix.det hAC
    simp only [Matrix.det_mul, Matrix.det_one, hAz, zero_mul, zero_ne_one] at he
  simpa only [Matrix.det_mul, Matrix.det_conjTranspose] using (hA.star.mul hH).mul hA

theorem chernConnectionMatrix_gauge {n r : ℕ}
    (H A C : ComplexVector n → Matrix (Fin r) (Fin r) ℂ) (z : ComplexVector n)
    (hH : ∀ α β, DifferentiableAt ℝ (fun w => H w α β) z)
    (hA : ∀ α β, DifferentiableAt ℂ (fun w => A w α β) z)
    (hdet : IsUnit (H z).det) (hAC : A z * C z = 1) (i : Fin n) :
    chernConnectionMatrix (fun w => (A w)ᴴ * H w * A w) z i =
      C z * chernConnectionMatrix H z i * A z + C z * matrixWirt A z i := by
  let K := fun w => (A w)ᴴ * H w * A w
  have hAr (α β : Fin r) := (hA α β).restrictScalars ℝ
  have hAs (α β : Fin r) : DifferentiableAt ℝ (fun w => (A w)ᴴ α β) z :=
    (hAr β α).star
  have hAsH := matrix_mul_differentiableAt_real (fun w => (A w)ᴴ) H z hAs hH
  have hDK : matrixWirt K z i =
      (A z)ᴴ * matrixWirt H z i * A z + (A z)ᴴ * H z * matrixWirt A z i := by
    change matrixWirt (fun w => ((A w)ᴴ * H w) * A w) z i = _
    rw [matrixWirt_mul _ A z hAsH hAr i,
      matrixWirt_mul (fun w => (A w)ᴴ) H z hAs hH i,
      matrixWirt_conjTranspose_holomorphic A z hA i, Matrix.zero_mul, zero_add]
  have hcancel (B : Matrix (Fin r) (Fin r) ℂ) : A z * (C z * B) = B := by
    rw [← Matrix.mul_assoc, hAC, Matrix.one_mul]
  have hright : K z *
      (C z * chernConnectionMatrix H z i * A z + C z * matrixWirt A z i) =
      matrixWirt K z i := by
    calc
      _ = (A z)ᴴ * (H z * chernConnectionMatrix H z i) * A z +
          (A z)ᴴ * H z * matrixWirt A z i := by
        simp only [K, Matrix.mul_add, Matrix.mul_assoc, hcancel]
      _ = _ := by
        rw [chernConnection_lower H z hdet i]
        exact hDK.symm
  have hunitK : IsUnit (K z).det := gaugeMetric_det_isUnit (H z) (A z) (C z) hdet hAC
  have he := congrArg (fun B : Matrix (Fin r) (Fin r) ℂ => (K z)⁻¹ * B)
    ((chernConnection_lower K z hunitK i).trans hright.symm)
  simpa only [Matrix.nonsing_inv_mul_cancel_left _ _ hunitK] using he

theorem curvatureMatrix_gauge {n r : ℕ}
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    (H A C : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (hH : ∀ α β, ContDiffOn ℝ ∞ (fun w => H w α β) O)
    (hdet : ∀ w ∈ O, (H w).det ≠ 0)
    (hA : ∀ α β, ContDiffOn ℂ ∞ (fun w => A w α β) O)
    (hC : ∀ α β, ContDiffOn ℂ ∞ (fun w => C w α β) O)
    (hAC : ∀ w ∈ O, A w * C w = 1)
    (z : ComplexVector n) (hz : z ∈ O) (i j : Fin n) :
    curvatureMatrix (fun w => (A w)ᴴ * H w * A w) z i j =
      (A z)ᴴ * curvatureMatrix H z i j * A z := by
  let Γ := fun w => chernConnectionMatrix H w i
  let D := fun w => matrixWirt A w i
  have hAz (α β : Fin r) : DifferentiableAt ℂ (fun w => A w α β) z :=
    ((hA α β).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
  have hCz (α β : Fin r) : DifferentiableAt ℂ (fun w => C w α β) z :=
    ((hC α β).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
  have hDz (α β : Fin r) : DifferentiableAt ℂ (fun w => D w α β) z :=
    matrixWirt_holomorphic_differentiableAt hO A hA z hz i α β
  have hΓz (α β : Fin r) : DifferentiableAt ℝ (fun w => Γ w α β) z :=
    ((chernConnectionMatrix_contDiffOn hO H hH hdet i α β).contDiffAt
      (hO.mem_nhds hz)).differentiableAt (by simp)
  have hAr (α β : Fin r) := (hAz α β).restrictScalars ℝ
  have hCr (α β : Fin r) := (hCz α β).restrictScalars ℝ
  have hDr (α β : Fin r) := (hDz α β).restrictScalars ℝ
  have hCΓ := matrix_mul_differentiableAt_real C Γ z hCr hΓz
  have hCΓA := matrix_mul_differentiableAt_real (fun w => C w * Γ w) A z hCΓ hAr
  have hCD := matrix_mul_differentiableAt_real C D z hCr hDr
  have hEq :
      (fun w => chernConnectionMatrix (fun t => (A t)ᴴ * H t * A t) w i) =ᶠ[𝓝 z]
      (fun w => C w * Γ w * A w + C w * D w) := by
    filter_upwards [hO.mem_nhds hz] with w hw
    exact chernConnectionMatrix_gauge H A C w
      (fun α β => ((hH α β).contDiffAt (hO.mem_nhds hw)).differentiableAt (by simp))
      (fun α β => ((hA α β).contDiffAt (hO.mem_nhds hw)).differentiableAt (by simp))
      (isUnit_iff_ne_zero.mpr (hdet w hw)) (hAC w hw) i
  have hbar :
      matrixWirtBar (fun w => chernConnectionMatrix (fun t => (A t)ᴴ * H t * A t) w i) z j =
      C z * matrixWirtBar Γ z j * A z := by
    rw [matrixWirtBar_congr_of_eventuallyEq _ _ z hEq j,
      matrixWirtBar_add _ _ z hCΓA hCD j,
      matrixWirtBar_mul (fun w => C w * Γ w) A z hCΓ hAr j,
      matrixWirtBar_mul C Γ z hCr hΓz j,
      matrixWirtBar_mul C D z hCr hDr j,
      matrixWirtBar_holomorphic C z hCz j,
      matrixWirtBar_holomorphic A z hAz j,
      matrixWirtBar_holomorphic D z hDz j]
    simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero]
  have hcancel (B : Matrix (Fin r) (Fin r) ℂ) : A z * (C z * B) = B := by
    rw [← Matrix.mul_assoc, hAC z hz, Matrix.one_mul]
  change -(((A z)ᴴ * H z * A z) *
    matrixWirtBar (fun w => chernConnectionMatrix (fun t => (A t)ᴴ * H t * A t) w i) z j) = _
  rw [hbar]
  change -(((A z)ᴴ * H z * A z) * (C z * matrixWirtBar Γ z j * A z)) =
    (A z)ᴴ * (-(H z * matrixWirtBar Γ z j)) * A z
  simp only [Matrix.mul_assoc, hcancel, Matrix.mul_neg, Matrix.neg_mul]

theorem curvatureMatrix_holomorphic_change {n r : ℕ}
    {O U : Set (ComplexVector n)} (hO : IsOpen O) (hU : IsOpen U)
    (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (T : ComplexVector n → ComplexVector n)
    (A C : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (hH : ∀ α β, ContDiffOn ℝ ∞ (fun w => H w α β) U)
    (hdet : ∀ w ∈ U, (H w).det ≠ 0)
    (hT : ContDiffOn ℂ ∞ T O) (hTU : Set.MapsTo T O U)
    (hA : ∀ α β, ContDiffOn ℂ ∞ (fun w => A w α β) O)
    (hC : ∀ α β, ContDiffOn ℂ ∞ (fun w => C w α β) O)
    (hAC : ∀ w ∈ O, A w * C w = 1)
    (z : ComplexVector n) (hz : z ∈ O) (i j : Fin n) :
    curvatureMatrix (fun w => (A w)ᴴ * H (T w) * A w) z i j =
      (A z)ᴴ * (∑ p, ∑ q,
        (fderiv ℂ T z (stdVec i) p * star (fderiv ℂ T z (stdVec j) q)) •
          curvatureMatrix H (T z) p q) * A z := by
  have hHT (α β : Fin r) : ContDiffOn ℝ ∞ (fun w => H (T w) α β) O :=
    (hH α β).comp (hT.restrict_scalars ℝ) hTU
  rw [curvatureMatrix_gauge hO (fun w => H (T w)) A C hHT
    (fun w hw => hdet (T w) (hTU hw)) hA hC hAC z hz i j,
    curvatureMatrix_comp hO hU H T hH hdet hT hTU z hz i j]

end Yau.LeafProofs.L14Aux
