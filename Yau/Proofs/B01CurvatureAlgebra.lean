import Yau.Proofs.B01Coordinate
import Yau.LeafProofs.L14Gauge

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Set Filter

noncomputable section

namespace Yau.Proofs.B01Aux
open Yau Yau.Blueprint Yau.Blueprint.BundlePresentation BundleDbar
open LeafProofs.L14Aux

theorem curvatureMatrix_lowered {n r : ℕ} {O : Set (ComplexVector n)}
    (hO : IsOpen O) (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (hH : ∀ α β, ContDiffOn ℝ ∞ (fun w => H w α β) O)
    (hdet : ∀ w ∈ O, (H w).det ≠ 0) (z : ComplexVector n) (hz : z ∈ O) (i j : Fin n) :
    curvatureMatrix H z i j =
      -matrixWirtBar (fun w => matrixWirt H w i) z j +
        matrixWirtBar H z j * ((H z)⁻¹ * matrixWirt H z i) := by
  let Γ : ComplexVector n → Matrix (Fin r) (Fin r) ℂ := fun w => chernConnectionMatrix H w i
  have hlocal : (fun w => H w * Γ w) =ᶠ[𝓝 z] (fun w => matrixWirt H w i) := by
    filter_upwards [hO.mem_nhds hz] with w hw
    exact chernConnection_lower H w (isUnit_iff_ne_zero.mpr (hdet w hw)) i
  have hl := matrixWirtBar_congr_of_eventuallyEq _ _ z hlocal j
  have hdH (α β : Fin r) := ((hH α β).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
  have hdΓ (α β : Fin r) :=
    ((chernConnectionMatrix_contDiffOn hO H hH hdet i α β).contDiffAt
      (hO.mem_nhds hz)).differentiableAt (by simp)
  rw [matrixWirtBar_mul H Γ z hdH hdΓ j] at hl
  calc
    curvatureMatrix H z i j =
        -matrixWirtBar (fun w => matrixWirt H w i) z j + matrixWirtBar H z j * Γ z := by
      change -(H z * matrixWirtBar Γ z j) = _
      rw [← hl]
      abel
    _ = _ := rfl

theorem complexOneEquiv_symm_stdVec : complexOneEquiv.symm (stdVec 0) = (1 : ℂ) := by
  have he : complexOneEquiv (1 : ℂ) = stdVec 0 := by
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [stdVec]
  rw [← he, complexOneEquiv.symm_apply_apply]

private def oneSymmRealEquiv : ComplexVector 1 ≃L[ℝ] ℂ :=
  { complexOneEquiv.symm.toLinearEquiv.restrictScalars ℝ with
    continuous_toFun := complexOneEquiv.symm.continuous
    continuous_invFun := complexOneEquiv.continuous }

theorem wirt_comp_one_symm (f : ℂ → ℂ) (z v : ComplexVector 1) :
    wirt (fun w => f (complexOneEquiv.symm w)) z v =
      wirt f (complexOneEquiv.symm z) (complexOneEquiv.symm v) := by
  let e : ComplexVector 1 ≃L[ℂ] ℂ := complexOneEquiv.symm.toContinuousLinearEquiv
  have hd : fderiv ℝ (fun w => f (complexOneEquiv.symm w)) z =
      (fderiv ℝ f (complexOneEquiv.symm z)).comp oneSymmRealEquiv.toContinuousLinearMap :=
    oneSymmRealEquiv.comp_right_fderiv
  unfold wirt
  rw [hd]
  change (1 / 2 : ℂ) * (fderiv ℝ f (e z) (e v) -
    Complex.I * fderiv ℝ f (e z) (e (Complex.I • v))) = _
  rw [e.map_smul]
  rfl

theorem wirtBar_comp_one_symm (f : ℂ → ℂ) (z v : ComplexVector 1) :
    wirtBar (fun w => f (complexOneEquiv.symm w)) z v =
      wirtBar f (complexOneEquiv.symm z) (complexOneEquiv.symm v) := by
  let e : ComplexVector 1 ≃L[ℂ] ℂ := complexOneEquiv.symm.toContinuousLinearEquiv
  have hd : fderiv ℝ (fun w => f (complexOneEquiv.symm w)) z =
      (fderiv ℝ f (complexOneEquiv.symm z)).comp oneSymmRealEquiv.toContinuousLinearMap :=
    oneSymmRealEquiv.comp_right_fderiv
  unfold wirtBar
  rw [hd]
  change (1 / 2 : ℂ) * (fderiv ℝ f (e z) (e v) +
    Complex.I * fderiv ℝ f (e z) (e (Complex.I • v))) = _
  rw [e.map_smul]
  rfl

theorem wirt_one_symm (f : ℂ → ℂ) (z : ComplexVector 1) :
    wirt (fun w => f (complexOneEquiv.symm w)) z (stdVec 0) =
      wirt f (complexOneEquiv.symm z) 1 := by
  rw [wirt_comp_one_symm, complexOneEquiv_symm_stdVec]

theorem wirtBar_one_symm (f : ℂ → ℂ) (z : ComplexVector 1) :
    wirtBar (fun w => f (complexOneEquiv.symm w)) z (stdVec 0) =
      wirtBar f (complexOneEquiv.symm z) 1 := by
  rw [wirtBar_comp_one_symm, complexOneEquiv_symm_stdVec]

theorem scalar_curvatureMatrix_eq {r : ℕ} (K : ℂ → Matrix (Fin r) (Fin r) ℂ)
    (U : Set ℂ) (hU : IsOpen U) (hK : ∀ α β, ContDiffOn ℝ ∞ (fun z => K z α β) U)
    (hdet : ∀ z ∈ U, (K z).det ≠ 0) (z : ℂ) (hz : z ∈ U) :
    curvatureMatrix (fun w => K (complexOneEquiv.symm w)) (complexOneEquiv z) 0 0 =
      fun α β => -wirtBar (fun w => wirt (fun u => K u α β) w 1) z 1 +
        ∑ p, ∑ l, wirtBar (fun w => K w α p) z 1 * (K z)⁻¹ p l *
          wirt (fun w => K w l β) z 1 := by
  let O : Set (ComplexVector 1) := complexOneEquiv.symm ⁻¹' U
  have hO : IsOpen O := hU.preimage complexOneEquiv.symm.continuous
  have hKO (α β : Fin r) : ContDiffOn ℝ ∞ (fun w => K (complexOneEquiv.symm w) α β) O :=
    (hK α β).comp (complexOneEquiv.symm.toContinuousLinearEquiv.contDiff.restrict_scalars ℝ).contDiffOn
      (fun _ hw => hw)
  have hdetO : ∀ w ∈ O, (K (complexOneEquiv.symm w)).det ≠ 0 := fun w hw => hdet _ hw
  have hzO : complexOneEquiv z ∈ O := by simpa only [O, mem_preimage, complexOneEquiv.symm_apply_apply] using hz
  have hW (w : ComplexVector 1) (α β : Fin r) :
      wirt (fun u => K (complexOneEquiv.symm u) α β) w (stdVec 0) =
        wirt (fun u => K u α β) (complexOneEquiv.symm w) 1 :=
    wirt_one_symm (fun u => K u α β) w
  have hB (w : ComplexVector 1) (α β : Fin r) :
      wirtBar (fun u => K (complexOneEquiv.symm u) α β) w (stdVec 0) =
        wirtBar (fun u => K u α β) (complexOneEquiv.symm w) 1 :=
    wirtBar_one_symm (fun u => K u α β) w
  have hWB (w : ComplexVector 1) (α β : Fin r) :
      wirtBar (fun t => wirt (fun u => K (complexOneEquiv.symm u) α β) t (stdVec 0)) w (stdVec 0) =
        wirtBar (fun t : ℂ => wirt (fun u => K u α β) t 1) (complexOneEquiv.symm w) 1 := by
    simp_rw [hW]
    exact wirtBar_one_symm (fun t : ℂ => wirt (fun u => K u α β) t 1) w
  rw [curvatureMatrix_lowered hO _ hKO hdetO _ hzO 0 0]
  ext α β
  simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.mul_apply, matrixWirtBar, matrixWirt]
  rw [hWB]
  simp only [hW, hB, complexOneEquiv.symm_apply_apply, Finset.mul_sum, mul_assoc]

theorem wirtBar_congr_of_eventuallyEq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {f g : V → ℂ} {z : V} (he : f =ᶠ[𝓝 z] g) (v : V) : wirtBar f z v = wirtBar g z v := by
  unfold wirtBar
  rw [he.fderiv_eq]

theorem matrixWirtBar_eq_adjoint {n r : ℕ} {O : Set (ComplexVector n)}
    (hO : IsOpen O) (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (hHerm : ∀ w ∈ O, (H w).IsHermitian) (z : ComplexVector n) (hz : z ∈ O) (i : Fin n) :
    matrixWirtBar H z i = (matrixWirt H z i)ᴴ := by
  ext α β
  change wirtBar (fun w => H w α β) z (stdVec i) =
    star (wirt (fun w => H w β α) z (stdVec i))
  have he : (fun w => H w α β) =ᶠ[𝓝 z] (fun w => star (H w β α)) := by
    filter_upwards [hO.mem_nhds hz] with w hw
    exact (congrArg (fun A : Matrix (Fin r) (Fin r) ℂ => A α β) (hHerm w hw).eq).symm
  rw [wirtBar_congr_of_eventuallyEq he, wirtBar_star]

theorem matrixMixed_isHermitian {n r : ℕ} {O : Set (ComplexVector n)}
    (hO : IsOpen O) (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (hH : ∀ α β, ContDiffOn ℝ ∞ (fun w => H w α β) O)
    (hHerm : ∀ w ∈ O, (H w).IsHermitian) (z : ComplexVector n) (hz : z ∈ O) (i : Fin n) :
    (matrixWirtBar (fun w => matrixWirt H w i) z i).IsHermitian := by
  have hval (α β : Fin r) :
      wirtBar (fun w => wirt (fun t => H t α β) w (stdVec i)) z (stdVec i) =
        star (wirtBar (fun w => wirt (fun t => H t β α) w (stdVec i)) z (stdVec i)) := by
    have hinner : (fun w => wirt (fun t => H t α β) w (stdVec i)) =ᶠ[𝓝 z]
        (fun w => star (wirtBar (fun t => H t β α) w (stdVec i))) := by
      filter_upwards [hO.mem_nhds hz] with w hw
      have he : (fun t => H t α β) =ᶠ[𝓝 w] (fun t => star (H t β α)) := by
        filter_upwards [hO.mem_nhds hw] with t ht
        exact (congrArg (fun A : Matrix (Fin r) (Fin r) ℂ => A α β) (hHerm t ht).eq).symm
      calc
        wirt (fun t => H t α β) w (stdVec i) =
            wirt (fun t => star (H t β α)) w (stdVec i) := by
          unfold wirt
          rw [he.fderiv_eq]
        _ = _ := wirt_star _ _ _
    rw [wirtBar_congr_of_eventuallyEq hinner, wirtBar_star,
      wirt_wirtBar_comm (fun t => H t β α) z
        (((hH β α).contDiffAt (hO.mem_nhds hz)).of_le (by norm_num))]
  ext α β
  exact (hval α β).symm

theorem curvatureMatrix_diagonal_isHermitian {n r : ℕ} {O : Set (ComplexVector n)}
    (hO : IsOpen O) (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (hH : ∀ α β, ContDiffOn ℝ ∞ (fun w => H w α β) O)
    (hdet : ∀ w ∈ O, (H w).det ≠ 0) (hHerm : ∀ w ∈ O, (H w).IsHermitian)
    (z : ComplexVector n) (hz : z ∈ O) (i : Fin n) : (curvatureMatrix H z i i).IsHermitian := by
  rw [curvatureMatrix_lowered hO H hH hdet z hz i i, matrixWirtBar_eq_adjoint hO H hHerm z hz i,
    ← Matrix.mul_assoc]
  exact (matrixMixed_isHermitian hO H hH hHerm z hz i).neg.add
    (Matrix.isHermitian_conjTranspose_mul_mul _ (hHerm z hz).inv)

theorem matrix_posSemidef_of_real_nonnegative {r : ℕ} (R : Matrix (Fin r) (Fin r) ℂ)
    (hHerm : R.IsHermitian)
    (hR : ∀ v : Fin r → ℂ, 0 ≤ (star v ⬝ᵥ (R *ᵥ v)).re) : R.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm
  intro v
  apply Complex.nonneg_iff.mpr
  refine ⟨hR v, ?_⟩
  have hi := congrArg Complex.im (hHerm.star_dotProduct_mulVec_comm v v)
  simp only [Complex.star_def, Complex.conj_im] at hi
  linarith

end Yau.Proofs.B01Aux
