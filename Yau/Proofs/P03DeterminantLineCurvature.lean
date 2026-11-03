import Yau.LeafProofs.L07

open scoped Manifold Topology ContDiff ComplexOrder Matrix
open Filter Yau.LeafProofs.L07Aux

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar

variable {n r : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem constant_finOne_matrix (d : ℂ) :
    (show Matrix (Fin 1) (Fin 1) ℂ from fun _ _ => d) = d • 1 := by
  ext a b
  have hab : a = b := Subsingleton.elim _ _
  subst b
  simp

theorem constant_finOne_matrix_inv (d : ℂ) (hd : d ≠ 0) (a b : Fin 1) :
    (show Matrix (Fin 1) (Fin 1) ℂ from fun _ _ => d)⁻¹ a b = d⁻¹ := by
  letI : Invertible d := invertibleOfNonzero hd
  have he : (d • (1 : Matrix (Fin 1) (Fin 1) ℂ))⁻¹ = d⁻¹ • 1 :=
    (Matrix.inv_smul (A := (1 : Matrix (Fin 1) (Fin 1) ℂ)) d (by simp)).trans
      (by simp only [invOf_eq_inv, inv_one])
  have hc := congrArg (fun A : Matrix (Fin 1) (Fin 1) ℂ => A a b) he
  have hab : a = b := Subsingleton.elim _ _
  have hv : (d⁻¹ • (1 : Matrix (Fin 1) (Fin 1) ℂ)) a b = d⁻¹ := by
    subst b
    simp
  exact (congrArg (fun A : Matrix (Fin 1) (Fin 1) ℂ => A⁻¹ a b)
    (constant_finOne_matrix d)).trans (hc.trans hv)

theorem chernConnectionMatrix_determinantLine
    (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ) (z : ComplexVector n)
    (hH : DifferentiableAt ℝ H z) (hdet : (H z).det ≠ 0) (i : Fin n) (a b : Fin 1) :
    chernConnectionMatrix (fun w => fun _ _ : Fin 1 => (H w).det) z i a b =
      Matrix.trace (chernConnectionMatrix H z i) := by
  simp only [chernConnectionMatrix, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_one]
  have he := constant_finOne_matrix_inv (H z).det hdet a 0
  calc
    _ = (H z).det⁻¹ * wirt (fun w => (H w).det) z (stdVec i) :=
      congrArg (fun c : ℂ => c * wirt (fun w => (H w).det) z (stdVec i)) he
    _ = _ := by
      rw [determinant_wirt H z (stdVec i) hH (isUnit_iff_ne_zero.mpr hdet)]
      field_simp

/-- The determinant line uses the actual metric `det H`; its curvature is
the trace of the metric-raised curvature of `H`, with the determinant factor. -/
theorem curvatureMatrix_determinantLine {s : Set (ComplexVector n)} (hs : IsOpen s)
    (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (hH : ContDiffOn ℝ ∞ H s) (hdet : ∀ w ∈ s, (H w).det ≠ 0)
    (z : ComplexVector n) (hz : z ∈ s) (i j : Fin n) (a b : Fin 1) :
    curvatureMatrix (fun w => fun _ _ : Fin 1 => (H w).det) z i j a b =
      (H z).det * Matrix.trace ((H z)⁻¹ * curvatureMatrix H z i j) := by
  let A := fun w => chernConnectionMatrix H w i
  let B : Matrix (Fin r) (Fin r) ℂ :=
    Matrix.of fun α β => wirtBar (fun w => A w α β) z (stdVec j)
  have hA : DifferentiableAt ℝ A z :=
    ((chernConnectionMatrix_contDiffOn hs H hH hdet i).differentiableOn (by simp)).differentiableAt
      (hs.mem_nhds hz)
  have he : (fun w => chernConnectionMatrix
      (fun t => fun _ _ : Fin 1 => (H t).det) w i a b) =ᶠ[𝓝 z]
        (fun w => Matrix.trace (A w)) := by
    filter_upwards [hs.mem_nhds hz] with w hw
    exact chernConnectionMatrix_determinantLine H w
      ((hH.differentiableOn (by simp)).differentiableAt (hs.mem_nhds hw)) (hdet w hw) i a b
  have htrace : Matrix.trace ((H z)⁻¹ * curvatureMatrix H z i j) = -Matrix.trace B := by
    change Matrix.trace ((H z)⁻¹ * -(H z * B)) = -Matrix.trace B
    rw [Matrix.mul_neg, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hdet z hz)), Matrix.one_mul,
      Matrix.trace_neg]
  rw [htrace]
  have ha : a = 0 := Subsingleton.elim _ _
  have hb : b = 0 := Subsingleton.elim _ _
  subst a
  subst b
  change -(∑ α : Fin 1, (H z).det * wirtBar
    (fun w => chernConnectionMatrix (fun t => fun _ _ : Fin 1 => (H t).det) w i α 0)
      z (stdVec j)) = _
  rw [Fin.sum_univ_one, wirtBar_eventuallyEq he, wirtBar_trace A z (stdVec j) hA]
  exact (mul_neg _ _).symm

end Yau.NodeProofs.P03Aux
