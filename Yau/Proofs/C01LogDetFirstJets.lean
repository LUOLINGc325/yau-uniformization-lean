import Yau.Proofs.C01DeterminantFirstJets

/-! The real log determinant and the holomorphic scalar logarithm agree
on the actual positive metric matrices.  Its first jets therefore obey
Jacobi's formula without an additional trace or curvature premise. -/

noncomputable section

open scoped Topology ContDiff Matrix ComplexOrder
open Filter

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem positive_matrix_logDet_eq_log (H : Herm n) (hH : H.PosDef) :
    (Real.log H.det.re : ℂ) = Complex.log H.det := by
  have hp := Complex.pos_iff.mp hH.det_pos
  have hre : (H.det.re : ℂ) = H.det := by
    apply Complex.ext
    · simp only [Complex.ofReal_re]
    · simpa only [Complex.ofReal_im] using hp.2
  rw [Complex.ofReal_log hp.1.le, hre]

theorem matrix_logDet_wirtinger
    (H : V → Herm n) (s : Set V) (hs : IsOpen s)
    (hpos : ∀ p ∈ s, (H p).PosDef) (z v : V) (hz : z ∈ s)
    (hH : DifferentiableAt ℝ H z) :
    wirt (fun p => (Real.log (H p).det.re : ℂ)) z v =
      Matrix.trace ((H z)⁻¹ *
        (Matrix.of fun i j => wirt (fun p => H p i j) z v)) ∧
    wirtBar (fun p => (Real.log (H p).det.re : ℂ)) z v =
      Matrix.trace ((H z)⁻¹ *
        (Matrix.of fun i j => wirtBar (fun p => H p i j) z v)) := by
  have hgerm : (fun p => (Real.log (H p).det.re : ℂ)) =ᶠ[𝓝 z]
      (fun p => Complex.log (H p).det) := by
    filter_upwards [hs.mem_nhds hz] with p hp
    exact positive_matrix_logDet_eq_log (H p) (hpos p hp)
  have hd : DifferentiableAt ℝ (fun p => (H p).det) z :=
    ((((determinantMultilinear n).hasFDerivAt (H z)).restrictScalars ℝ).comp
      z hH.hasFDerivAt).differentiableAt
  have hslit : (H z).det ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (Complex.pos_iff.mp (hpos z hz).det_pos).1)
  have hchain := scalar_holomorphic_outer_wirtinger
    (fun p => (H p).det) Complex.log z v (H z).det⁻¹ hd
      (Complex.hasDerivAt_log hslit)
  have hunit : IsUnit (H z).det := (hpos z hz).isUnit.map Matrix.detMonoidHom
  constructor
  · rw [wirt_congr_germ hgerm v, hchain.1, determinant_wirt H z v hH hunit,
      ← mul_assoc, inv_mul_cancel₀ hunit.ne_zero, one_mul]
  · rw [wirtBar_congr_germ hgerm v, hchain.2, determinant_wirtBar H z v hH hunit,
      ← mul_assoc, inv_mul_cancel₀ hunit.ne_zero, one_mul]

end Yau.NodeProofs.C01Aux
