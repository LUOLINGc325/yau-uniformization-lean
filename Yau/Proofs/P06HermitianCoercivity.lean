import Yau.Proofs.P06OrderAlgebra

noncomputable section
open scoped Topology ComplexOrder MatrixOrder

namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint Matrix

theorem hermitian_coordinate_norm_sq_le {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.PosDef) (v : Fin n → ℂ) (i : Fin n) :
    ‖v i‖ ^ 2 ≤ (H⁻¹ i i).re * (star v ⬝ᵥ (H *ᵥ v)).re := by
  classical
  let e : Fin n → ℂ := Pi.single i 1
  let w := H⁻¹ *ᵥ e
  have hdet : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det _).mp hH.isUnit
  have hw : H *ᵥ w = e := by
    dsimp only [w]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv H hdet, Matrix.one_mulVec]
  have hwi : w i = H⁻¹ i i := by
    simp only [w, e, Matrix.mulVec_single_one, Matrix.col_apply]
  have h := hH.star_dotProduct_mulVec_mul_le v w
  simp only [hw, e, dotProduct_single_one, Pi.star_apply, star_star] at h
  have hr := (Complex.le_def.mp h).1
  have hqim : (star v ⬝ᵥ (H *ᵥ v)).im = 0 := by
    simpa only [RCLike.im_eq_complex_im] using hH.isHermitian.im_star_dotProduct_mulVec_self v
  rw [hwi] at hr
  simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    hqim, zero_mul, sub_zero] at hr
  rw [Complex.sq_norm, Complex.normSq_apply]
  nlinarith

/-- The actual Hermitian chart metric has a uniform positive quadratic
lower bound on each compact coordinate set. -/
theorem hMat_uniform_coercivity {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (x : M.Carrier) {K : Set (ComplexVector n)}
    (hK : IsCompact K) (hKO : K ⊆ chartTarget x) :
    ∃ ell : ℝ, 0 < ell ∧ ∀ z ∈ K, ∀ v : Fin n → ℂ,
      ell * (∑ i, ‖v i‖ ^ 2) ≤ leviDirection (hMat g.form x z) (WithLp.toLp 2 v) := by
  have hc : ContinuousOn (fun z => ∑ i, ‖(hMat g.form x z)⁻¹ i i‖) K :=
    continuousOn_finsetSum Finset.univ (fun i _ =>
      ((Yau.LeafProofs.L18Aux.hMat_inverse_contDiffOn g x i i).continuousOn.mono hKO).norm)
  obtain ⟨d, hd⟩ := hK.bddAbove_image hc
  let D : ℝ := max d 0 + 1
  have hD : 0 < D := by dsimp only [D]; linarith [le_max_right d 0]
  refine ⟨D⁻¹, inv_pos.mpr hD, ?_⟩
  intro z hz v
  have hH := Yau.LeafProofs.L12Aux.hMat_posDef g.form x z (hKO hz)
  let Q := leviDirection (hMat g.form x z) (WithLp.toLp 2 v)
  have hQ : 0 ≤ Q := by
    simpa only [Q, leviDirection, WithLp.ofLp_toLp, RCLike.re_eq_complex_re] using
      hH.posSemidef.re_dotProduct_nonneg v
  have hs : (∑ i, ‖v i‖ ^ 2) ≤ (∑ i, ‖(hMat g.form x z)⁻¹ i i‖) * Q := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    have hi := hermitian_coordinate_norm_sq_le _ hH v i
    change ‖v i‖ ^ 2 ≤ ((hMat g.form x z)⁻¹ i i).re * Q at hi
    exact hi.trans (mul_le_mul_of_nonneg_right (Complex.re_le_norm _) hQ)
  have hdD : (∑ i, ‖(hMat g.form x z)⁻¹ i i‖) ≤ D := by
    have h := hd ⟨z, hz, rfl⟩
    dsimp only [D]
    linarith [le_max_left d 0]
  have hfinal := hs.trans (mul_le_mul_of_nonneg_right hdD hQ)
  have hdiv : (∑ i, ‖v i‖ ^ 2) / D ≤ Q :=
    (div_le_iff₀ hD).mpr (by simpa only [mul_comm] using hfinal)
  simpa only [div_eq_mul_inv, mul_comm, Q] using hdiv

end Yau.NodeProofs.P06Aux
