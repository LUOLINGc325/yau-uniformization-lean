import Yau.Proofs.Y01GermSandwich
import Yau.Proofs.Y03Frames

/-! The first component of the original germ identity is the actual
matrix conjugacy, so inverse bounds use the original center derivative. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open Yau.Blueprint Yau.Blueprint.Alignment Yau.Blueprint.Alignment.Y03Proof
open Yau.Proofs.Y02Aux
open scoped ContDiff Matrix.Norms.L2Operator

variable {n d : ℕ}

theorem matrix_toEuclideanCLM_ring_coe (A : Herm n) :
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).toRingEquiv A =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A := rfl

theorem germJetEq_fderiv {f g : ComplexVector n → ComplexVector n}
    (hd : 1 ≤ d) (h : GermJetEq f g d) : fderiv ℂ f 0 = fderiv ℂ g 0 := by
  apply ContinuousLinearMap.ext
  intro z
  have hz := congrArg (fun p => p (fun _ : Fin 1 => z)) (h 1 hd)
  simpa only [iteratedFDeriv_one_apply] using hz

theorem matrix_toEuclideanCLM_inverse {A : Herm n} (hA : IsUnit A) :
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A).inverse =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A⁻¹ := by
  apply ContinuousLinearMap.inverse_eq
  · change Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A *
        Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A⁻¹ = 1
    rw [← map_mul, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hA), map_one]
  · change Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A⁻¹ *
        Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A = 1
    rw [← map_mul, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hA), map_one]

theorem original_transition_inverse_bound
    {X : KahlerManifold n} {o : Pt X} {h : Flow X} {ρ : STF X}
    {r₀ r₁ σ C Cb t₀ : ℝ} {Φ : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {f : ℝ → Pt X → ComplexVector n}
    (hcharts : ShrinkingCharts X o h ρ r₀ r₁ σ C Cb t₀ Φ F f)
    {t t' : ℝ} (ht : t₀ ≤ t) (htt' : t ≤ t') :
    IsUnit (derivativeMatrix (F t t')) ∧
      matOpNorm (derivativeMatrix (F t t'))⁻¹ ≤ Real.exp ((ρ o t' - ρ o t) / 2) := by
  have hstep := hcharts.2.2.2.2.2.1 t t' ht htt'
  have hdet : ‖(derivativeMatrix (F t t')).det‖ = Real.exp (-(ρ o t' - ρ o t) / 2) := by
    rw [derivativeMatrix_det]
    exact hstep.2.2.2.2.2.1
  have hunit : IsUnit (derivativeMatrix (F t t')) := by
    apply (Matrix.isUnit_iff_isUnit_det _).2
    apply isUnit_iff_ne_zero.2
    intro hz
    rw [hz, norm_zero] at hdet
    exact (ne_of_gt (Real.exp_pos _)) hdet.symm
  refine ⟨hunit, ?_⟩
  have hInv := matrix_toEuclideanCLM_inverse hunit
  rw [derivativeMatrix_toEuclideanCLM] at hInv
  unfold matOpNorm
  rw [← hInv]
  exact hstep.2.2.2.2.2.2

set_option backward.isDefEq.respectTransparency false in
theorem center_conjugacy
    {H Hnext G : PolyMap n} {F : ComplexVector n → ComplexVector n}
    (hd : 1 ≤ d) (hF : DifferentiableAt ℂ F 0) (hF0 : F 0 = 0)
    (hH : H.FixesZero)
    (hjet : GermJetEq (Hnext.eval ∘ F) (G.eval ∘ H.eval) d) :
    Hnext.linearPart * derivativeMatrix F = G.linearPart * H.linearPart := by
  have hH0 := (fixesZero_iff_eval_zero _).1 hH
  have hN : DifferentiableAt ℂ Hnext.eval (F 0) :=
    (polyMap_eval_contDiff Hnext).differentiable (by simp) _
  have hG : DifferentiableAt ℂ G.eval (H.eval 0) :=
    (polyMap_eval_contDiff G).differentiable (by simp) _
  have hHd : DifferentiableAt ℂ H.eval 0 :=
    (polyMap_eval_contDiff H).differentiable (by simp) _
  have h := germJetEq_fderiv hd hjet
  rw [fderiv_comp 0 hN hF, fderiv_comp 0 hG hHd, hF0, hH0,
    fderiv_polyMap_eval, fderiv_polyMap_eval, fderiv_polyMap_eval,
    ] at h
  have hD : fderiv ℂ F 0 = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (derivativeMatrix F) := by
    simpa only [centerDeriv] using (derivativeMatrix_toEuclideanCLM F).symm
  rw [hD] at h
  apply (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).injective
  rw [map_mul, map_mul]
  apply ContinuousLinearMap.ext
  intro z
  have hz := congrArg (fun L => L z) h
  simpa only [matrix_toEuclideanCLM_ring_coe, ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply] using hz

set_option backward.isDefEq.respectTransparency false in
theorem transition_jet_linearPart
    {J Hnext Hinv : PolyMap n} {F : ComplexVector n → ComplexVector n}
    (hd : 1 ≤ d) (hF : DifferentiableAt ℂ F 0) (hF0 : F 0 = 0)
    (hI : Hinv.FixesZero)
    (hjet : GermJetEq J.eval (Hnext.eval ∘ F ∘ Hinv.eval) d) :
    J.linearPart = Hnext.linearPart * derivativeMatrix F * Hinv.linearPart := by
  have hI0 := (fixesZero_iff_eval_zero _).1 hI
  have hN : DifferentiableAt ℂ Hnext.eval (F 0) :=
    (polyMap_eval_contDiff Hnext).differentiable (by simp) _
  have hOuter : DifferentiableAt ℂ (Hnext.eval ∘ F) 0 := hN.comp 0 hF
  have hOuterI : DifferentiableAt ℂ (Hnext.eval ∘ F) (Hinv.eval 0) := by
    simpa only [hI0] using hOuter
  have hId : DifferentiableAt ℂ Hinv.eval 0 :=
    (polyMap_eval_contDiff Hinv).differentiable (by simp) _
  have h := germJetEq_fderiv hd hjet
  change fderiv ℂ J.eval 0 = fderiv ℂ ((Hnext.eval ∘ F) ∘ Hinv.eval) 0 at h
  rw [fderiv_comp 0 hOuterI hId, hI0, fderiv_comp 0 hN hF, hF0,
    fderiv_polyMap_eval, fderiv_polyMap_eval, fderiv_polyMap_eval,
    ] at h
  have hD : fderiv ℂ F 0 = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (derivativeMatrix F) := by
    simpa only [centerDeriv] using (derivativeMatrix_toEuclideanCLM F).symm
  rw [hD] at h
  apply (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).injective
  simp only [map_mul]
  apply ContinuousLinearMap.ext
  intro z
  have hz := congrArg (fun L => L z) h
  simpa only [matrix_toEuclideanCLM_ring_coe, ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply] using hz

theorem model_inverse_bound_of_conjugacy
    {T Tnext D B : Herm n} (hT : IsUnit T)
    (hconj : Tnext * D = B * T) :
    matOpNorm B⁻¹ ≤ matOpNorm T * matOpNorm D⁻¹ * matOpNorm Tnext⁻¹ := by
  have hTi : T * T⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hT)
  have hB : B = Tnext * D * T⁻¹ := by
    rw [hconj, Matrix.mul_assoc, hTi, Matrix.mul_one]
  rw [hB, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).1 hT)]
  rw [← Matrix.mul_assoc]
  change ‖T * D⁻¹ * Tnext⁻¹‖ ≤ ‖T‖ * ‖D⁻¹‖ * ‖Tnext⁻¹‖
  exact (norm_mul_le (T * D⁻¹) Tnext⁻¹).trans
    (mul_le_mul_of_nonneg_right (norm_mul_le T D⁻¹) (norm_nonneg Tnext⁻¹))

end Yau.Proofs.Y01Aux
