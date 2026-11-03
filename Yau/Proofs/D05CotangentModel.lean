import Yau.Proofs.D05CanonicalAlgebra
import Yau.Proofs.V03CotangentSmooth

/-! The derivative of the explicit induced cotangent-coordinate model.
All maps and second derivatives are complex, with no Hermitian duality. -/

open scoped Manifold Topology ContDiff Matrix

noncomputable section
namespace Yau.Blueprint.D05Proof
open Yau

variable {n : ℕ}

def modelCotangentChange (φ ψ : ComplexVector n → ComplexVector n)
    (w : CotangentCoord n) : CotangentCoord n :=
  (φ w.1, WithLp.toLp 2 (fun i =>
    ∑ k, (fderiv ℂ ψ (φ w.1) (stdVec i)) k * w.2 k))

def complexLinearMatrix {m : ℕ} (L : ComplexVector n →L[ℂ] ComplexVector m) :
    Matrix (Fin m) (Fin n) ℂ := fun i j => L (stdVec j) i

def cotangentModelHessian (ψ : ComplexVector n → ComplexVector n)
    (u ξ : ComplexVector n) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => ∑ k, (fderiv ℂ (fderiv ℂ ψ) u (stdVec j) (stdVec i)) k * ξ k

theorem modelCotangentChange_contDiffAt {φ ψ : ComplexVector n → ComplexVector n}
    {z : CotangentCoord n} (hφ : ContDiffAt ℂ ∞ φ z.1)
    (hψ : ContDiffAt ℂ ∞ ψ (φ z.1)) :
    ContDiffAt ℂ ∞ (modelCotangentChange φ ψ) z := by
  have hΦ := hφ.comp z contDiffAt_fst
  have hD : ContDiffAt ℂ ∞ (fun w : CotangentCoord n => fderiv ℂ ψ (φ w.1)) z :=
    (hψ.fderiv_right (m := ∞) (by simp)).comp z hΦ
  refine hΦ.prodMk ?_
  apply (contDiffAt_piLp 2).mpr
  intro i
  change ContDiffAt ℂ ∞ (fun w : CotangentCoord n =>
    ∑ k, (fderiv ℂ ψ (φ w.1) (stdVec i)) k * w.2 k) z
  apply ContDiffAt.sum
  intro k _
  exact ((contDiffAt_piLp_apply (p := 2) (i := k)).comp z
    (hD.clm_apply contDiffAt_const)).mul
    ((contDiffAt_piLp_apply (p := 2) (i := k)).comp z contDiffAt_snd)

theorem complex_fderiv_coordinate {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    {f : P → ComplexVector n} {z : P} (hf : DifferentiableAt ℂ f z) (v : P) (i : Fin n) :
    fderiv ℂ (fun w => f w i) z v = (fderiv ℂ f z v) i := by
  have h := ((PiLp.hasFDerivAt_apply 2 (f z) i).comp z hf.hasFDerivAt).fderiv
  exact congrArg (fun L : P →L[ℂ] ℂ => L v) h

theorem modelCotangentChange_fderiv_fst {φ ψ : ComplexVector n → ComplexVector n}
    {z : CotangentCoord n} (hφ : ContDiffAt ℂ ∞ φ z.1)
    (hψ : ContDiffAt ℂ ∞ ψ (φ z.1)) (v : CotangentCoord n) :
    (fderiv ℂ (modelCotangentChange φ ψ) z v).1 = fderiv ℂ φ z.1 v.1 := by
  have hK := (modelCotangentChange_contDiffAt hφ hψ).differentiableAt (by simp)
  have hcomp := ((hφ.differentiableAt (by simp)).hasFDerivAt.comp z
    (hasFDerivAt_fst (𝕜 := ℂ))).fderiv
  have hfst := hK.hasFDerivAt.fst.fderiv
  exact congrArg (fun L : CotangentCoord n →L[ℂ] ComplexVector n => L v)
    (hfst.symm.trans hcomp)

theorem modelCotangentChange_fderiv_snd {φ ψ : ComplexVector n → ComplexVector n}
    {z : CotangentCoord n} (hφ : ContDiffAt ℂ ∞ φ z.1)
    (hψ : ContDiffAt ℂ ∞ ψ (φ z.1)) (v : CotangentCoord n) (i : Fin n) :
    (fderiv ℂ (modelCotangentChange φ ψ) z v).2 i =
      ∑ k, ((fderiv ℂ (fderiv ℂ ψ) (φ z.1) (fderiv ℂ φ z.1 v.1) (stdVec i)) k * z.2 k +
        (fderiv ℂ ψ (φ z.1) (stdVec i)) k * v.2 k) := by
  let D : CotangentCoord n → ComplexVector n →L[ℂ] ComplexVector n :=
    fun w => fderiv ℂ ψ (φ w.1)
  have hΦ := hφ.comp z contDiffAt_fst
  have hD : ContDiffAt ℂ ∞ D z :=
    (hψ.fderiv_right (m := ∞) (by simp)).comp z hΦ
  have hDf := ((hψ.fderiv_right (m := 1) (by simp)).differentiableAt one_ne_zero).hasFDerivAt.comp z
    ((hφ.differentiableAt (by simp)).hasFDerivAt.comp z (hasFDerivAt_fst (𝕜 := ℂ)))
  have hDval : fderiv ℂ D z v =
      fderiv ℂ (fderiv ℂ ψ) (φ z.1) (fderiv ℂ φ z.1 v.1) :=
    congrArg (fun L : CotangentCoord n →L[ℂ] (ComplexVector n →L[ℂ] ComplexVector n) => L v)
      hDf.fderiv
  have hcoef (k : Fin n) : DifferentiableAt ℂ (fun w : CotangentCoord n => D w (stdVec i) k) z :=
    ((contDiffAt_piLp_apply (p := 2) (i := k)).comp z
      (hD.clm_apply contDiffAt_const)).differentiableAt (by simp)
  have hξ (k : Fin n) : DifferentiableAt ℂ (fun w : CotangentCoord n => w.2 k) z :=
    (show ContDiffAt ℂ ∞ (fun w : CotangentCoord n => w.2 k) z from
      (contDiffAt_piLp_apply (p := 2) (i := k)).comp z contDiffAt_snd).differentiableAt (by simp)
  have hcoefDer (k : Fin n) :
      fderiv ℂ (fun w : CotangentCoord n => D w (stdVec i) k) z v =
        (fderiv ℂ (fderiv ℂ ψ) (φ z.1) (fderiv ℂ φ z.1 v.1) (stdVec i)) k := by
    rw [complex_fderiv_coordinate ((hD.clm_apply contDiffAt_const).differentiableAt (by simp)),
      fderiv_clm_apply (hD.differentiableAt (by simp)) (differentiableAt_const (stdVec i))]
    simp only [fderiv_fun_const, Pi.zero_apply, zero_apply, map_zero, zero_add, add_apply,
      ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, hDval]
  have hξDer (k : Fin n) : fderiv ℂ (fun w : CotangentCoord n => w.2 k) z v = v.2 k := by
    exact congrArg (fun L : CotangentCoord n →L[ℂ] ℂ => L v)
      (((PiLp.hasFDerivAt_apply 2 z.2 k).comp z (hasFDerivAt_snd (𝕜 := ℂ))).fderiv)
  have hK := (modelCotangentChange_contDiffAt hφ hψ).differentiableAt (by simp)
  have hsnd := ((PiLp.hasFDerivAt_apply 2 (modelCotangentChange φ ψ z).2 i).comp z
    hK.hasFDerivAt.snd).fderiv
  have heq := congrArg (fun L : CotangentCoord n →L[ℂ] ℂ => L v) hsnd
  change fderiv ℂ (fun w : CotangentCoord n =>
    ∑ k, D w (stdVec i) k * w.2 k) z v =
      (fderiv ℂ (modelCotangentChange φ ψ) z v).2 i at heq
  rw [← heq, fderiv_fun_sum (fun k _ => (hcoef k).fun_mul (hξ k))]
  simp only [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [fderiv_fun_mul (hcoef k) (hξ k)]
  simp only [add_apply, smul_apply, smul_eq_mul, hcoefDer k, hξDer k]
  ring

end Yau.Blueprint.D05Proof
