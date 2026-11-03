import Yau.Proofs.D05ProjectedBundle
import Yau.Proofs.B01Frame
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-! Actual local holomorphic projections from full-column ambient matrices.
The formula uses a constant left inverse only at the reference point. -/

open Set
open scoped Topology ContDiff Matrix

noncomputable section
namespace Yau.Blueprint.D05Proof
open Yau.Blueprint.BundlePresentation

def matrixCLM {q r : ℕ} (A : Matrix (Fin q) (Fin r) ℂ) :
    EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q) :=
  (Matrix.toEuclideanLin A).toContinuousLinearMap

theorem matrixCLM_apply {q r : ℕ} (A : Matrix (Fin q) (Fin r) ℂ)
    (v : EuclideanSpace ℂ (Fin r)) :
    matrixCLM A v = WithLp.toLp 2 (A *ᵥ WithLp.ofLp v) :=
  Matrix.toLpLin_apply 2 2 A v

theorem matrixCLM_mul {q r b : ℕ} (A : Matrix (Fin q) (Fin r) ℂ)
    (C : Matrix (Fin r) (Fin b) ℂ) :
    matrixCLM (A * C) = (matrixCLM A).comp (matrixCLM C) := by
  apply ContinuousLinearMap.ext
  intro v
  exact LinearMap.congr_fun (Matrix.toLpLin_mul 2 2 2 A C) v

theorem matrixCLM_contDiffOn {q r : ℕ} {A : ℂ → Matrix (Fin q) (Fin r) ℂ}
    {U : Set ℂ} (hA : ∀ i j, ContDiffOn ℂ ∞ (fun z => A z i j) U) :
    ContDiffOn ℂ ∞ (fun z => matrixCLM (A z)) U := by
  apply contDiffOn_clm_apply.mpr
  intro v
  apply (contDiffOn_piLp 2).mpr
  intro i
  change ContDiffOn ℂ ∞ (fun z => ∑ j, A z i j * v j) U
  exact ContDiffOn.sum fun j _ => (hA i j).mul contDiffOn_const

theorem matrix_projection_range {q r : ℕ} (W : Matrix (Fin q) (Fin r) ℂ)
    (L : Matrix (Fin r) (Fin q) ℂ) (v : EuclideanSpace ℂ (Fin q)) :
    matrixCLM (W * (L * W)⁻¹ * L) v ∈ LinearMap.range (frameLinear W) := by
  rw [matrixCLM_mul, matrixCLM_mul]
  exact ⟨matrixCLM ((L * W)⁻¹) (matrixCLM L v), rfl⟩

theorem matrix_projection_fix {q r : ℕ} (W : Matrix (Fin q) (Fin r) ℂ)
    (L : Matrix (Fin r) (Fin q) ℂ) (hdet : (L * W).det ≠ 0)
    {v : EuclideanSpace ℂ (Fin q)} (hv : v ∈ LinearMap.range (frameLinear W)) :
    matrixCLM (W * (L * W)⁻¹ * L) v = v := by
  obtain ⟨u, rfl⟩ := hv
  have hmul : (W * (L * W)⁻¹ * L) * W = W := by
    calc
      _ = W * ((L * W)⁻¹ * (L * W)) := by simp only [Matrix.mul_assoc]
      _ = W := by
        rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), Matrix.mul_one]
  have h := congrArg (fun T => matrixCLM T u) hmul
  rw [matrixCLM_mul] at h
  exact h

theorem locallyProjectedOn_of_local_frames {q r : ℕ}
    {B : ℂ → Submodule ℂ (EuclideanSpace ℂ (Fin q))} {U : Set ℂ}
    (hframes : ∀ p ∈ U, ∃ V : Set ℂ, IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧
      ∃ W : ℂ → Matrix (Fin q) (Fin r) ℂ,
        (∀ i j, ContDiffOn ℂ ∞ (fun z => W z i j) V) ∧
        Function.Injective (frameLinear (W p)) ∧
        ∀ z ∈ V, LinearMap.range (frameLinear (W z)) = B z) :
    LocallyProjectedOn B U := by
  intro p hp
  obtain ⟨V, hV, hpV, hVU, W, hW, hWp, hWr⟩ := hframes p hp
  obtain ⟨L, hL⟩ := Yau.Proofs.B01Aux.frame_leftInverse (W p) hWp
  have hLW : ∀ i j, ContDiffOn ℂ ∞ (fun z => (L * W z) i j) V :=
    Yau.Proofs.B01Aux.holomorphic_matrix_mul (fun _ _ => contDiffOn_const) hW
  have hdet := Yau.Proofs.B01Aux.holomorphic_matrix_det hLW
  let O := V ∩ {z | (L * W z).det ≠ 0}
  have hO : IsOpen O := hdet.continuousOn.isOpen_inter_preimage hV isOpen_ne
  have hpO : p ∈ O := ⟨hpV, by
    change (L * W p).det ≠ 0
    rw [hL, Matrix.det_one]
    exact one_ne_zero⟩
  have hOV : O ⊆ V := Set.inter_subset_left
  have hInv : ∀ i j, ContDiffOn ℂ ∞ (fun z => (L * W z)⁻¹ i j) O :=
    Yau.Proofs.B01Aux.holomorphic_matrix_inv (fun i j => (hLW i j).mono hOV)
      (fun z hz => hz.2)
  have hProd : ∀ i j, ContDiffOn ℂ ∞
      (fun z => (W z * (L * W z)⁻¹ * L) i j) O :=
    Yau.Proofs.B01Aux.holomorphic_matrix_mul
      (Yau.Proofs.B01Aux.holomorphic_matrix_mul (fun i j => (hW i j).mono hOV) hInv)
      (fun _ _ => contDiffOn_const)
  refine ⟨O, hO, hpO, fun z hz => hVU hz.1,
    fun z => matrixCLM (W z * (L * W z)⁻¹ * L), matrixCLM_contDiffOn hProd, ?_, ?_⟩
  · intro z hz v
    rw [← hWr z hz.1]
    exact matrix_projection_range (W z) L v
  · intro z hz v hv
    apply matrix_projection_fix (W z) L hz.2
    rw [hWr z hz.1]
    exact hv

end Yau.Blueprint.D05Proof
