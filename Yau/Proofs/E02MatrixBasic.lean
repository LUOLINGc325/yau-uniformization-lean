import Yau.Blueprint.Nodes

open Matrix
open scoped Topology ContDiff Matrix ComplexOrder
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

abbrev Rect (n m : ℕ) := Matrix (Fin n) (Fin m) ℂ

def qform {n : ℕ} (B : Herm n) (ξ : ComplexVector n) : ℝ :=
  (star (WithLp.ofLp ξ) ⬝ᵥ (B *ᵥ WithLp.ofLp ξ)).re

def tracePair {n : ℕ} (B K : Herm n) : ℝ := (Matrix.trace (Bᵀ*K)).re

/-- The transpose in the actual cotangent contraction is retained. -/
theorem tracePair_cometric {n : ℕ} (H K : Herm n) :
    tracePair (H⁻¹)ᵀ K = traceWith H K := by
  simp only [tracePair,Matrix.transpose_transpose,traceWith]

def rowProjector {n m : ℕ} (M : Rect n m) : Herm m := Mᴴ*(M*Mᴴ)⁻¹*M

def projectorPenalty {n m : ℕ} (P₀ : Herm m) (M : Rect n m) : ℝ :=
  (n : ℝ)-(Matrix.trace (P₀*rowProjector M)).re

/-- This is the actual real Hessian expression in the standard finite
matrix topology, not a replacement definition by the desired logdet formula.
The later inf-convolution uses an explicit Euclidean packing and its exact
sum-of-squares identity; no plain product norm is identified with that sum. -/
def rectLevi {n m : ℕ} (f : Rect n m → ℝ) (M Z : Rect n m) : ℝ :=
  (fderiv ℝ (fderiv ℝ f) M Z Z+
    fderiv ℝ (fderiv ℝ f) M (Complex.I • Z) (Complex.I • Z))/4

theorem rowProjector_posSemidef {n m : ℕ} (M : Rect n m) (hM : (M*Mᴴ).PosDef) :
    (rowProjector M).PosSemidef :=
  hM.inv.posSemidef.conjTranspose_mul_mul_same M

theorem rowProjector_isHermitian {n m : ℕ} (M : Rect n m) (hM : (M*Mᴴ).PosDef) :
    (rowProjector M).IsHermitian := (rowProjector_posSemidef M hM).isHermitian

theorem rowProjector_idempotent {n m : ℕ} (M : Rect n m) (hM : (M*Mᴴ).PosDef) :
    rowProjector M*rowProjector M = rowProjector M := by
  have hInv : (M*Mᴴ)⁻¹*(M*Mᴴ) = 1 := Matrix.nonsing_inv_mul _ (hM.isUnit.map Matrix.detMonoidHom)
  unfold rowProjector
  calc
    _ = Mᴴ*((M*Mᴴ)⁻¹*(M*Mᴴ))*(M*Mᴴ)⁻¹*M := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hInv]; simp

theorem one_sub_rowProjector_posSemidef {n m : ℕ} (M : Rect n m) (hM : (M*Mᴴ).PosDef) :
    (1-rowProjector M).PosSemidef := by
  let P := rowProjector M
  have hP : P.IsHermitian := rowProjector_isHermitian M hM
  have hPP : P*P = P := rowProjector_idempotent M hM
  have hQ : (1-P)ᴴ*(1-P) = 1-P := by
    rw [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,hP.eq]
    calc
      (1-P)*(1-P) = 1-P-P+P*P := by noncomm_ring
      _ = 1-P := by rw [hPP]; abel
  have hp := Matrix.posSemidef_conjTranspose_mul_self (1-P)
  rwa [hQ] at hp

theorem trace_rowProjector {n m : ℕ} (M : Rect n m) (hM : (M*Mᴴ).PosDef) :
    (Matrix.trace (rowProjector M)).re = n := by
  have hInv : (M*Mᴴ)*(M*Mᴴ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (hM.isUnit.map Matrix.detMonoidHom)
  calc
    _ = (Matrix.trace ((M*Mᴴ)*(M*Mᴴ)⁻¹)).re := by
      rw [rowProjector,Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    _ = n := by rw [hInv,Matrix.trace_one]; simp

end Yau.NodeProofs.E02Aux
