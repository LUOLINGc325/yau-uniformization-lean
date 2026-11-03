import Yau.LeafProofs.L12

/-! Actual entrywise time differentiation of the finite matrix product
and inverse, with the inverse jet derived from the identity HH⁻¹=1. -/
noncomputable section
open Set Filter
open scoped Matrix ContDiff Topology
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs
variable {n : ℕ}

def matrixCurveJet (H : ℝ → Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℂ := fun i j => deriv (fun s => H s i j) t

theorem matrixCurveJet_mul (A B : ℝ → Matrix (Fin n) (Fin n) ℂ) (t : ℝ)
    (hA : ∀ i j, DifferentiableAt ℝ (fun s => A s i j) t)
    (hB : ∀ i j, DifferentiableAt ℝ (fun s => B s i j) t) :
    matrixCurveJet (fun s => A s * B s) t =
      matrixCurveJet A t * B t + A t * matrixCurveJet B t := by
  ext i j
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
    (hA i k).hasDerivAt.mul (hB k j).hasDerivAt)
  change deriv (fun s => ∑ k, A s i k * B s k j) t = _
  erw [hsum.deriv]
  simp only [matrixCurveJet, Matrix.add_apply, Matrix.mul_apply, Finset.sum_add_distrib]

theorem matrixCurveJet_inverse (H : ℝ → Matrix (Fin n) (Fin n) ℂ)
    {I : Set ℝ} (hI : IsOpen I)
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun s => H s i j) I)
    (hdet : ∀ s ∈ I, (H s).det ≠ 0) {t : ℝ} (ht : t ∈ I) :
    matrixCurveJet (fun s => (H s)⁻¹) t =
      -((H t)⁻¹ * matrixCurveJet H t * (H t)⁻¹) := by
  have hHd (i j : Fin n) := ((hH i j).contDiffAt (hI.mem_nhds ht)).differentiableAt (by simp)
  have hId (i j : Fin n) := ((L12Aux.contDiffOn_matrix_inv hH hdet i j).contDiffAt
    (hI.mem_nhds ht)).differentiableAt (by simp)
  have hzero : matrixCurveJet (fun s => H s * (H s)⁻¹) t = 0 := by
    ext i j
    have heq : (fun s => (H s * (H s)⁻¹) i j) =ᶠ[𝓝 t]
        (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) i j) := by
      filter_upwards [hI.mem_nhds ht] with s hs
      rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hdet s hs))]
    change deriv _ t = 0
    rw [heq.deriv_eq]
    simp
  have hh := matrixCurveJet_mul H (fun s => (H s)⁻¹) t hHd hId
  rw [hzero] at hh
  have hc := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => (H t)⁻¹ * A) hh.symm
  rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hdet t ht)), Matrix.one_mul,
    Matrix.mul_zero] at hc
  calc
    matrixCurveJet (fun s => (H s)⁻¹) t =
        -((H t)⁻¹ * matrixCurveJet H t * (H t)⁻¹) +
          ((H t)⁻¹ * matrixCurveJet H t * (H t)⁻¹ +
            matrixCurveJet (fun s => (H s)⁻¹) t) := by abel
    _ = _ := by rw [hc, add_zero]

end Yau.NodeProofs.F01Aux
