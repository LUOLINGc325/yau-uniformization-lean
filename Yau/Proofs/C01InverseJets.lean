import Yau.Proofs.C01InverseJetAlgebra
import Yau.Proofs.C01WirtingerProducts
import Yau.LeafProofs.SharedCalculus

/-!
Actual Wirtinger derivatives of the inverse metric on the original open
coordinate domain.  Inverse regularity is derived from the determinant;
it is not a supplied curvature or Harnack input.
-/

noncomputable section

open scoped Topology ContDiff Matrix
open Filter

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  {n : ℕ}

theorem matrix_inverse_wirt
    (H : V → Herm n) (s : Set V) (hs : IsOpen s)
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun p => H p i j) s)
    (hdet : ∀ p ∈ s, (H p).det ≠ 0) (z v : V) (hz : z ∈ s) :
    (Matrix.of fun i j => wirt (fun p => (H p)⁻¹ i j) z v) =
      -((H z)⁻¹ * (Matrix.of fun i j => wirt (fun p => H p i j) z v) * (H z)⁻¹) := by
  have hHd (i j : Fin n) : DifferentiableAt ℝ (fun p => H p i j) z :=
    ((hH i j).contDiffAt (hs.mem_nhds hz)).differentiableAt (by simp)
  have hKd (i j : Fin n) : DifferentiableAt ℝ (fun p => (H p)⁻¹ i j) z :=
    ((Yau.LeafProofs.SharedCalculus.contDiffOn_matrix_inv hH hdet i j).contDiffAt
      (hs.mem_nhds hz)).differentiableAt (by simp)
  have hproduct : (fun p => (H p)⁻¹ * H p) =ᶠ[𝓝 z]
      (fun _ : V => (1 : Herm n)) := by
    filter_upwards [hs.mem_nhds hz] with p hp
    exact Matrix.nonsing_inv_mul (H p) (isUnit_iff_ne_zero.mpr (hdet p hp))
  have hzero : (fun i j => wirt (fun p => ((H p)⁻¹ * H p) i j) z v) =
      (0 : Herm n) := by
    ext i j
    have hentry : (fun p => ((H p)⁻¹ * H p) i j) =ᶠ[𝓝 z]
        (fun _ : V => (1 : Herm n) i j) :=
      hproduct.mono (fun p hp => congrArg (fun A : Herm n => A i j) hp)
    rw [wirt_congr_germ hentry v]
    simp [wirt]
  have hfirst :
      (Matrix.of fun i j => wirt (fun p => (H p)⁻¹ i j) z v) * H z +
        (H z)⁻¹ * (Matrix.of fun i j => wirt (fun p => H p i j) z v) = 0 := by
    rw [← matrix_wirt_product (fun p => (H p)⁻¹) H z v hKd hHd]
    exact hzero
  exact inverse_firstJet_of_product (H z)
    (fun i j => wirt (fun p => H p i j) z v)
    (fun i j => wirt (fun p => (H p)⁻¹ i j) z v)
    (isUnit_iff_ne_zero.mpr (hdet z hz)) hfirst

theorem matrix_inverse_wirtBar
    (H : V → Herm n) (s : Set V) (hs : IsOpen s)
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun p => H p i j) s)
    (hdet : ∀ p ∈ s, (H p).det ≠ 0) (z v : V) (hz : z ∈ s) :
    (Matrix.of fun i j => wirtBar (fun p => (H p)⁻¹ i j) z v) =
      -((H z)⁻¹ * (Matrix.of fun i j => wirtBar (fun p => H p i j) z v) * (H z)⁻¹) := by
  have hHd (i j : Fin n) : DifferentiableAt ℝ (fun p => H p i j) z :=
    ((hH i j).contDiffAt (hs.mem_nhds hz)).differentiableAt (by simp)
  have hKd (i j : Fin n) : DifferentiableAt ℝ (fun p => (H p)⁻¹ i j) z :=
    ((Yau.LeafProofs.SharedCalculus.contDiffOn_matrix_inv hH hdet i j).contDiffAt
      (hs.mem_nhds hz)).differentiableAt (by simp)
  have hproduct : (fun p => (H p)⁻¹ * H p) =ᶠ[𝓝 z]
      (fun _ : V => (1 : Herm n)) := by
    filter_upwards [hs.mem_nhds hz] with p hp
    exact Matrix.nonsing_inv_mul (H p) (isUnit_iff_ne_zero.mpr (hdet p hp))
  have hzero : (fun i j => wirtBar (fun p => ((H p)⁻¹ * H p) i j) z v) =
      (0 : Herm n) := by
    ext i j
    have hentry : (fun p => ((H p)⁻¹ * H p) i j) =ᶠ[𝓝 z]
        (fun _ : V => (1 : Herm n) i j) :=
      hproduct.mono (fun p hp => congrArg (fun A : Herm n => A i j) hp)
    rw [wirtBar_congr_germ hentry v]
    simp [wirtBar]
  have hfirst :
      (Matrix.of fun i j => wirtBar (fun p => (H p)⁻¹ i j) z v) * H z +
        (H z)⁻¹ * (Matrix.of fun i j => wirtBar (fun p => H p i j) z v) = 0 := by
    rw [← matrix_wirtBar_product (fun p => (H p)⁻¹) H z v hKd hHd]
    exact hzero
  exact inverse_firstJet_of_product (H z)
    (fun i j => wirtBar (fun p => H p i j) z v)
    (fun i j => wirtBar (fun p => (H p)⁻¹ i j) z v)
    (isUnit_iff_ne_zero.mpr (hdet z hz)) hfirst

end Yau.NodeProofs.C01Aux
