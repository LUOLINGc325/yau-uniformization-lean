import Yau.Proofs.C01InverseJets

/-! The actual mixed inverse-metric jet has the Chern curvature
congruence after eliminating the free cotangent first derivative. -/

noncomputable section

open scoped Topology ContDiff Matrix
open Filter

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  {n : ℕ}

theorem matrix_inverse_mixed_schur
    (H : V → Herm n) (s : Set V) (hs : IsOpen s)
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun p => H p i j) s)
    (hdet : ∀ p ∈ s, (H p).det ≠ 0) (z v w : V) (hz : z ∈ s) :
    let K := (H z)⁻¹
    let H₁ : Herm n := fun i j => wirt (fun p => H p i j) z w
    let H₂ : Herm n := fun i j => wirtBar (fun p => H p i j) z v
    let H₁₂ : Herm n := fun i j => wirt (fun p => wirtBar (fun q => H q i j) p v) z w
    let K₁ : Herm n := fun i j => wirt (fun p => (H p)⁻¹ i j) z w
    let K₂ : Herm n := fun i j => wirtBar (fun p => (H p)⁻¹ i j) z v
    let K₁₂ : Herm n := fun i j => wirt (fun p => wirtBar (fun q => (H q)⁻¹ i j) p v) z w
    K₁₂ - K₁ * H z * K₂ = K * (-H₁₂ + H₂ * K * H₁) * K := by
  dsimp only
  let K := (H z)⁻¹
  let H₁ : Herm n := fun i j => wirt (fun p => H p i j) z w
  let H₂ : Herm n := fun i j => wirtBar (fun p => H p i j) z v
  let H₁₂ : Herm n := fun i j => wirt (fun p => wirtBar (fun q => H q i j) p v) z w
  let K₁ : Herm n := fun i j => wirt (fun p => (H p)⁻¹ i j) z w
  let K₂ : Herm n := fun i j => wirtBar (fun p => (H p)⁻¹ i j) z v
  let K₁₂ : Herm n := fun i j => wirt (fun p => wirtBar (fun q => (H q)⁻¹ i j) p v) z w
  have hunit : IsUnit (H z).det := isUnit_iff_ne_zero.mpr (hdet z hz)
  have hKH : K * H z = 1 := Matrix.nonsing_inv_mul (H z) hunit
  have hK₁ : K₁ = -(K * H₁ * K) := matrix_inverse_wirt H s hs hH hdet z w hz
  have hK₂ : K₂ = -(K * H₂ * K) := matrix_inverse_wirtBar H s hs hH hdet z v hz
  have hfirst₁ : K₁ * H z + K * H₁ = 0 := by
    rw [hK₁]
    calc
      -(K * H₁ * K) * H z + K * H₁ = -(K * H₁ * (K * H z)) + K * H₁ := by noncomm_ring
      _ = 0 := by rw [hKH, Matrix.mul_one]; abel
  have hfirst₂ : K₂ * H z + K * H₂ = 0 := by
    rw [hK₂]
    calc
      -(K * H₂ * K) * H z + K * H₂ = -(K * H₂ * (K * H z)) + K * H₂ := by noncomm_ring
      _ = 0 := by rw [hKH, Matrix.mul_one]; abel
  have hH₂ (i j : Fin n) : ContDiffAt ℝ 2 (fun p => H p i j) z :=
    ((hH i j).contDiffAt (hs.mem_nhds hz)).of_le (by simp)
  have hK₂smooth (i j : Fin n) : ContDiffAt ℝ 2 (fun p => (H p)⁻¹ i j) z :=
    ((Yau.LeafProofs.SharedCalculus.contDiffOn_matrix_inv hH hdet i j).contDiffAt
      (hs.mem_nhds hz)).of_le (by simp)
  have hproduct : (fun p => (H p)⁻¹ * H p) =ᶠ[𝓝 z]
      (fun _ : V => (1 : Herm n)) := by
    filter_upwards [hs.mem_nhds hz] with p hp
    exact Matrix.nonsing_inv_mul (H p) (isUnit_iff_ne_zero.mpr (hdet p hp))
  have hzero :
      (fun i j => wirt (fun p => wirtBar (fun q => ((H q)⁻¹ * H q) i j) p v) z w) =
      (0 : Herm n) := by
    ext i j
    have hentry : (fun p => ((H p)⁻¹ * H p) i j) =ᶠ[𝓝 z]
        (fun _ : V => (1 : Herm n) i j) :=
      hproduct.mono (fun p hp => congrArg (fun A : Herm n => A i j) hp)
    rw [wirt_wirtBar_congr_germ hentry v w]
    simp [wirt, wirtBar]
  have hprod₀ : K₁₂ * H z + K₂ * H₁ + K₁ * H₂ + K * H₁₂ = 0 := by
    have hformula := matrix_wirt_wirtBar_product (fun p => (H p)⁻¹) H z v w hK₂smooth hH₂
    exact hformula.symm.trans hzero
  have hprod : K₁₂ * H z + K₁ * H₂ + K₂ * H₁ + K * H₁₂ = 0 := by
    calc
      _ = K₁₂ * H z + K₂ * H₁ + K₁ * H₂ + K * H₁₂ := by abel
      _ = 0 := hprod₀
  exact inverse_mixedJet_schur_remainder (H z) H₁ H₂ H₁₂ K₁ K₂ K₁₂
    hunit hfirst₁ hfirst₂ hprod

end Yau.NodeProofs.C01Aux
