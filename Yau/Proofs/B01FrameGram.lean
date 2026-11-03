import Yau.Proofs.B01Frame

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Set Filter Bundle

noncomputable section

namespace Yau.Proofs.B01Aux
open Yau Yau.Blueprint Yau.Blueprint.BundlePresentation
open LeafProofs.L14Aux

variable {r q : ℕ}

theorem frameLift_val_of_range (E : EmbeddedFibers q)
    (F : ℂ → Matrix (Fin q) (Fin r) ℂ) (z : ℂ)
    (hF : LinearMap.range (frameLinear (F z)) = E z) (j : Fin r) :
    (frameLift E F z j).val = frameLinear (F z) (stdVec j) := by
  classical
  have hm : frameLinear (F z) (stdVec j) ∈ E z := hF ▸ LinearMap.mem_range_self _ _
  simp only [frameLift, dite_eq_left hm]

theorem frameLift_gauge (E : EmbeddedFibers q)
    (B F : ℂ → Matrix (Fin q) (Fin r) ℂ) (z : ℂ)
    (hB : LinearMap.range (frameLinear (B z)) = E z)
    (hF : LinearMap.range (frameLinear (F z)) = E z)
    (C : Matrix (Fin r) (Fin r) ℂ) (hC : B z * C = F z) (j : Fin r) :
    frameLift E F z j = ∑ i, C i j • frameLift E B z i := by
  apply Subtype.ext
  simp only [Submodule.coe_sum, Submodule.coe_smul, frameLift_val_of_range E F z hF,
    frameLift_val_of_range E B z hB]
  rw [← hC, frameLinear_mul]
  change frameLinear (B z) (frameLinear C (stdVec j)) = _
  have hv : frameLinear C (stdVec j) = ∑ i, C i j • stdVec i := by
    ext k
    simp [frameLinear, Matrix.toLpLin_apply, stdVec, Pi.single_apply]
  rw [hv, map_sum]
  simp only [map_smul]

theorem embeddedGram_gauge (E : EmbeddedFibers q) (k : EmbeddedMetric E)
    (B F : ℂ → Matrix (Fin q) (Fin r) ℂ) (z : ℂ)
    (hB : LinearMap.range (frameLinear (B z)) = E z)
    (hF : LinearMap.range (frameLinear (F z)) = E z)
    (C : Matrix (Fin r) (Fin r) ℂ) (hC : B z * C = F z) :
    embeddedGram E k F z = Cᴴ * embeddedGram E k B z * C := by
  ext i j
  change (k z).toFun (frameLift E F z i) (frameLift E F z j) = _
  rw [frameLift_gauge E B F z hB hF C hC i, frameLift_gauge E B F z hB hF C hC j]
  simp only [LeafProofs.hermitian_sum_left, LeafProofs.hermitian_sum_right,
    HermitianInnerProduct.map_smul_left, HermitianInnerProduct.map_smul_right,
    Matrix.mul_apply, Matrix.conjTranspose_apply, embeddedGram, Finset.sum_mul]

theorem smooth_matrix_mul {m n p : ℕ}
    {A : ℂ → Matrix (Fin m) (Fin n) ℂ} {B : ℂ → Matrix (Fin n) (Fin p) ℂ}
    {U : Set ℂ} (hA : ∀ i j, ContDiffOn ℝ ∞ (fun z => A z i j) U)
    (hB : ∀ i j, ContDiffOn ℝ ∞ (fun z => B z i j) U) (i j) :
    ContDiffOn ℝ ∞ (fun z => (A z * B z) i j) U := by
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun l _ => (hA i l).mul (hB l j)

theorem embeddedGram_gauge_smooth (E : EmbeddedFibers q) (k : EmbeddedMetric E)
    (B F : ℂ → Matrix (Fin q) (Fin r) ℂ) {O : Set ℂ}
    (hB : ∀ w ∈ O, LinearMap.range (frameLinear (B w)) = E w)
    (hF : ∀ w ∈ O, LinearMap.range (frameLinear (F w)) = E w)
    (C : ℂ → Matrix (Fin r) (Fin r) ℂ)
    (hC : ∀ i j, ContDiffOn ℂ ∞ (fun w => C w i j) O)
    (hCF : ∀ w ∈ O, B w * C w = F w)
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun w => embeddedGram E k B w i j) O) (i j) :
    ContDiffOn ℝ ∞ (fun w => embeddedGram E k F w i j) O := by
  have hR (i j) := (hC i j).restrict_scalars ℝ
  have hS (i j) : ContDiffOn ℝ ∞ (fun w => (C w)ᴴ i j) O :=
    Complex.conjCLE.contDiff.comp_contDiffOn (hR j i)
  have hSH (i j) := smooth_matrix_mul hS hH i j
  have hSHC := smooth_matrix_mul hSH hR i j
  apply hSHC.congr
  intro w hw
  exact congrArg (fun K : Matrix (Fin r) (Fin r) ℂ => K i j)
    (embeddedGram_gauge E k B F w (hB w hw) (hF w hw) (C w) (hCF w hw))

end Yau.Proofs.B01Aux
