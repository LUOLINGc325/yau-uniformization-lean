import Yau.Proofs.D06HardyBoundaryLimits

/-! The sharp interior matrix bounds and inverse identities pass to the actual
L² boundary traces along a common radial subsequence. -/

open scoped Topology Matrix
open Filter MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

open Yau.Blueprint
variable {r : ℕ}

theorem hardy_radial_point_mem (n : ℕ) (t : HardyCircle) :
    ‖(hardyRadius n : ℂ) * fourier 1 t‖ < 1 := by
  simpa only [norm_mul, fourier_apply, Circle.norm_coe, mul_one] using hardyRadius_norm n

theorem hardyMatrixTrace_bound (a : Fin r → HardySeq r) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ z : ℂ, ‖z‖ < 1 → matOpNormR (hardyMatrixInterior a z) ≤ C) :
    ∀ᵐ t ∂hardyCircleMeasure, matOpNormR (hardyMatrixTrace a t) ≤ C := by
  obtain ⟨ns, _, hlim⟩ := hardyMatrix_radial_subsequence (fun _ : Unit => a)
  filter_upwards [hlim] with t ht
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro v
  have hv := (Matrix.continuous_uncurry_toEuclideanCLM (n := Fin r) (𝕜 := ℂ)).continuousAt.tendsto.comp
    ((ht ()).prodMk_nhds (tendsto_const_nhds (x := v)))
  apply le_of_tendsto hv.norm
  apply Eventually.of_forall
  intro n
  exact ((Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℂ)
    (hardyMatrixInterior a ((hardyRadius (ns n) : ℂ) * fourier 1 t))).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hbound _ (hardy_radial_point_mem _ _)) (norm_nonneg v))

theorem hardyMatrixTrace_inverse (a b : Fin r → HardySeq r)
    (hinv : ∀ z : ℂ, ‖z‖ < 1 → hardyMatrixInterior a z * hardyMatrixInterior b z = 1 ∧
      hardyMatrixInterior b z * hardyMatrixInterior a z = 1) :
    ∀ᵐ t ∂hardyCircleMeasure, hardyMatrixTrace a t * hardyMatrixTrace b t = 1 ∧
      hardyMatrixTrace b t * hardyMatrixTrace a t = 1 := by
  obtain ⟨ns, _, hlim⟩ := hardyMatrix_radial_subsequence (fun k : Bool => if k then b else a)
  filter_upwards [hlim] with t ht
  have ha := ht false
  have hb := ht true
  simp only [Bool.false_eq_true, ↓reduceIte] at ha
  simp only [↓reduceIte] at hb
  constructor
  · have hp := ha.mul hb
    have heq : (fun n => hardyMatrixInterior a ((hardyRadius (ns n) : ℂ) * fourier 1 t) *
        hardyMatrixInterior b ((hardyRadius (ns n) : ℂ) * fourier 1 t)) = fun _ : ℕ => 1 := by
      funext n
      exact (hinv _ (hardy_radial_point_mem _ _)).1
    rw [heq] at hp
    exact tendsto_nhds_unique hp tendsto_const_nhds
  · have hp := hb.mul ha
    have heq : (fun n => hardyMatrixInterior b ((hardyRadius (ns n) : ℂ) * fourier 1 t) *
        hardyMatrixInterior a ((hardyRadius (ns n) : ℂ) * fourier 1 t)) = fun _ : ℕ => 1 := by
      funext n
      exact (hinv _ (hardy_radial_point_mem _ _)).2
    rw [heq] at hp
    exact tendsto_nhds_unique hp tendsto_const_nhds

theorem norm_matrix_entry_le_matOpNormR (A : Matrix (Fin r) (Fin r) ℂ) (i j : Fin r) :
    ‖A i j‖ ≤ matOpNormR A := by
  change ‖A i j‖ ≤ ‖Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℂ) A‖
  let v := EuclideanSpace.single j (1 : ℂ)
  have h := (PiLp.norm_apply_le (Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℂ) A v) i).trans
    ((Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℂ) A).le_opNorm v)
  have hv : ‖v‖ = 1 := by simp only [v, PiLp.norm_single, norm_one]
  have ha : (Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℂ) A v) i = A i j := by
    change (A *ᵥ Pi.single j 1) i = A i j
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  simpa only [ha, hv, mul_one] using h

theorem hardyMatrixTrace_memLp_top (a : Fin r → HardySeq r) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ z : ℂ, ‖z‖ < 1 → matOpNormR (hardyMatrixInterior a z) ≤ C) (i j : Fin r) :
    MemLp (fun t => hardyMatrixTrace a t i j) ⊤ hardyCircleMeasure := by
  apply memLp_top_of_bound (Lp.aestronglyMeasurable (hardyTraceLp (a j) i)) C
  filter_upwards [hardyMatrixTrace_bound a C hC hbound] with t ht
  exact (norm_matrix_entry_le_matOpNormR _ i j).trans ht

end Yau.NodeProofs.D06Aux
