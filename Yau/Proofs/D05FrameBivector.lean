import Yau.Proofs.D05AmbientBivector

/-! The bivector of every original closed-disc frame is holomorphic in
the actual induced charts, and its ambient pushforward is the same Π_G. -/

open scoped Manifold Topology ContDiff Matrix
open Filter
noncomputable section
namespace Yau.Blueprint.D05Proof
open Yau V03Proof

theorem inverse_preserves_canonicalBivector {n : ℕ} (T : CotangentMatrix n)
    (hTd : T.det ≠ 0)
    (hT : T * (canonicalBivector : CotangentMatrix n) * Matrix.transpose T = (canonicalBivector : CotangentMatrix n)) :
    T⁻¹ * (canonicalBivector : CotangentMatrix n) * Matrix.transpose T⁻¹ = (canonicalBivector : CotangentMatrix n) := by
  have hinv : T⁻¹ * T = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hTd)
  have hinvT : Matrix.transpose T * Matrix.transpose T⁻¹ = 1 := by
    rw [← Matrix.transpose_mul, hinv, Matrix.transpose_one]
  calc
    _ = T⁻¹ * (T * (canonicalBivector : CotangentMatrix n) * Matrix.transpose T) * Matrix.transpose T⁻¹ := by rw [hT]
    _ = (T⁻¹ * T) * (canonicalBivector : CotangentMatrix n) *
        (Matrix.transpose T * Matrix.transpose T⁻¹) := by simp only [Matrix.mul_assoc]
    _ = canonicalBivector := by rw [hinv, hinvT, Matrix.one_mul, Matrix.mul_one]

theorem frameBivector_in_fixed_chart {n : ℕ} {M : ComplexManifold n}
    (x : M.Carrier) (f : ℂ → CotangentPoint M) (E : ℂ → CotangentMatrix n) (z : ℂ)
    (hx : f z ∈ cotangentSource x) :
    frameBivector (frameInChart x f E z) = frameBivector (E z) := by
  let T := cotangentTransition (f z).1 x (f z)
  have hTi := cotangentTransition_mulVec_injective (f z).1 x (f z)
    (mem_extChartAt_source _) hx
  have hTd : T.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hTi)).ne_zero
  have hTJ : T⁻¹ * (canonicalBivector : CotangentMatrix n) * Matrix.transpose T⁻¹ =
      (canonicalBivector : CotangentMatrix n) :=
    inverse_preserves_canonicalBivector T hTd
      (cotangentTransition_symplectic (f z).1 x (f z) (mem_extChartAt_source _) hx)
  change frameBivector (T * E z) = frameBivector (E z)
  unfold frameBivector
  rw [Matrix.mul_inv_rev, Matrix.transpose_mul]
  calc
    _ = (E z)⁻¹ * (T⁻¹ * (canonicalBivector : CotangentMatrix n) * Matrix.transpose T⁻¹) *
        Matrix.transpose (E z)⁻¹ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hTJ]

theorem frameBivector_entry_contDiffOn {n : ℕ} {M : ComplexManifold n}
    {f : ℂ → CotangentPoint M} {E : ℂ → CotangentMatrix n}
    (hE : IsDiscFrame f E) (i j : CotangentIndex n) :
    ContDiffOn ℂ ∞ (fun z => frameBivector (E z) i j) (Metric.closedBall (0 : ℂ) 1) := by
  intro z₀ hz₀
  obtain ⟨V, hV, hz₀V, hsource, hframe⟩ := hE.2.2 z₀ hz₀
  let x := (f z₀).1
  let S : ℂ → CotangentMatrix n := frameInChart x f E
  have hSd : ∀ z ∈ Metric.closedBall (0 : ℂ) 1 ∩ V, (S z).det ≠ 0 :=
    fun z hz => frameInChart_det_ne_zero hE hz.1 x (hsource z hz)
  have hS : ∀ k l, ContDiffOn ℂ ∞ (fun z => S z k l)
      (Metric.closedBall (0 : ℂ) 1 ∩ V) := hframe
  have hInv : ∀ k l, ContDiffOn ℂ ∞ (fun z => (S z)⁻¹ k l)
      (Metric.closedBall (0 : ℂ) 1 ∩ V) :=
    Yau.Proofs.B01Aux.holomorphic_matrix_inv hS hSd
  have hB : ContDiffOn ℂ ∞ (fun z => frameBivector (S z) i j)
      (Metric.closedBall (0 : ℂ) 1 ∩ V) := by
    change ContDiffOn ℂ ∞ (fun z =>
      ((S z)⁻¹ * (canonicalBivector : CotangentMatrix n) * Matrix.transpose (S z)⁻¹) i j)
        (Metric.closedBall (0 : ℂ) 1 ∩ V)
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact ContDiffOn.sum fun k _ =>
      (ContDiffOn.sum fun l _ => (hInv i l).mul contDiffOn_const).mul (hInv j k)
  apply (contDiffWithinAt_inter (hV.mem_nhds hz₀V)).mp
  apply (hB z₀ ⟨hz₀, hz₀V⟩).congr_of_eventuallyEq_of_mem ?_ ⟨hz₀, hz₀V⟩
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact congrFun (congrFun (frameBivector_in_fixed_chart x f E z (hsource z hz)).symm i) j

theorem ambientBivector_eq_frame_pushforward {n q : ℕ} {M : ComplexManifold n}
    (G : CotangentPoint M → ComplexVector q) (f : ℂ → CotangentPoint M)
    {E : ℂ → CotangentMatrix n} (hE : IsDiscFrame f E)
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    ambientBivector G (f z) =
      ambientFrame G f E z * frameBivector (E z) * Matrix.transpose (ambientFrame G f E z) := by
  have hinv : E z * (E z)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hE.1 z hz))
  have hinvT : Matrix.transpose (E z)⁻¹ * Matrix.transpose (E z) = 1 := by
    rw [← Matrix.transpose_mul, hinv, Matrix.transpose_one]
  unfold ambientBivector ambientFrame frameBivector
  rw [Matrix.transpose_mul]
  symm
  calc
    _ = cotangentDG G (f z).1 (f z) * (E z * (E z)⁻¹) * (canonicalBivector : CotangentMatrix n) *
        (Matrix.transpose (E z)⁻¹ * Matrix.transpose (E z)) *
          Matrix.transpose (cotangentDG G (f z).1 (f z)) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hinv, hinvT, Matrix.mul_one, Matrix.mul_one]

end Yau.Blueprint.D05Proof
