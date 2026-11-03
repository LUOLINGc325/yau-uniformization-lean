import Yau.LeafProofs.L17ChartNaturality

/-! An actual holomorphic chart differential is invertible. Its fixed
inverse congruence recovers the native metric matrix and transports
genuine chart-matrix limits to the canonical frame. -/
noncomputable section
open Set Filter
open scoped Topology Manifold Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem native_matrix_recovery_from_chart
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {z : ComplexVector n} (hz : z ∈ e.source) (k : HermitianField M) :
    let J := linearMatrix (coordinateDifferential e (e z) z)
    gMat k (e z) = (J⁻¹)ᴴ * pullbackMatrix k e z * J⁻¹ := by
  let J := linearMatrix (coordinateDifferential e (e z) z)
  have hDet : J.det ≠ 0 := linearMatrix_det_ne_zero _
    (coordinateDifferential_injective e he hei (e z) hz (mem_extChartAt_source (e z)))
  have hInv : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J (isUnit_iff_ne_zero.mpr hDet)
  have hStar : (J⁻¹)ᴴ * Jᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hInv, Matrix.conjTranspose_one]
  change gMat k (e z) = (J⁻¹)ᴴ * pullbackMatrix k e z * J⁻¹
  rw [pullbackMatrix_eq_congruence k e (e z) z (mem_extChartAt_source (e z))]
  change gMat k (e z) = (J⁻¹)ᴴ * (Jᴴ * gMat k (e z) * J) * J⁻¹
  calc
    _ = ((J⁻¹)ᴴ * Jᴴ) * gMat k (e z) * (J * J⁻¹) := by rw [hStar, hInv]; simp
    _ = _ := by noncomm_ring

theorem native_matrix_limit_from_chart
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {z : ComplexVector n} (hz : z ∈ e.source)
    (k : ℕ → HermitianField M) (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : Tendsto (fun m => pullbackMatrix (k m) e z) atTop (𝓝 H)) :
    ∃ B : Matrix (Fin n) (Fin n) ℂ,
      Tendsto (fun m => gMat (k m) (e z)) atTop (𝓝 B) := by
  let J := linearMatrix (coordinateDifferential e (e z) z)
  refine ⟨(J⁻¹)ᴴ * H * J⁻¹, ?_⟩
  have hh : Tendsto (fun m => (J⁻¹)ᴴ * pullbackMatrix (k m) e z * J⁻¹) atTop
      (𝓝 ((J⁻¹)ᴴ * H * J⁻¹)) :=
    (tendsto_const_nhds.mul hH).mul tendsto_const_nhds
  have heq : (fun m => gMat (k m) (e z)) =
      (fun m => (J⁻¹)ᴴ * pullbackMatrix (k m) e z * J⁻¹) := by
    funext m
    exact native_matrix_recovery_from_chart e he hei hz (k m)
  rw [heq]
  exact hh

end Yau.NodeProofs.F01Aux
