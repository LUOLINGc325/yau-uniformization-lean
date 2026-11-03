import Yau.LeafProofs.L17ScalarEllipticity

/-! The computed scalar metric operator in the actual bounded-geometry charts. -/

noncomputable section

open Set Metric Filter
open scoped Topology ContDiff Manifold Matrix

namespace Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem traceWith_congruence
    (G L J : Matrix (Fin n) (Fin n) ℂ) (hJ : J.det ≠ 0) :
    traceWith (Jᴴ * G * J) (Jᴴ * L * J) = traceWith G L := by
  have hJUnit : IsUnit J.det := isUnit_iff_ne_zero.mpr hJ
  have hJH : IsUnit Jᴴ.det := by simpa only [Matrix.det_conjTranspose, isUnit_star] using hJUnit
  have hprod : (Jᴴ * G * J)⁻¹ * (Jᴴ * L * J) = J⁻¹ * (G⁻¹ * L) * J := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
    calc
      J⁻¹ * (G⁻¹ * Jᴴ⁻¹) * (Jᴴ * L * J) = J⁻¹ * G⁻¹ * (Jᴴ⁻¹ * Jᴴ) * L * J := by
        noncomm_ring
      _ = _ := by rw [Matrix.nonsing_inv_mul _ hJH]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [traceWith, traceWith, hprod, Matrix.trace_mul_cycle, Matrix.mul_nonsing_inv _ hJUnit,
    Matrix.one_mul]

theorem leviC_backgroundChart_pullback
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (f : M.Carrier → ℝ) {z : ComplexVector n} (hz : z ∈ e.source)
    (hf : ContDiffAt ℝ 2 (inChart (e z) f) (chartPt (e z) (e z))) :
    leviC (fun w => f (e w)) z =
      (linearMatrix (coordinateDifferential e (e z) z))ᴴ * levi f (e z) *
        linearMatrix (coordinateDifferential e (e z) z) := by
  let a := e z
  let T : ComplexVector n → ComplexVector n := fun w => chartPt a (e w)
  have hU := (forwardChartDomain_isOpen e a).mem_nhds ⟨hz, mem_extChartAt_source a⟩
  have hT : ContDiffAt ℂ 2 T z :=
    ((forwardChart_contDiffOn e he a).contDiffAt hU).of_le (by simp)
  have heq : (fun w => f (e w)) =ᶠ[𝓝 z] ((inChart a f) ∘ T) := by
    filter_upwards [hU] with w hw
    change f (e w) = f (chartInv a (chartPt a (e w)))
    exact congrArg f ((extChartAt (ComplexModel n) a).left_inv hw.2).symm
  rw [L22Aux.leviC_congr_of_eventuallyEq heq, leviC_comp hT hf,
    ← coordinateDifferential_eq_fderiv e he a hz (mem_extChartAt_source a)]
  rfl

theorem backgroundChart_comp_contDiffAt
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (f : M.Carrier → ℝ) {z : ComplexVector n} (hz : z ∈ e.source)
    (hf : ContDiffAt ℝ 2 (inChart (e z) f) (chartPt (e z) (e z))) :
    ContDiffAt ℝ 2 (fun w => f (e w)) z := by
  let a := e z
  let T : ComplexVector n → ComplexVector n := fun w => chartPt a (e w)
  have hU := (forwardChartDomain_isOpen e a).mem_nhds ⟨hz, mem_extChartAt_source a⟩
  have hT : ContDiffAt ℝ 2 T z :=
    ((forwardChart_real_contDiffOn e he a).contDiffAt hU).of_le (by simp)
  apply (hf.comp z hT).congr_of_eventuallyEq
  filter_upwards [hU] with w hw
  change f (e w) = f (chartInv a (chartPt a (e w)))
  exact congrArg f ((extChartAt (ComplexModel n) a).left_inv hw.2).symm

theorem traceWith_backgroundChart_eq_laplacian
    (g : HermitianField M)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    (f : M.Carrier → ℝ) {z : ComplexVector n} (hz : z ∈ e.source)
    (hf : ContDiffAt ℝ 2 (inChart (e z) f) (chartPt (e z) (e z))) :
    traceWith (pullbackMatrix g e z) (leviC (fun w => f (e w)) z) = laplacian g f (e z) := by
  rw [pullbackMatrix_eq_congruence g e (e z) z (mem_extChartAt_source (e z)),
    leviC_backgroundChart_pullback e he f hz hf,
    traceWith_congruence _ _ _ (linearMatrix_det_ne_zero _
      (coordinateDifferential_injective e he hei (e z) hz (mem_extChartAt_source (e z))))]
  rfl

theorem laplacian_eq_backgroundChart_scalarSymbol
    (g : HermitianField M)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    (f : M.Carrier → ℝ) {z : ComplexVector n} (hz : z ∈ e.source)
    (hf : ContDiffAt ℝ 2 (inChart (e z) f) (chartPt (e z) (e z))) :
    laplacian g f (e z) = realHessianContraction (scalarSymbol (pullbackMatrix g e z))
      (fun w => f (e w)) z := by
  rw [← traceWith_backgroundChart_eq_laplacian g e he hei f hz hf,
    traceWith_levi_eq_scalarSymbol _ (backgroundChart_comp_contDiffAt e he f hz hf)]

end Yau.LeafProofs.L17Aux
