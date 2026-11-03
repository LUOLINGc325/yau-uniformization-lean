import Yau.Proofs.C02ParallelComplexField
import Yau.Proofs.C02KahlerConnectionComplex
import Yau.Proofs.C02NormalConnection
import Yau.Proofs.C02ConnectionRadialZero

/-! The actual transported complex structure has the genuine commutator
covariant derivative. Its radial derivative vanishes in the parallel gauge. -/

noncomputable section
open Set Filter
open scoped Manifold InnerProductSpace ContDiff Topology
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem normalParallelComplex_fderiv (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) (x u z : ComplexVector n) :
    fderiv ℝ (normalParallelComplex g p U hU) x u z =
      normalParallelComplex g p U hU x (normalConnection g p U hU x u z) -
        normalConnection g p U hU x u (normalParallelComplex g p U hU x z) := by
  letI := manifold_realSmooth M
  let c := normalRealMap g p U x
  let Q := normalParallelCoefficients g p U hU c
  let C := normalParallelComplex g p U hU
  let A := normalConnection g p U hU
  let Γ := chartChristoffelBilin g.form c (normalCoordinateMap g p U c x)
  let v := fderiv ℝ (normalCoordinateMap g p U c) x u
  have hx : normalRealMap g p U x ∈ (chartAt (ComplexVector n) c).source := mem_chart_source _ _
  have hO := (normalRealMap_smooth g p U hU).continuous.continuousAt.preimage_mem_nhds
    ((chartAt (ComplexVector n) c).open_source.mem_nhds hx)
  have hQ : DifferentiableAt ℝ Q x :=
    ((normalParallelCoefficients_smooth g p U hU c).contDiffAt hO).differentiableAt (by simp)
  have hC : DifferentiableAt ℝ C x := (normalParallelComplex_smooth g p U hU).differentiable (by simp) x
  have hQC (w : ComplexVector n) : Q x (C x w) = Complex.I • Q x w := by
    dsimp only [Q, C]
    rw [normalParallelComplex_eq_chart g p U hU c x hx]
    exact normalParallelComplex_reconstruct g p U hU c x w hx
  have heq : (fun y => Q y (C y z)) =ᶠ[𝓝 x] (fun y => Complex.I • Q y z) := by
    filter_upwards [hO] with y hy
    change normalParallelCoefficients g p U hU c y (normalParallelComplex g p U hU y z) = _
    rw [normalParallelComplex_eq_chart g p U hU c y hy]
    exact normalParallelComplex_reconstruct g p U hU c y z hy
  have hLeft := hQ.hasFDerivAt.clm_apply (hC.hasFDerivAt.clm_apply (hasFDerivAt_const z x))
  have hRight := (complexStructureCLM n).hasFDerivAt.comp x
    (hQ.hasFDerivAt.clm_apply (hasFDerivAt_const z x))
  have hDeriv := congrArg (fun L : ComplexVector n →L[ℝ] ComplexVector n => L u)
    (hLeft.fderiv.symm.trans (heq.fderiv_eq.trans hRight.fderiv))
  have hJApply (w : ComplexVector n) : complexStructureCLM n w = Complex.I • w := rfl
  have hD : Q x (fderiv ℝ C x u z) + fderiv ℝ Q x u (C x z) =
      Complex.I • fderiv ℝ Q x u z := by
    simpa only [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, zero_apply, map_zero, add_zero, zero_add,
      ContinuousLinearMap.comp_zero, hJApply] using hDeriv
  have hRec (w : ComplexVector n) : Q x (A x u w) = fderiv ℝ Q x u w + Γ v (Q x w) := by
    change normalParallelCoefficients g p U hU c x (normalConnection g p U hU x u w) = _
    rw [normalConnection_eq_chart g p U hU c x hx]
    exact normalConnectionInChart_reconstruct g p U hU c x u w hx
  have hy : normalCoordinateMap g p U c x ∈ chartTarget c := mem_extChartAt_target c
  have hΓ := chartChristoffelBilin_I g c (normalCoordinateMap g p U c x) hy v (Q x z)
  apply (normalParallelCoefficients_isInvertible g p U hU c x hx).bijective.injective
  change Q x (fderiv ℝ C x u z) = Q x (C x (A x u z) - A x u (C x z))
  rw [map_sub, hQC, hRec, hRec, hQC, hΓ, smul_add]
  calc
    _ = Complex.I • fderiv ℝ Q x u z - fderiv ℝ Q x u (C x z) := eq_sub_iff_add_eq.mpr hD
    _ = _ := by dsimp only [Γ]; abel

theorem normalParallelComplex_radial_fderiv (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) (x : ComplexVector n) :
    fderiv ℝ (normalParallelComplex g p U hU) x x = 0 := by
  apply ContinuousLinearMap.ext
  intro z
  rw [normalParallelComplex_fderiv, normalConnection_radial_zero]
  simp

end Yau.Blueprint.C02Proof
