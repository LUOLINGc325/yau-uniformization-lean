import Yau.Proofs.C04BoundedGeometryChartsNormalChartHolomorphic

/-! The real and complex differentials of the same actual map agree on tangent vectors. -/
noncomputable section
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5

theorem realTangentEquiv_realMapDeriv (f : ComplexVector n → M.Carrier)
    (z v : ComplexVector n)
    (hf : MDifferentiableAt (ComplexModel n) (ComplexModel n) f z) :
    realTangentEquiv (f z) (realMapDeriv f z v) =
      mfderiv (ComplexModel n) (ComplexModel n) f z v := by
  let S := ComplexEuclideanManifold n (Nat.succ_le_iff.mpr (manifold_dimension_pos M))
  have hd := mfderiv_real (M := S) (N := M) hf
  have hv := congrArg (fun A => realTangentEquiv (f z)
    (A ((tangentSpaceCastModel 𝓘(ℝ, ComplexVector n) z).symm v))) hd
  have hsource : realTangentEquiv (M := S) z
      ((tangentSpaceCastModel 𝓘(ℝ, ComplexVector n) z).symm v) = v := rfl
  change realTangentEquiv (f z) (realMapDeriv f z v) =
    realTangentEquiv (f z) ((realTangentEquiv (f z)).symm
      (((mfderiv (ComplexModel n) (ComplexModel n) f z).restrictScalars ℝ)
        (realTangentEquiv (M := S) z
          ((tangentSpaceCastModel 𝓘(ℝ, ComplexVector n) z).symm v)))) at hv
  rw [ContinuousLinearEquiv.apply_symm_apply, hsource] at hv
  exact hv

theorem realMapDeriv_comp (E : ComplexVector n → M.Carrier)
    (a : ComplexVector n → ComplexVector n) (z : ComplexVector n)
    (hE : letI := manifold_realSmooth M
      MDifferentiableAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) E (a z))
    (ha : DifferentiableAt ℝ a z) :
    realMapDeriv (fun x => E (a x)) z = (realMapDeriv E (a z)).comp (fderiv ℝ a z) := by
  letI := manifold_realSmooth M
  let c := E (a z)
  have hc : E (a z) ∈ (chartAt (ComplexVector n) c).source := mem_chart_source _ _
  have hchart : DifferentiableAt ℝ (fun x => chartPt c (E x)) (a z) :=
    ((mdifferentiableAt_extChartAt (I := 𝓘(ℝ, ComplexVector n)) hc).comp (a z) hE).differentiableAt
  apply ContinuousLinearMap.ext
  intro v
  have hi : Function.Injective (realTangentCoords c (E (a z))) :=
    Function.LeftInverse.injective (realFrameCLM_realTangentCoords c (E (a z)) hc)
  apply hi
  change realTangentCoords c (E (a z)) (realMapDeriv (fun x => E (a x)) z v) =
    realTangentCoords c (E (a z)) (realMapDeriv E (a z) (fderiv ℝ a z v))
  calc
    _ = fderiv ℝ (fun x => chartPt c (E (a x))) z v :=
      realTangentCoords_mfderiv (fun x => E (a x)) z c hc v (hE.comp z ha.mdifferentiableAt)
    _ = fderiv ℝ (fun x => chartPt c (E x)) (a z) (fderiv ℝ a z v) := by
      exact congrArg (fun T : ComplexVector n →L[ℝ] ComplexVector n => T v)
        (fderiv_comp z hchart ha)
    _ = _ := (realTangentCoords_mfderiv E (a z) c hc (fderiv ℝ a z v) hE).symm

theorem realMetric_of_complex_derivative (k : HermitianField M)
    (f : ComplexVector n → M.Carrier) (z u v : ComplexVector n)
    (hf : MDifferentiableAt (ComplexModel n) (ComplexModel n) f z) :
    (underlyingRealRiemannianMetric k).inner (f z)
      (realMapDeriv f z u) (realMapDeriv f z v) =
      2 * ((k (f z)).toFun (mfderiv (ComplexModel n) (ComplexModel n) f z u)
        (mfderiv (ComplexModel n) (ComplexModel n) f z v)).re := by
  rw [underlyingRealRiemannianMetric_inner,
    realTangentEquiv_realMapDeriv f z u hf, realTangentEquiv_realMapDeriv f z v hf]

theorem complex_mfderiv_bijective_of_real (f : ComplexVector n → M.Carrier)
    (z : ComplexVector n)
    (hf : MDifferentiableAt (ComplexModel n) (ComplexModel n) f z)
    (hi : (realMapDeriv f z).IsInvertible) :
    Function.Bijective (mfderiv (ComplexModel n) (ComplexModel n) f z) := by
  constructor
  · intro u v huv
    apply hi.injective
    apply (realTangentEquiv (f z)).injective
    simpa only [realTangentEquiv_realMapDeriv f z _ hf] using huv
  · intro w
    obtain ⟨v, hv⟩ := hi.surjective ((realTangentEquiv (f z)).symm w)
    refine ⟨v, ?_⟩
    rw [← realTangentEquiv_realMapDeriv f z v hf, hv, ContinuousLinearEquiv.apply_symm_apply]

end Yau.Proofs.C04ChartsAux
