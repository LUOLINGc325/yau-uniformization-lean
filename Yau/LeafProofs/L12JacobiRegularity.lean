import Yau.LeafProofs.L12ExponentialVolume

/-! Linear regularity of the genuine initial-velocity Jacobi differential
and its actual parallel-frame matrix. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff Bundle ComplexOrder InnerProductSpace
namespace Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000

/-- The genuine initial-velocity Jacobi differential as a linear map. -/
def realGeodesicJacobiOperator (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ) :
    TangentSpace 𝓘(ℝ, ComplexVector n) p.proj →L[ℝ]
      TangentSpace 𝓘(ℝ, ComplexVector n) (realGeodesicFlow g p t).proj := by
  letI := manifold_realSmooth M
  letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
  letI := underlyingRealTangentInnerProductSpace g.form p.proj
  exact (mfderiv 𝓘(ℝ, TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) 𝓘(ℝ, ComplexVector n)
    (fun a => realVelocityBaseFlow g p.proj a t) p.2).comp
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) p.2).symm.toContinuousLinearMap)

theorem realGeodesicJacobiOperator_apply (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ)
    (w : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) :
    realGeodesicJacobiOperator g p t w = realGeodesicJacobiField g p w t := rfl

theorem realGeodesicJacobiField_initial_expansion (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ)
    (w : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) :
    letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
    letI := underlyingRealTangentInnerProductSpace g.form p.proj
    realGeodesicJacobiField g p w t =
      ∑ j, ⟪realInitialOrthonormalFrame g p.proj j, w⟫_ℝ •
        realGeodesicJacobiField g p (realInitialOrthonormalFrame g p.proj j) t := by
  letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
  letI := underlyingRealTangentInnerProductSpace g.form p.proj
  have h := congrArg (realGeodesicJacobiOperator g p t)
    ((realInitialOrthonormalFrame g p.proj).sum_repr' w)
  simpa only [map_sum, map_smul, realGeodesicJacobiOperator_apply] using h.symm

theorem realGeodesicJacobiField_coefficients (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ)
    (w : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) :
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentInnerProductSpace g.form y
    ∀ i, (realGlobalParallelFrame g p t).repr (realGeodesicJacobiField g p w t) i =
      (realGeodesicJacobiMatrix g p t *ᵥ (fun j => (realInitialOrthonormalFrame g p.proj).repr w j)) i := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  intro i
  simp only [OrthonormalBasis.repr_apply_apply]
  rw [realGeodesicJacobiField_initial_expansion g p t w]
  simp only [inner_sum, inner_smul_right, Matrix.mulVec, dotProduct, realGeodesicJacobiMatrix]
  apply Finset.sum_congr rfl
  intro j _
  change ⟪realInitialOrthonormalFrame g p.proj j, w⟫_ℝ *
      (underlyingRealRiemannianMetric g.form).inner (realGeodesicFlow g p t).proj
        (realGlobalParallelFrame g p t i)
        (realGeodesicJacobiField g p (realInitialOrthonormalFrame g p.proj j) t) = _
  exact mul_comm _ _

/-- Nonsingularity of the genuine parallel-frame Jacobi matrix is exactly
nonsingularity of the actual initial-velocity differential. -/
theorem realGeodesicJacobiOperator_injective_of_det_ne_zero (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ)
    (hdet : (realGeodesicJacobiMatrix g p t).det ≠ 0) :
    Function.Injective (realGeodesicJacobiOperator g p t) := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  intro u v huv
  have hc : realGeodesicJacobiMatrix g p t *ᵥ
      (fun j => (realInitialOrthonormalFrame g p.proj).repr u j) =
      realGeodesicJacobiMatrix g p t *ᵥ
        (fun j => (realInitialOrthonormalFrame g p.proj).repr v j) := by
    funext i
    rw [← realGeodesicJacobiField_coefficients, ← realGeodesicJacobiField_coefficients]
    exact congrArg (fun w => (realGlobalParallelFrame g p t).repr w i) huv
  have he := Matrix.mulVec_injective_of_det_ne_zero hdet hc
  apply (realInitialOrthonormalFrame g p.proj).repr.injective
  exact PiLp.ext (fun i => congrFun he i)

theorem realGeodesicJacobiOperator_surjective_of_det_ne_zero (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ)
    (hdet : (realGeodesicJacobiMatrix g p t).det ≠ 0) :
    Function.Surjective (realGeodesicJacobiOperator g p t) := by
  let e : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj ≃L[ℝ]
      TangentSpace 𝓘(ℝ, ComplexVector n) (realGeodesicFlow g p t).proj :=
    (tangentSpaceCastModel 𝓘(ℝ, ComplexVector n) p.proj).trans
      (tangentSpaceCastModel 𝓘(ℝ, ComplexVector n) (realGeodesicFlow g p t).proj).symm
  let L := e.symm.toLinearMap.comp (realGeodesicJacobiOperator g p t).toLinearMap
  have hL : Function.Injective L :=
    e.symm.injective.comp (realGeodesicJacobiOperator_injective_of_det_ne_zero g p t hdet)
  have hs := LinearMap.surjective_of_injective hL
  intro w
  obtain ⟨u, hu⟩ := hs (e.symm w)
  exact ⟨u, e.symm.injective hu⟩

/-- The actual Jacobi differential is a genuine continuous linear
isomorphism wherever its actual matrix determinant is nonzero. -/
def realGeodesicJacobiEquiv (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ)
    (hdet : (realGeodesicJacobiMatrix g p t).det ≠ 0) :
    TangentSpace 𝓘(ℝ, ComplexVector n) p.proj ≃L[ℝ]
      TangentSpace 𝓘(ℝ, ComplexVector n) (realGeodesicFlow g p t).proj :=
  (LinearEquiv.ofBijective (realGeodesicJacobiOperator g p t).toLinearMap
    ⟨realGeodesicJacobiOperator_injective_of_det_ne_zero g p t hdet,
      realGeodesicJacobiOperator_surjective_of_det_ne_zero g p t hdet⟩).toContinuousLinearEquiv

theorem realGeodesicJacobiEquiv_apply (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ)
    (hdet : (realGeodesicJacobiMatrix g p t).det ≠ 0)
    (w : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) :
    realGeodesicJacobiEquiv g p t hdet w = realGeodesicJacobiField g p w t := rfl

end Yau.LeafProofs.L12Aux
