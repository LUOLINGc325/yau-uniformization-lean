import Yau.Proofs.C02ParallelCoefficients

/-! The inverse frame coefficient matrix is constructed from the actual
inverse tangent chart and the inverse parallel isometry. This invertibility
concerns the parallel frame, with no assumption on the exponential differential. -/

noncomputable section
open Set
open scoped Manifold InnerProductSpace ContDiff
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

def normalParallelCoefficientInverse (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    (c : M.Carrier) (x : ComplexVector n) : ComplexVector n →L[ℝ] ComplexVector n := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  exact (normalParallelIsometry g p U hU x).symm.toContinuousLinearMap.comp
    (realFrameCLM c (normalRealMap g p U x))

theorem normalParallelCoefficient_inverse_identities (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) (c : M.Carrier)
    (x : ComplexVector n) (hx : normalRealMap g p U x ∈ (chartAt (ComplexVector n) c).source) :
    (normalParallelCoefficients g p U hU c x).comp
        (normalParallelCoefficientInverse g p U hU c x) = ContinuousLinearMap.id ℝ (ComplexVector n) ∧
      (normalParallelCoefficientInverse g p U hU c x).comp
        (normalParallelCoefficients g p U hU c x) = ContinuousLinearMap.id ℝ (ComplexVector n) := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  let P := normalParallelIsometry g p U hU x
  constructor
  · apply ContinuousLinearMap.ext
    intro z
    change realTangentCoords c (normalRealMap g p U x)
      (P (P.symm (realFrameCLM c (normalRealMap g p U x) z))) = z
    rw [P.apply_symm_apply]
    exact realTangentCoords_realFrameCLM c _ hx z
  · apply ContinuousLinearMap.ext
    intro z
    change P.symm (realFrameCLM c (normalRealMap g p U x)
      (realTangentCoords c (normalRealMap g p U x) (P z))) = z
    rw [realFrameCLM_realTangentCoords c _ hx]
    exact P.symm_apply_apply z

theorem normalParallelCoefficients_isInvertible (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) (c : M.Carrier)
    (x : ComplexVector n) (hx : normalRealMap g p U x ∈ (chartAt (ComplexVector n) c).source) :
    (normalParallelCoefficients g p U hU c x).IsInvertible := by
  obtain ⟨hRight, hLeft⟩ := normalParallelCoefficient_inverse_identities g p U hU c x hx
  exact ContinuousLinearMap.IsInvertible.of_inverse hRight hLeft

theorem normalParallelCoefficients_inverse_eq (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) (c : M.Carrier)
    (x : ComplexVector n) (hx : normalRealMap g p U x ∈ (chartAt (ComplexVector n) c).source) :
    (normalParallelCoefficients g p U hU c x).inverse = normalParallelCoefficientInverse g p U hU c x := by
  obtain ⟨hRight, hLeft⟩ := normalParallelCoefficient_inverse_identities g p U hU c x hx
  exact ContinuousLinearMap.inverse_eq hRight hLeft

theorem normalParallelCoefficientInverse_smooth (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) (c : M.Carrier) :
    ContDiffOn ℝ ∞ (normalParallelCoefficientInverse g p U hU c)
      ((normalRealMap g p U) ⁻¹' (chartAt (ComplexVector n) c).source) := by
  have hQ := normalParallelCoefficients_smooth g p U hU c
  have hInv : ContDiffOn ℝ ∞ (fun x => (normalParallelCoefficients g p U hU c x).inverse)
      ((normalRealMap g p U) ⁻¹' (chartAt (ComplexVector n) c).source) := by
    intro x hx
    exact ((normalParallelCoefficients_isInvertible g p U hU c x hx).contDiffAt_map_inverse
      (𝕜 := ℝ) (n := ∞)).comp_contDiffWithinAt x (hQ x hx)
  exact (contDiffOn_congr (fun x hx => normalParallelCoefficients_inverse_eq g p U hU c x hx)).mp hInv

end Yau.Blueprint.C02Proof
