import Yau.LeafProofs.L19EndpointEnergyCenter
import Yau.LeafProofs.L12MinimizingJacobi

/-! Euclidean trace comparison for the genuine Jacobi shape, including
the terminal time of a nonsingular actual endpoint branch. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff Bundle ComplexOrder InnerProductSpace
namespace Yau.LeafProofs.L19Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

/-- The scalar Riccati inequality and its initial asymptotic are derived
from the actual Jacobi equation and actual nonnegative Ricci tensor. -/
theorem realGeodesicJacobi_shapeTrace_le
    (g : SmoothMetric M) (hK : IsKahler g)
    (hR : ∀ x, (ricci g.form x).PosSemidef)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (T : ℝ)
    (hdet : ∀ t ∈ Set.Ioo 0 T, (realGeodesicJacobiMatrix g p t).det ≠ 0) :
    ∀ t ∈ Set.Ioo 0 T,
      Matrix.trace (realGeodesicJacobiMatrixDeriv g p t * (realGeodesicJacobiMatrix g p t)⁻¹) ≤
        (2 * n : ℕ) / t := by
  let A := realGeodesicJacobiMatrix g p
  let A₁ := realGeodesicJacobiMatrixDeriv g p
  let R := realGeodesicCurvatureMatrix g p
  let A₂ := fun t => -(R t * A t)
  have hA : ∀ t ∈ Set.Ioo 0 T, ∀ i j,
      HasDerivAt (fun s => A s i j) (A₁ t i j) t :=
    fun t _ => realGeodesicJacobiMatrix_hasDerivAt g p t
  have hA₁ : ∀ t ∈ Set.Ioo 0 T, ∀ i j,
      HasDerivAt (fun s => A₁ s i j) (A₂ t i j) t :=
    fun t _ => realGeodesicJacobiMatrixDeriv_hasDerivAt_matrix g p t
  have hA0 : A 0 = 0 := realGeodesicJacobiMatrix_zero g p
  have hAinit := realGeodesicJacobiMatrix_hasDerivAt_initial g p
  have hcA : ContinuousAt A 0 := continuousAt_pi.mpr
    (fun i => continuousAt_pi.mpr (fun j => (hAinit i j).continuousAt))
  have hcA₁ := realGeodesicJacobiMatrixDeriv_continuousAt_zero g p
  have hW := matrixJacobi_Wronskian_zero hA0 hcA hcA₁ hA hA₁
    (fun t _ => realGeodesicCurvatureMatrix_isSymm g p t)
    (fun _ _ => neg_add_cancel _)
  have hk : 0 < ((2 * n : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mul_pos (by omega) (complexDimension_pos M))
  apply riccati_le_euclidean hk
    (fun t ht => matrixJacobi_trace_hasDerivAt (hA t ht) (hA₁ t ht) (hdet t ht))
  · intro t ht
    simpa only [Fintype.card_fin] using
      matrixJacobi_trace_inequality (hA t ht) (hA₁ t ht) (hdet t ht)
        (neg_add_cancel _) (hW t ht) (realGeodesicCurvatureMatrix_trace_nonneg g hK hR p t)
  · simpa only [Fintype.card_fin] using matrixJacobi_shape_initial_asymptotic
      hA0 hAinit hcA₁ (realGeodesicJacobiMatrixDeriv_zero g p)

/-- Nonsingularity at the terminal time lets the actual interior Riccati
bound extend to that terminal time by continuity. -/
theorem realGeodesicJacobi_shapeTrace_le_terminal
    (g : SmoothMetric M) (hK : IsKahler g)
    (hR : ∀ x, (ricci g.form x).PosSemidef)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) {T : ℝ} (hT : 0 < T)
    (hdet : ∀ t ∈ Set.Ioc 0 T, (realGeodesicJacobiMatrix g p t).det ≠ 0) :
    Matrix.trace (realGeodesicJacobiMatrixDeriv g p T * (realGeodesicJacobiMatrix g p T)⁻¹) ≤
      (2 * n : ℕ) / T := by
  have hc := (matrixJacobi_trace_hasDerivAt
    (realGeodesicJacobiMatrix_hasDerivAt g p T)
    (realGeodesicJacobiMatrixDeriv_hasDerivAt_matrix g p T)
    (hdet T ⟨hT, le_rfl⟩)).continuousAt
  have hcomp := realGeodesicJacobi_shapeTrace_le g hK hR p T
    (fun t ht => hdet t ⟨ht.1, ht.2.le⟩)
  apply le_of_tendsto_of_tendsto
    (hc.tendsto.mono_left (show 𝓝[<] T ≤ 𝓝 T from nhdsWithin_le_nhds))
    (((continuousAt_const.div continuousAt_id hT.ne').tendsto).mono_left
      (show 𝓝[<] T ≤ 𝓝 T from nhdsWithin_le_nhds))
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hT)] with t htT ht0
  exact hcomp t ⟨ht0, htT⟩

/-- For an actual minimizing segment only terminal nonsingularity is
needed: interior nonsingularity is already a proved geometric theorem. -/
theorem realMinimizingGeodesic_shapeTrace_le_terminal
    (g : SmoothMetric M) (hK : IsKahler g)
    (hR : ∀ x, (ricci g.form x).PosSemidef)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) {T : ℝ} (hT : 0 < T)
    (hdetT : (realGeodesicJacobiMatrix g p T).det ≠ 0) :
    letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
    letI := underlyingRealTangentInnerProductSpace g.form p.proj
    inducedDistance g.form p.proj (realGeodesicFlow g p T).proj = T * ‖p.2‖ →
    Matrix.trace (realGeodesicJacobiMatrixDeriv g p T * (realGeodesicJacobiMatrix g p T)⁻¹) ≤
      (2 * n : ℕ) / T := by
  letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
  letI := underlyingRealTangentInnerProductSpace g.form p.proj
  intro hmin
  apply realGeodesicJacobi_shapeTrace_le_terminal g hK hR p hT
  intro t ht
  rcases lt_or_eq_of_le ht.2 with hlt | rfl
  · exact realGeodesicJacobiMatrix_det_ne_zero_of_minimizing g p hT hmin t ⟨ht.1, hlt⟩
  · exact hdetT

end Yau.LeafProofs.L19Aux
