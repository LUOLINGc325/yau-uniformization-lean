import Yau.LeafProofs.L12NormalCoordinates
import Yau.LeafProofs.L12ParallelTransport

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff Bundle
namespace Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

/-- The actual exponential expressed in the base chart at a fixed
endpoint, using the genuine initial tangent frame. -/
def realExponentialEndpointCoordinates (g : SmoothMetric M) (x : M.Carrier)
    (v w : ComplexVector n) : ComplexVector n :=
  chartPt (realNormalExponentialMap g x v) (realNormalExponentialMap g x w)

theorem realExponentialEndpointCoordinates_contDiffAt (g : SmoothMetric M)
    (x : M.Carrier) (v : ComplexVector n) :
    ContDiffAt ℝ 1 (realExponentialEndpointCoordinates g x v) v := by
  letI := manifold_realSmooth M
  have hchart : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 1
      (chartPt (realNormalExponentialMap g x v)) (realNormalExponentialMap g x v) :=
    contMDiffAt_extChartAt (I := 𝓘(ℝ, ComplexVector n))
  exact (hchart.comp v ((realNormalExponentialMap_contMDiff g x).contMDiffAt)).contDiffAt

theorem realExponentialEndpointCoordinates_radial_hasDerivAt (g : SmoothMetric M)
    (x : M.Carrier) (v : ComplexVector n) :
    HasDerivAt (fun t : ℝ => realExponentialEndpointCoordinates g x v (t • v))
      (realTangentCoords (realNormalExponentialMap g x v) (realNormalExponentialMap g x v)
        (realGeodesicFlow g (⟨x, realFrameCLM x x v⟩ :
          TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) 1).2) 1 := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  let p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier := ⟨x, realFrameCLM x x v⟩
  have hbase := realGeodesicFlow_baseCoords_hasDerivAt g p 1
  have heq : (fun t : ℝ => realExponentialEndpointCoordinates g x v (t • v)) =
      (fun t => chartPt (realNormalExponentialMap g x v) (realGeodesicFlow g p t).proj) := by
    funext t
    simp only [realExponentialEndpointCoordinates, realNormalExponentialMap, map_smul,
      realExponentialMap_smul, p]
  rwa [heq]

/-- The actual radial differential of the exponential is precisely the
endpoint geodesic velocity in endpoint coordinates. -/
theorem realExponentialEndpointCoordinates_fderiv_radial (g : SmoothMetric M)
    (x : M.Carrier) (v : ComplexVector n) :
    fderiv ℝ (realExponentialEndpointCoordinates g x v) v v =
      realTangentCoords (realNormalExponentialMap g x v) (realNormalExponentialMap g x v)
        (realGeodesicFlow g (⟨x, realFrameCLM x x v⟩ :
          TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) 1).2 := by
  have hd := (realExponentialEndpointCoordinates_contDiffAt g x v).differentiableAt (by simp)
  have hin : HasDerivAt (fun t : ℝ => t • v) v 1 := by
    simpa only [id_eq, one_smul] using (hasDerivAt_id (1 : ℝ)).smul_const v
  have hDAt : HasFDerivAt (realExponentialEndpointCoordinates g x v)
      (fderiv ℝ (realExponentialEndpointCoordinates g x v) v) ((1 : ℝ) • v) := by
    simpa only [one_smul] using hd.hasFDerivAt
  have hout : HasDerivAt (fun t : ℝ => realExponentialEndpointCoordinates g x v (t • v))
      (fderiv ℝ (realExponentialEndpointCoordinates g x v) v v) 1 := by
    simpa only [Function.comp_def] using hDAt.comp_hasDerivAt 1 hin
  exact hout.unique (realExponentialEndpointCoordinates_radial_hasDerivAt g x v)

theorem realExponential_radialDifferential_eq_velocity (g : SmoothMetric M)
    (x : M.Carrier) (v : ComplexVector n) :
    realFrameCLM (realNormalExponentialMap g x v) (realNormalExponentialMap g x v)
      (fderiv ℝ (realExponentialEndpointCoordinates g x v) v v) =
        (realGeodesicFlow g (⟨x, realFrameCLM x x v⟩ :
          TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) 1).2 := by
  rw [realExponentialEndpointCoordinates_fderiv_radial]
  exact realFrameCLM_realTangentCoords _ _ (mem_chart_source _ _) _

theorem realExponential_radialDifferential_norm (g : SmoothMetric M)
    (x : M.Carrier) (v : ComplexVector n) :
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    ‖realFrameCLM (realNormalExponentialMap g x v) (realNormalExponentialMap g x v)
      (fderiv ℝ (realExponentialEndpointCoordinates g x v) v v)‖ = ‖realFrameCLM x x v‖ := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  rw [realExponential_radialDifferential_eq_velocity]
  let p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier := ⟨x, realFrameCLM x x v⟩
  have hE := realGeodesicFlow_energy g p 1
  rw [realTangentEnergy_eq_norm_sq, realTangentEnergy_eq_norm_sq] at hE
  change ‖(realGeodesicFlow g p 1).2‖ = ‖p.2‖
  nlinarith [norm_nonneg (realGeodesicFlow g p 1).2, norm_nonneg p.2]

/-- A connected noncompact complex manifold has positive complex dimension. -/
theorem complexDimension_pos (M : ComplexManifold n) : 0 < n := by
  by_contra hn
  have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
  subst n
  letI : DiscreteTopology (ComplexVector 0) := inferInstance
  letI : DiscreteTopology M.Carrier := ChartedSpace.discreteTopology (ComplexVector 0) M.Carrier
  letI : Subsingleton M.Carrier := subsingleton_of_preconnected_totallyDisconnected
  exact noncompact_univ M.Carrier (isCompact_univ : IsCompact (Set.univ : Set M.Carrier))

end Yau.LeafProofs.L12Aux
