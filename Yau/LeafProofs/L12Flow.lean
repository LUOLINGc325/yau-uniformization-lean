import Yau.LeafProofs.L12GlobalGeodesic

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal Matrix ContDiff
namespace Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

/-- The unique genuine geodesic flow, selected from the global existence theorem. -/
def realGeodesicFlow (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :
    ℝ → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  exact (exists_global_realGeodesic g p).choose

theorem realGeodesicFlow_zero (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) : realGeodesicFlow g p 0 = p := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  exact (exists_global_realGeodesic g p).choose_spec.1

theorem realGeodesicFlow_integral (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    IsMIntegralCurve (realGeodesicFlow g p) (realGeodesicSpray g) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  exact (exists_global_realGeodesic g p).choose_spec.2

theorem realGeodesicFlow_contMDiff (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ContMDiff 𝓘(ℝ, ℝ) (realPhaseModel n) ∞ (realGeodesicFlow g p) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  intro t
  exact realGeodesic_contMDiffAt g (realGeodesicFlow g p)
    ((realGeodesicFlow_integral g p).isMIntegralCurveAt t)

theorem realGeodesicFlow_energy (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ) :
    realTangentEnergy g.form (realGeodesicFlow g p t) = realTangentEnergy g.form p := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  let A := |t| + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have h0 : (0 : ℝ) ∈ Set.Ioo (-A) A := ⟨by linarith, hA⟩
  have ht : t ∈ Set.Ioo (-A) A := abs_lt.mp (lt_add_one |t|)
  have h := realGeodesicEnergy_constant g (realGeodesicFlow g p)
    ((realGeodesicFlow_integral g p).isMIntegralCurveOn _) ht h0
  rwa [realGeodesicFlow_zero] at h

theorem realGeodesicFlow_distFrom_le (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ) :
    inducedDistance g.form p.proj (realGeodesicFlow g p t).proj ≤
      Real.sqrt (realTangentEnergy g.form p) * |t| := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  let A := |t| + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have ht : t ∈ Set.Ioo (-A) A := abs_lt.mp (lt_add_one |t|)
  exact realGeodesic_distFrom_le g (realGeodesicFlow g p) p hA
    (realGeodesicFlow_zero g p) ((realGeodesicFlow_integral g p).isMIntegralCurveOn _) ht

theorem realGeodesicFlow_unique (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (γ : ℝ → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    γ 0 = p → IsMIntegralCurve γ (realGeodesicSpray g) → γ = realGeodesicFlow g p := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := realPhase_t2Space M
  letI := realPhaseModel_boundaryless n
  intro hγ0 hγ
  apply isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless
    ((realGeodesicSpray_contMDiff g).of_le (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp))
    hγ (realGeodesicFlow_integral g p)
  exact hγ0.trans (realGeodesicFlow_zero g p).symm

theorem realGeodesicFlow_add (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (s t : ℝ) :
    realGeodesicFlow g p (s + t) = realGeodesicFlow g (realGeodesicFlow g p s) t := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  have h := realGeodesicFlow_unique g (realGeodesicFlow g p s)
    (realGeodesicFlow g p ∘ (· + s)) (by simp)
    ((realGeodesicFlow_integral g p).comp_add s)
  simpa only [Function.comp_apply, add_comm] using congrFun h t

theorem realGeodesicFlow_neg (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ) :
    realGeodesicFlow g (realGeodesicFlow g p t) (-t) = p := by
  rw [← realGeodesicFlow_add, add_neg_cancel, realGeodesicFlow_zero]

theorem realGeodesicSpray_zero (g : SmoothMetric M) (x : M.Carrier) :
    letI := manifold_realSmooth M
    realGeodesicSpray g (⟨x, 0⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) = 0 := by
  letI := manifold_realSmooth M
  simp [realGeodesicSpray, realPhaseChart, chartGeodesicSpray,
    chartGeodesicAcceleration, realCoord]
  rfl

theorem realGeodesicFlow_zeroVelocity (g : SmoothMetric M) (x : M.Carrier) (t : ℝ) :
    realGeodesicFlow g (⟨x, 0⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) t = ⟨x, 0⟩ := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  have h := realGeodesicFlow_unique g
    (⟨x, 0⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (fun _ => ⟨x, 0⟩) rfl
    (isMIntegralCurve_const (realGeodesicSpray_zero g x))
  exact (congrFun h t).symm

/-- The Riemannian exponential defined by the actual global geodesic with
initial position `x` and initial tangent vector `v`. -/
def realExponentialMap (g : SmoothMetric M) (x : M.Carrier)
    (v : TangentSpace 𝓘(ℝ, ComplexVector n) x) : M.Carrier :=
  (realGeodesicFlow g ⟨x, v⟩ 1).proj

theorem realExponentialMap_zero (g : SmoothMetric M) (x : M.Carrier) :
    realExponentialMap g x 0 = x := by
  exact congrArg Bundle.TotalSpace.proj (realGeodesicFlow_zeroVelocity g x 1)

theorem inducedDistance_realExponentialMap_le (g : SmoothMetric M) (x : M.Carrier)
    (v : TangentSpace 𝓘(ℝ, ComplexVector n) x) :
    letI := underlyingRealTangentNormedAddCommGroup g.form x
    inducedDistance g.form x (realExponentialMap g x v) ≤ ‖v‖ := by
  letI := manifold_realSmooth M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  have h := realGeodesicFlow_distFrom_le g
    (⟨x, v⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) 1
  simpa only [realExponentialMap, abs_one, mul_one, realTangentEnergy_eq_norm_sq,
    Real.sqrt_sq (norm_nonneg _)] using h

end Yau.LeafProofs.L12Aux
