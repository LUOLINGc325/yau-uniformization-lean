import Yau.LeafProofs.L12ShortBranches

/-! The genuine three-piece endpoint energy and its minimizing central
configuration, measured with the original length distance. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff Bundle ComplexOrder InnerProductSpace
namespace Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

/-- The first piece varies its actual initial velocity. The two following
pieces are actual endpoint branches, with a freely varying middle point. -/
def realBrokenEndpointEnergy (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (s e d : ℝ)
    (P Q : M.Carrier × M.Carrier → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (y z : M.Carrier) (θ : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n) : ℝ :=
  realSegmentEnergy g s ⟨p.proj, θ.1⟩ +
    realSegmentEnergy g e (P (realVelocityBaseFlow g p.proj θ.1 s, chartInv y θ.2)) +
      realSegmentEnergy g d (Q (chartInv y θ.2, z))

/-- True minimizing geodesics give local minima of the genuine finite
broken-geodesic energy. No nonsingularity of the long first piece is needed. -/
theorem realBrokenEndpointEnergy_isLocalMin (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) {s e d : ℝ}
    (hs : 0 < s) (he : 0 < e) (hd : 0 < d)
    (U V : Set (M.Carrier × M.Carrier)) (hU : IsOpen U) (hV : IsOpen V)
    (P Q : M.Carrier × M.Carrier → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (hPU : realGeodesicEndpointMap g e (realGeodesicFlow g p s) ∈ U)
    (hQV : realGeodesicEndpointMap g d (realGeodesicFlow g p (s + e)) ∈ V)
    (hPcenter : P (realGeodesicEndpointMap g e (realGeodesicFlow g p s)) = realGeodesicFlow g p s)
    (hQcenter : Q (realGeodesicEndpointMap g d (realGeodesicFlow g p (s + e))) = realGeodesicFlow g p (s + e))
    (hPends : ∀ a ∈ U, (P a).proj = a.1 ∧ (realGeodesicFlow g (P a) e).proj = a.2)
    (hQends : ∀ a ∈ V, (Q a).proj = a.1 ∧ (realGeodesicFlow g (Q a) d).proj = a.2) :
    letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
    letI := underlyingRealTangentInnerProductSpace g.form p.proj
    inducedDistance g.form p.proj (realGeodesicFlow g p (s + e + d)).proj =
      (s + e + d) * ‖p.2‖ →
    IsLocalMin (realBrokenEndpointEnergy g p s e d P Q
      (realGeodesicFlow g p (s + e)).proj (realGeodesicFlow g p (s + e + d)).proj)
      (p.2, chartPt (realGeodesicFlow g p (s + e)).proj (realGeodesicFlow g p (s + e)).proj) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
  letI := underlyingRealTangentInnerProductSpace g.form p.proj
  intro hmin
  let a := (realGeodesicFlow g p s).proj
  let y := (realGeodesicFlow g p (s + e)).proj
  let z := (realGeodesicFlow g p (s + e + d)).proj
  let θ₀ : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n := (p.2, chartPt y y)
  let χ : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n → M.Carrier :=
    fun θ => chartInv y θ.2
  let A : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n → M.Carrier :=
    fun θ => realVelocityBaseFlow g p.proj θ.1 s
  have hχc : ContinuousAt (chartInv y) (chartPt y y) :=
    (contMDiffAt_chartInv_real y (chartPt y y) (mem_extChartAt_target y)).continuousAt
  have hχ : ContinuousAt χ θ₀ :=
    hχc.comp (f := Prod.snd) (x := θ₀) continuousAt_snd
  have hχ₀ : χ θ₀ = y := (extChartAt (ComplexModel n) y).left_inv (mem_extChartAt_source y)
  have hA : ContinuousAt A θ₀ :=
    (realVelocityBaseFlow_contMDiff g p.proj s).continuous.continuousAt.comp continuousAt_fst
  have hA₀ : A θ₀ = a := rfl
  have hendP : realGeodesicEndpointMap g e (realGeodesicFlow g p s) = (a, y) := by
    apply Prod.ext
    · rfl
    · exact congrArg Bundle.TotalSpace.proj (realGeodesicFlow_add g p s e).symm
  have hendQ : realGeodesicEndpointMap g d (realGeodesicFlow g p (s + e)) = (y, z) := by
    apply Prod.ext
    · rfl
    · exact congrArg Bundle.TotalSpace.proj (realGeodesicFlow_add g p (s + e) d).symm
  have hpU : (a, y) ∈ U := hendP ▸ hPU
  have hqV : (y, z) ∈ V := hendQ ▸ hQV
  have hN₀ : ∀ᶠ θ in 𝓝 θ₀, (A θ, χ θ) ∈ U := by
    have hh := (hA.prodMk hχ).eventually (hU.mem_nhds (by change (A θ₀, χ θ₀) ∈ U; rw [hA₀, hχ₀]; exact hpU))
    exact hh
  have hN₁ : ∀ᶠ θ in 𝓝 θ₀, (χ θ, z) ∈ V := by
    have hzcont : ContinuousAt
        (fun _ : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n => z) θ₀ :=
      continuousAt_const
    have hh := (hχ.prodMk hzcont).eventually
      (hV.mem_nhds (by change (χ θ₀, z) ∈ V; rw [hχ₀]; exact hqV))
    exact hh
  have hP₀ : P (a, y) = realGeodesicFlow g p s := hendP ▸ hPcenter
  have hQ₀ : Q (y, z) = realGeodesicFlow g p (s + e) := hendQ ▸ hQcenter
  have hvalue : realBrokenEndpointEnergy g p s e d P Q y z θ₀ =
      ((s + e + d) / 2) * ‖p.2‖ ^ 2 := by
    change realSegmentEnergy g s p + realSegmentEnergy g e (P (A θ₀, χ θ₀)) +
      realSegmentEnergy g d (Q (χ θ₀, z)) = _
    rw [hA₀, hχ₀, hP₀, hQ₀]
    dsimp only [realSegmentEnergy]
    rw [realGeodesicFlow_energy, realGeodesicFlow_energy, realTangentEnergy_eq_norm_sq]
    ring
  change ∀ᶠ θ in 𝓝 θ₀, _
  filter_upwards [hN₀, hN₁] with θ hθU hθV
  have hp := hPends (A θ, χ θ) hθU
  have hq := hQends (χ θ, z) hθV
  rw [hvalue]
  have hbound := realBrokenGeodesicEnergy_lower_bound g
    (⟨p.proj, θ.1⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (P (A θ, χ θ)) (Q (χ θ, z)) hs he hd (norm_nonneg p.2)
    hp.1.symm (hp.2.trans hq.1.symm) (by rw [hq.2]; exact le_of_eq hmin.symm)
  exact hbound

end Yau.LeafProofs.L12Aux
