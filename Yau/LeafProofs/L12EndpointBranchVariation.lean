import Yau.LeafProofs.L12ShortBranches
import Yau.LeafProofs.L12PhaseVariation

/-! Differentiating an actual endpoint branch when its terminal endpoint is held fixed. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff Bundle ComplexOrder InnerProductSpace
namespace Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

private theorem held_second_fderiv {E F G H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (A : E → F) (B : E → G) (C : F × G → H) (V : E → H)
    (z w : E) (hA : DifferentiableAt ℝ A z) (hB : DifferentiableAt ℝ B z)
    (hC : DifferentiableAt ℝ C (A z, B z))
    (hV : DifferentiableAt ℝ V z)
    (hBw : fderiv ℝ B z w = 0)
    (hEq : (fun u => C (A u, B u)) =ᶠ[𝓝 z] V) :
    fderiv ℝ (fun u => C (A u, B z)) z w = fderiv ℝ V z w := by
  have hvariable := hC.hasFDerivAt.comp z (hA.hasFDerivAt.prodMk hB.hasFDerivAt)
  have hfixed := hC.hasFDerivAt.comp z (hA.hasFDerivAt.prodMk (hasFDerivAt_const (B z) z))
  have hD := (hEq.hasFDerivAt_iff.mp hvariable).unique hV.hasFDerivAt
  have hDfixed := hfixed.fderiv
  have hDvar := hD
  calc
    fderiv ℝ (fun u => C (A u, B z)) z w =
        fderiv ℝ C (A z, B z) (fderiv ℝ A z w, (0 : G)) := by
          have heval := congrArg (fun L : E →L[ℝ] H => L w) hDfixed
          simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
            ContinuousLinearMap.prod_apply, zero_apply] using heval
    _ = fderiv ℝ C (A z, B z) (fderiv ℝ A z w, fderiv ℝ B z w) := by rw [hBw]
    _ = fderiv ℝ V z w := by
      have heval := congrArg (fun L : E →L[ℝ] H => L w) hDvar
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply] using heval

/-- A C¹ actual endpoint branch, tested by any C¹ observable of the phase,
transports the derivative of an initial-velocity variation when the genuine
terminal Jacobi field vanishes. -/
theorem realEndpointBranch_held_observable_fderiv
    (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (s e : ℝ)
    (U : Set (M.Carrier × M.Carrier)) (hU : IsOpen U)
    (P : M.Carrier × M.Carrier → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (hPU : realGeodesicEndpointMap g e (realGeodesicFlow g p s) ∈ U)
    (hP : letI := manifold_realSmooth M; letI := manifold_realPhase M;
      ContMDiffOn (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n))
      (realPhaseModel n) 1 P U)
    (hleft : letI := manifold_realSmooth M; letI := manifold_realPhase M;
      ∀ᶠ q' in 𝓝 (realGeodesicFlow g p s),
        P (realGeodesicEndpointMap g e q') = q')
    (O : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier → ComplexVector n × ComplexVector n)
    (hO : letI := manifold_realSmooth M; letI := manifold_realPhase M;
      ContMDiffAt (realPhaseModel n) 𝓘(ℝ, ComplexVector n × ComplexVector n) 1 O
        (realGeodesicFlow g p s))
    (w : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj)
    (hJ : realGeodesicJacobiField g p w (s + e) = 0) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
    letI := underlyingRealTangentInnerProductSpace g.form p.proj
    fderiv ℝ (fun u => O (P (realVelocityBaseFlow g p.proj u s,
      (realGeodesicFlow g p (s + e)).proj))) p.2 w =
    fderiv ℝ (fun u => O (realGeodesicFlow g
      (⟨p.proj, u⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) s)) p.2 w := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
  letI := underlyingRealTangentInnerProductSpace g.form p.proj
  let qS := realGeodesicFlow g p s
  let qT := realGeodesicFlow g p (s + e)
  let a := qS.proj
  let b := qT.proj
  let z : ComplexVector n × ComplexVector n := (chartPt a a, chartPt b b)
  let χ : ComplexVector n × ComplexVector n → M.Carrier × M.Carrier :=
    fun ξ => (chartInv a ξ.1, chartInv b ξ.2)
  let A : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj → ComplexVector n :=
    fun u => chartPt a (realVelocityBaseFlow g p.proj u s)
  let B : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj → ComplexVector n :=
    fun u => chartPt b (realVelocityBaseFlow g p.proj u (s + e))
  let C : ComplexVector n × ComplexVector n → ComplexVector n × ComplexVector n :=
    fun ξ => O (P (χ ξ))
  let V : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj → ComplexVector n × ComplexVector n :=
    fun u => O (realGeodesicFlow g
      (⟨p.proj, u⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) s)
  have hPcenter : P (a, b) = qS := by
    have h := hleft.self_of_nhds
    have he : realGeodesicEndpointMap g e qS = (a, b) := by
      apply Prod.ext
      · rfl
      · exact congrArg Bundle.TotalSpace.proj (realGeodesicFlow_add g p s e).symm
    rw [he] at h
    exact h
  have hχ₀ : χ z = (a, b) := Prod.ext
    ((extChartAt (ComplexModel n) a).left_inv (mem_extChartAt_source a))
    ((extChartAt (ComplexModel n) b).left_inv (mem_extChartAt_source b))
  have hχ : ContMDiffAt 𝓘(ℝ, ComplexVector n × ComplexVector n)
      (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n)) 1 χ z :=
    (((contMDiffAt_chartInv_real a (chartPt a a) (mem_extChartAt_target a)).of_le (by simp)).comp z
      contDiffAt_fst.contMDiffAt).prodMk
      (((contMDiffAt_chartInv_real b (chartPt b b) (mem_extChartAt_target b)).of_le (by simp)).comp z
        contDiffAt_snd.contMDiffAt)
  have hPAt : ContMDiffAt (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n))
      (realPhaseModel n) 1 P (a, b) := by
    apply hP.contMDiffAt
    apply hU.mem_nhds
    have he : realGeodesicEndpointMap g e qS = (a, b) := by
      apply Prod.ext
      · rfl
      · exact congrArg Bundle.TotalSpace.proj (realGeodesicFlow_add g p s e).symm
    rw [← he]
    exact hPU
  have hC : ContDiffAt ℝ 1 C z := by
    have hO' : ContMDiffAt (realPhaseModel n) 𝓘(ℝ, ComplexVector n × ComplexVector n)
        1 O (P (a, b)) := by rw [hPcenter]; exact hO
    have hmid := hO'.comp (a, b) hPAt
    have hmid' : ContMDiffAt (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n))
        𝓘(ℝ, ComplexVector n × ComplexVector n) 1 (O ∘ P) (χ z) := by
      rw [hχ₀]
      exact hmid
    exact (hmid'.comp z hχ).contDiffAt
  have hA : ContDiffAt ℝ 1 A p.2 := by
    exact ((contMDiffAt_extChartAt' (mem_chart_source _ _)).comp p.2
      (realVelocityBaseFlow_contMDiff g p.proj s p.2)).contDiffAt
  have hB : ContDiffAt ℝ 1 B p.2 := by
    exact ((contMDiffAt_extChartAt' (mem_chart_source _ _)).comp p.2
      (realVelocityBaseFlow_contMDiff g p.proj (s + e) p.2)).contDiffAt
  have hA₀ : A p.2 = z.1 := rfl
  have hB₀ : B p.2 = z.2 := rfl
  have hBw : fderiv ℝ B p.2 w = 0 := by
    have hcoords := realGeodesicJacobiField_in_chart g p w (s + e) b (mem_chart_source _ _)
    rw [hJ, map_zero] at hcoords
    exact hcoords.symm
  have hV : ContDiffAt ℝ 1 V p.2 :=
    (hO.comp p.2 (realVelocityFlow_contMDiff g p.proj s p.2)).contDiffAt
  have hflow : ∀ᶠ u : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj in 𝓝 p.2,
      P (realGeodesicEndpointMap g e
        (realGeodesicFlow g (⟨p.proj, u⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) s)) =
      realGeodesicFlow g (⟨p.proj, u⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) s :=
    (realVelocityFlow_contMDiff g p.proj s).continuous.continuousAt.tendsto.eventually hleft
  have hsourceA : ∀ᶠ u : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj in 𝓝 p.2,
      realVelocityBaseFlow g p.proj u s ∈ (chartAt (ComplexVector n) a).source :=
    (realVelocityBaseFlow_contMDiff g p.proj s).continuous.continuousAt.eventually
      ((chartAt (ComplexVector n) a).open_source.mem_nhds (mem_chart_source _ _))
  have hsourceB : ∀ᶠ u : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj in 𝓝 p.2,
      realVelocityBaseFlow g p.proj u (s + e) ∈ (chartAt (ComplexVector n) b).source :=
    (realVelocityBaseFlow_contMDiff g p.proj (s + e)).continuous.continuousAt.eventually
      ((chartAt (ComplexVector n) b).open_source.mem_nhds (mem_chart_source _ _))
  have heq : (fun u => C (A u, B u)) =ᶠ[𝓝 p.2] V := by
    filter_upwards [hflow, hsourceA, hsourceB] with u hu hsa hsb
    dsimp only [C, χ, A, B, V]
    have hai : chartInv a (chartPt a (realVelocityBaseFlow g p.proj u s)) =
        realVelocityBaseFlow g p.proj u s :=
      (extChartAt (ComplexModel n) a).left_inv (by simpa only [extChartAt_source] using hsa)
    have hbi : chartInv b (chartPt b (realVelocityBaseFlow g p.proj u (s + e))) =
        realVelocityBaseFlow g p.proj u (s + e) :=
      (extChartAt (ComplexModel n) b).left_inv (by simpa only [extChartAt_source] using hsb)
    rw [hai, hbi]
    have hend : realGeodesicEndpointMap g e
        (realGeodesicFlow g (⟨p.proj, u⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) s) =
        (realVelocityBaseFlow g p.proj u s, realVelocityBaseFlow g p.proj u (s + e)) := by
      apply Prod.ext
      · rfl
      · exact congrArg Bundle.TotalSpace.proj
          (realGeodesicFlow_add g (⟨p.proj, u⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) s e).symm
    rw [← hend, hu]
  have hheld : (fun u => C (A u, B p.2)) =ᶠ[𝓝 p.2]
      (fun u => O (P (realVelocityBaseFlow g p.proj u s, b))) := by
    filter_upwards [hsourceA] with u hsa
    dsimp only [C, χ, A, B]
    have hai : chartInv a (chartPt a (realVelocityBaseFlow g p.proj u s)) =
        realVelocityBaseFlow g p.proj u s :=
      (extChartAt (ComplexModel n) a).left_inv (by simpa only [extChartAt_source] using hsa)
    have hbi : chartInv b (chartPt b b) = b :=
      (extChartAt (ComplexModel n) b).left_inv (mem_extChartAt_source b)
    change chartPt b (realVelocityBaseFlow g p.proj p.2 (s + e)) = chartPt b b at hB₀
    rw [hai, hB₀, hbi]
  have hderiv := held_second_fderiv A B C V p.2 w
     (hA.differentiableAt (by simp)) (hB.differentiableAt (by simp))
    (by rw [hA₀, hB₀]; exact hC.differentiableAt (by simp))
    (hV.differentiableAt (by simp)) hBw heq
  change fderiv ℝ (fun u => O (P (realVelocityBaseFlow g p.proj u s, b))) p.2 w =
    fderiv ℝ V p.2 w
  rw [← hheld.fderiv_eq]
  exact hderiv


/-- With the actual terminal point held fixed, the endpoint branch has the
same initial-velocity derivative as the true intermediate phase. -/
theorem realEndpointBranch_held_phase_fderiv
    (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (s e : ℝ)
    (U : Set (M.Carrier × M.Carrier)) (hU : IsOpen U)
    (P : M.Carrier × M.Carrier → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (hPU : realGeodesicEndpointMap g e (realGeodesicFlow g p s) ∈ U)
    (hP : letI := manifold_realSmooth M; letI := manifold_realPhase M;
      ContMDiffOn (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n))
        (realPhaseModel n) 1 P U)
    (hleft : letI := manifold_realSmooth M; letI := manifold_realPhase M;
      ∀ᶠ q' in 𝓝 (realGeodesicFlow g p s),
        P (realGeodesicEndpointMap g e q') = q')
    (w : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj)
    (hJ : realGeodesicJacobiField g p w (s + e) = 0) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
    letI := underlyingRealTangentInnerProductSpace g.form p.proj
    fderiv ℝ (fun u => extChartAt (realPhaseModel n) (realGeodesicFlow g p s)
      (P (realVelocityBaseFlow g p.proj u s,
        (realGeodesicFlow g p (s + e)).proj))) p.2 w =
      fderiv ℝ (realVelocityPhaseCoordinates g p s) p.2 w := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
  letI := underlyingRealTangentInnerProductSpace g.form p.proj
  have hO : ContMDiffAt (realPhaseModel n) 𝓘(ℝ, ComplexVector n × ComplexVector n) 1
      (extChartAt (realPhaseModel n) (realGeodesicFlow g p s))
      (realGeodesicFlow g p s) := contMDiffAt_extChartAt
  exact realEndpointBranch_held_observable_fderiv g p s e U hU P hPU hP hleft
    (extChartAt (realPhaseModel n) (realGeodesicFlow g p s)) hO w hJ

/-- Flowing the held-endpoint branch to its actual terminal time has the
same full phase derivative as the original geodesic variation. -/
theorem realEndpointBranch_held_terminal_phase_fderiv
    (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (s e : ℝ)
    (U : Set (M.Carrier × M.Carrier)) (hU : IsOpen U)
    (P : M.Carrier × M.Carrier → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (hPU : realGeodesicEndpointMap g e (realGeodesicFlow g p s) ∈ U)
    (hP : letI := manifold_realSmooth M; letI := manifold_realPhase M;
      ContMDiffOn (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n))
        (realPhaseModel n) 1 P U)
    (hleft : letI := manifold_realSmooth M; letI := manifold_realPhase M;
      ∀ᶠ q' in 𝓝 (realGeodesicFlow g p s),
        P (realGeodesicEndpointMap g e q') = q')
    (w : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj)
    (hJ : realGeodesicJacobiField g p w (s + e) = 0) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
    letI := underlyingRealTangentInnerProductSpace g.form p.proj
    fderiv ℝ (fun u => extChartAt (realPhaseModel n) (realGeodesicFlow g p (s + e))
      (realGeodesicFlow g
        (P (realVelocityBaseFlow g p.proj u s,
          (realGeodesicFlow g p (s + e)).proj)) e)) p.2 w =
      fderiv ℝ (realVelocityPhaseCoordinates g p (s + e)) p.2 w := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
  letI := underlyingRealTangentInnerProductSpace g.form p.proj
  let qS := realGeodesicFlow g p s
  let qT := realGeodesicFlow g p (s + e)
  let O : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier →
      ComplexVector n × ComplexVector n :=
    fun q => extChartAt (realPhaseModel n) qT (realGeodesicFlow g q e)
  have htime : realGeodesicFlow g qS e = qT := (realGeodesicFlow_add g p s e).symm
  have hchart : ContMDiffAt (realPhaseModel n) 𝓘(ℝ, ComplexVector n × ComplexVector n)
      1 (extChartAt (realPhaseModel n) qT) (realGeodesicFlow g qS e) := by
    rw [htime]
    exact contMDiffAt_extChartAt
  have hO : ContMDiffAt (realPhaseModel n) 𝓘(ℝ, ComplexVector n × ComplexVector n)
      1 O qS := hchart.comp qS (realGeodesicPhaseFlow_contMDiff g e qS)
  have h := realEndpointBranch_held_observable_fderiv g p s e U hU P hPU hP hleft O hO w hJ
  have hV : (fun u : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj =>
      O (realGeodesicFlow g
        (⟨p.proj, u⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) s)) =
      realVelocityPhaseCoordinates g p (s + e) := by
    funext u
    change extChartAt (realPhaseModel n) qT
      (realGeodesicFlow g (realGeodesicFlow g
        (⟨p.proj, u⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) s) e) =
      extChartAt (realPhaseModel n) qT
        (realGeodesicFlow g (⟨p.proj, u⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (s + e))
    rw [← realGeodesicFlow_add]
  rw [hV] at h
  exact h

end Yau.LeafProofs.L12Aux
