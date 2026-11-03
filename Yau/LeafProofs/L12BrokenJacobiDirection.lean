import Yau.LeafProofs.L12BrokenEnergyGradient
import Yau.LeafProofs.L12EndpointBranchVariation

/-! The genuine Jacobi-kernel direction of the actual broken-energy
velocity mismatches. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff Bundle ComplexOrder InnerProductSpace
namespace Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

/-- A genuine Jacobi field with zero terminal position gives zero first
mismatch derivative and its true nontrivial terminal velocity as the second
mismatch derivative. -/
theorem realBrokenMismatch_fderiv_Jacobi_direction (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (s e : ℝ)
    (U V : Set (M.Carrier × M.Carrier)) (hU : IsOpen U) (hV : IsOpen V)
    (P Q : M.Carrier × M.Carrier → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (z : M.Carrier)
    (hPU : realGeodesicEndpointMap g e (realGeodesicFlow g p s) ∈ U)
    (hQV : ((realGeodesicFlow g p (s + e)).proj, z) ∈ V)
    (hQcenter : Q ((realGeodesicFlow g p (s + e)).proj, z) = realGeodesicFlow g p (s + e))
    (w : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj)
    (hJ : realGeodesicJacobiField g p w (s + e) = 0) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
    letI := underlyingRealTangentInnerProductSpace g.form p.proj
    ContMDiffOn (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n)) (realPhaseModel n) 1 P U →
    ContMDiffOn (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n)) (realPhaseModel n) 1 Q V →
    (∀ᶠ q' in 𝓝 (realGeodesicFlow g p s), P (realGeodesicEndpointMap g e q') = q') →
    let a := (realGeodesicFlow g p s).proj
    let y := (realGeodesicFlow g p (s + e)).proj
    let θ₀ := (p.2, chartPt y y)
    fderiv ℝ (realBrokenMismatch0 g p s P a y) θ₀ (w, 0) = 0 ∧
      fderiv ℝ (realBrokenMismatch1 g p s e P Q y z) θ₀ (w, 0) =
        (fderiv ℝ (realVelocityPhaseCoordinates g p (s + e)) p.2 w).2 := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
  letI := underlyingRealTangentInnerProductSpace g.form p.proj
  intro hP hQ hleft
  let qS := realGeodesicFlow g p s
  let qT := realGeodesicFlow g p (s + e)
  let a := qS.proj
  let y := qT.proj
  let c := chartPt y y
  let θ₀ : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n := (p.2, c)
  have hInv : chartInv y c = y := (extChartAt (ComplexModel n) y).left_inv (mem_extChartAt_source y)
  have hend : realGeodesicEndpointMap g e qS = (a, y) := by
    apply Prod.ext
    · rfl
    · exact congrArg Bundle.TotalSpace.proj (realGeodesicFlow_add g p s e).symm
  have hPc : P (a, y) = qS := hend ▸ hleft.self_of_nhds
  have hPU₀ : (a, y) ∈ U := hend ▸ hPU
  have hFirst₀ : realBrokenPhaseFirst g p s θ₀ = qS := rfl
  have hMiddle₀ : realBrokenPhaseMiddle g p s P y θ₀ = qS := by
    change P (a, chartInv y c) = qS
    rw [hInv, hPc]
  have hLast₀ : realBrokenPhaseLast p Q y z θ₀ = qT := by
    change Q (chartInv y c, z) = qT
    rw [hInv]
    exact hQcenter
  have hTerminal₀ : realGeodesicFlow g (realBrokenPhaseMiddle g p s P y θ₀) e = qT := by
    rw [hMiddle₀]
    exact (realGeodesicFlow_add g p s e).symm
  have hPUθ : ((realBrokenPhaseFirst g p s θ₀).proj, chartInv y θ₀.2) ∈ U := by
    rw [hFirst₀]
    change (a, chartInv y c) ∈ U
    rw [hInv]
    exact hPU₀
  have hQVθ : (chartInv y θ₀.2, z) ∈ V := by
    change (chartInv y c, z) ∈ V
    rw [hInv]
    exact hQV
  have hm0 := realBrokenMismatch0_contDiffAt g p s U hU P a y θ₀
    (mem_extChartAt_target y) hPUθ (by rw [hFirst₀]; exact mem_chart_source _ _)
    (by rw [hMiddle₀]; exact mem_chart_source _ _) hP
  have hm1 := realBrokenMismatch1_contDiffAt g p s e U V hU hV P Q y z θ₀
    (mem_extChartAt_target y) hPUθ hQVθ (by rw [hTerminal₀]; exact mem_chart_source _ _)
    (by rw [hLast₀]; exact mem_chart_source _ _) hP hQ
  let T : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier :=
    fun u => realGeodesicFlow g (⟨p.proj, u⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) s
  let H : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier :=
    fun u => P (realVelocityBaseFlow g p.proj u s, y)
  let HT := fun u => realGeodesicFlow g (H u) e
  have hT : ContMDiffAt 𝓘(ℝ, TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) (realPhaseModel n) 1 T p.2 :=
    realVelocityFlow_contMDiff g p.proj s p.2
  have hH : ContMDiffAt 𝓘(ℝ, TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) (realPhaseModel n) 1 H p.2 :=
    (hP.contMDiffAt (hU.mem_nhds hPU₀)).comp p.2
      ((realVelocityBaseFlow_contMDiff g p.proj s p.2).prodMk contMDiffAt_const)
  have hH₀ : H p.2 = qS := hPc
  have hHT : ContMDiffAt 𝓘(ℝ, TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) (realPhaseModel n) 1 HT p.2 :=
    (realGeodesicPhaseFlow_contMDiff g e (H p.2)).comp p.2 hH
  have hHT₀ : HT p.2 = qT := by
    dsimp only [HT]
    rw [hH₀]
    exact (realGeodesicFlow_add g p s e).symm
  have hVTsmooth : ContMDiffAt (realPhaseModel n) 𝓘(ℝ, ComplexVector n) 1
      (realChartVelocity a) (T p.2) :=
    (realChartVelocity_contMDiffAt a qS (mem_chart_source _ _)).of_le (by simp)
  have hVT : DifferentiableAt ℝ (fun u => realChartVelocity a (T u)) p.2 :=
    (hVTsmooth.comp p.2 hT).contDiffAt.differentiableAt (by simp)
  have hVH : DifferentiableAt ℝ (fun u => realChartVelocity a (H u)) p.2 := by
    have hh : ContMDiffAt (realPhaseModel n) 𝓘(ℝ, ComplexVector n) 1 (realChartVelocity a) (H p.2) := by
      rw [hH₀]
      exact (realChartVelocity_contMDiffAt a qS (mem_chart_source _ _)).of_le (by simp)
    exact (hh.comp p.2 hH).contDiffAt.differentiableAt (by simp)
  have hVHT : DifferentiableAt ℝ (fun u => realChartVelocity y (HT u)) p.2 := by
    have hh : ContMDiffAt (realPhaseModel n) 𝓘(ℝ, ComplexVector n) 1 (realChartVelocity y) (HT p.2) := by
      rw [hHT₀]
      exact (realChartVelocity_contMDiffAt y qT (mem_chart_source _ _)).of_le (by simp)
    exact (hh.comp p.2 hHT).contDiffAt.differentiableAt (by simp)
  have hDT := realChartVelocity_comp_fderiv T p.2 hT
  have hDH := realChartVelocity_comp_fderiv H p.2 hH
  rw [hH₀] at hDH
  have hDHT := realChartVelocity_comp_fderiv HT p.2 hHT
  rw [hHT₀] at hDHT
  have hheld := realEndpointBranch_held_phase_fderiv g p s e U hU P hPU hP hleft w hJ
  have hterminal := realEndpointBranch_held_terminal_phase_fderiv g p s e U hU P hPU hP hleft w hJ
  have hvel : fderiv ℝ (fun u => realChartVelocity a (H u)) p.2 w =
      fderiv ℝ (fun u => realChartVelocity a (T u)) p.2 w := by
    rw [hDH, hDT]
    exact congrArg Prod.snd hheld
  have hvelT : fderiv ℝ (fun u => realChartVelocity y (HT u)) p.2 w =
      (fderiv ℝ (realVelocityPhaseCoordinates g p (s + e)) p.2 w).2 := by
    rw [hDHT]
    exact congrArg Prod.snd hterminal
  let i : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj →
      TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n := fun u => (u, c)
  have hi : HasFDerivAt i (ContinuousLinearMap.inl ℝ
      (TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) (ComplexVector n)) p.2 :=
    hasFDerivAt_prodMk_left p.2 c
  have heq0 : realBrokenMismatch0 g p s P a y ∘ i =
      (fun u => realChartVelocity a (T u) - realChartVelocity a (H u)) := by
    funext u
    dsimp only [realBrokenMismatch0, realBrokenPhaseFirst, realBrokenPhaseMiddle, i, T, H, Function.comp_apply]
    rw [hInv]
    rfl
  have heq1 : realBrokenMismatch1 g p s e P Q y z ∘ i =
      (fun u => realChartVelocity y (HT u) - realChartVelocity y (Q (y, z))) := by
    funext u
    dsimp only [realBrokenMismatch1, realBrokenPhaseMiddle, realBrokenPhaseFirst, realBrokenPhaseLast,
      i, HT, H, Function.comp_apply]
    rw [hInv]
    rfl
  have hline0 := (hm0.differentiableAt (by simp)).hasFDerivAt.comp p.2 hi
  have hline1 := (hm1.differentiableAt (by simp)).hasFDerivAt.comp p.2 hi
  change HasFDerivAt (realBrokenMismatch0 g p s P a y ∘ i) _ p.2 at hline0
  change HasFDerivAt (realBrokenMismatch1 g p s e P Q y z ∘ i) _ p.2 at hline1
  rw [heq0] at hline0
  rw [heq1] at hline1
  have hD0 := hline0.unique (hVT.hasFDerivAt.sub hVH.hasFDerivAt)
  have hD1 := hline1.unique (hVHT.hasFDerivAt.sub
    (hasFDerivAt_const (realChartVelocity y (Q (y, z))) p.2))
  constructor
  · have hh := congrArg (fun L : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj →L[ℝ] ComplexVector n => L w) hD0
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
      ContinuousLinearMap.sub_apply] at hh
    rw [hvel, sub_self] at hh
    exact hh
  · have hh := congrArg (fun L : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj →L[ℝ] ComplexVector n => L w) hD1
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.zero_apply, sub_zero] at hh
    exact hh.trans hvelT

end Yau.LeafProofs.L12Aux
