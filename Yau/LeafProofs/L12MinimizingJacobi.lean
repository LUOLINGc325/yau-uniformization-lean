import Yau.LeafProofs.L12BrokenJacobiDirection
import Yau.LeafProofs.L12BishopAssembly

/-! Minimizing geodesics have no interior singular Jacobi differential,
proved using the actual finite broken-geodesic energy and its Hessian. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff Bundle ComplexOrder InnerProductSpace
namespace Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

/-- An actual minimizing geodesic has no singular genuine Jacobi
differential strictly before its endpoint. -/
theorem realGeodesicJacobiMatrix_det_ne_zero_of_minimizing (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) {T : ℝ} (hT : 0 < T) :
    letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
    letI := underlyingRealTangentInnerProductSpace g.form p.proj
    inducedDistance g.form p.proj (realGeodesicFlow g p T).proj = T * ‖p.2‖ →
      ∀ t ∈ Set.Ioo (0 : ℝ) T, (realGeodesicJacobiMatrix g p t).det ≠ 0 := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
  letI := underlyingRealTangentInnerProductSpace g.form p.proj
  intro hmin t ht hdet
  obtain ⟨s, e, d, hs, he, hd, hse, hsed, hreverse, hlast⟩ :=
    exists_realGeodesic_short_nonsingular_segments g p ht.1 ht.2
  have hdetse : (realGeodesicJacobiMatrix g p (s + e)).det = 0 := by rw [hse]; exact hdet
  obtain ⟨w, hw, hJ, hK⟩ := exists_realJacobi_kernel_of_det_eq_zero g p (s + e) hdetse
  let qS := realGeodesicFlow g p s
  let qT := realGeodesicFlow g p (s + e)
  let a := qS.proj
  let y := qT.proj
  let z := (realGeodesicFlow g p (s + e + d)).proj
  let θ₀ : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n := (p.2, chartPt y y)
  let K := (fderiv ℝ (realVelocityPhaseCoordinates g p (s + e)) p.2 w).2
  have hlast' : (realGeodesicJacobiMatrix g qT d).det ≠ 0 := by
    dsimp only [qT]
    rw [hse]
    exact hlast
  obtain ⟨U, hU, hPU, P, hP, hPcenter, hPends, hleft⟩ :=
    exists_realGeodesic_endpointBranch_reversed g qS e hreverse
  obtain ⟨V, hV, hQV, Q, hQ, hQcenter, hQends, _⟩ :=
    exists_realGeodesic_endpointBranch g qT d hlast'
  have hendP : realGeodesicEndpointMap g e qS = (a, y) := by
    apply Prod.ext
    · rfl
    · exact congrArg Bundle.TotalSpace.proj (realGeodesicFlow_add g p s e).symm
  have hendQ : realGeodesicEndpointMap g d qT = (y, z) := by
    apply Prod.ext
    · rfl
    · exact congrArg Bundle.TotalSpace.proj (realGeodesicFlow_add g p (s + e) d).symm
  have hPc : P (a, y) = qS := hendP ▸ hPcenter
  have hQc : Q (y, z) = qT := hendQ ▸ hQcenter
  have hInv : chartInv y (chartPt y y) = y :=
    (extChartAt (ComplexModel n) y).left_inv (mem_extChartAt_source y)
  have hFirst₀ : realBrokenPhaseFirst g p s θ₀ = qS := rfl
  have hMiddle₀ : realBrokenPhaseMiddle g p s P y θ₀ = qS := by
    change P (a, chartInv y (chartPt y y)) = qS
    rw [hInv, hPc]
  have hLast₀ : realBrokenPhaseLast p Q y z θ₀ = qT := by
    change Q (chartInv y (chartPt y y), z) = qT
    rw [hInv, hQc]
  have hTerminal₀ : realGeodesicFlow g (realBrokenPhaseMiddle g p s P y θ₀) e = qT := by
    rw [hMiddle₀]
    exact (realGeodesicFlow_add g p s e).symm
  have hPUθ : (realVelocityBaseFlow g p.proj θ₀.1 s, chartInv y θ₀.2) ∈ U := by
    change (a, chartInv y (chartPt y y)) ∈ U
    rw [hInv, ← hendP]
    exact hPU
  have hQVθ : (chartInv y θ₀.2, z) ∈ V := by
    change (chartInv y (chartPt y y), z) ∈ V
    rw [hInv, ← hendQ]
    exact hQV
  have ha : realVelocityBaseFlow g p.proj θ₀.1 s ∈ (chartAt (ComplexVector n) a).source :=
    mem_chart_source _ _
  have hy : θ₀.2 ∈ chartTarget y := mem_extChartAt_target y
  have hm0 := realBrokenMismatch0_contDiffAt g p s U hU P a y θ₀ hy hPUθ
    (by rw [hFirst₀]; exact mem_chart_source _ _)
    (by rw [hMiddle₀]; exact mem_chart_source _ _) hP
  have hm1 := realBrokenMismatch1_contDiffAt g p s e U V hU hV P Q y z θ₀ hy hPUθ hQVθ
    (by rw [hTerminal₀]; exact mem_chart_source _ _)
    (by rw [hLast₀]; exact mem_chart_source _ _) hP hQ
  have hm00 : realBrokenMismatch0 g p s P a y θ₀ = 0 := by
    dsimp only [realBrokenMismatch0]
    rw [hFirst₀, hMiddle₀, sub_self]
  have hm10 : realBrokenMismatch1 g p s e P Q y z θ₀ = 0 := by
    dsimp only [realBrokenMismatch1]
    rw [hTerminal₀, hLast₀, sub_self]
  have hdir := realBrokenMismatch_fderiv_Jacobi_direction g p s e U V hU hV P Q z
    hPU (hendQ ▸ hQV) hQc w hJ hP hQ hleft
  have hfirst := realBrokenEndpointEnergy_firstDerivative_eventually g p s e d U V hU hV
    P Q a y z θ₀ hPUθ hQVθ ha hy hP hQ hPends hQends
  have hminr := realGeodesicFlow_dist_eq_of_minimizing g p T hmin (s + e + d)
    ⟨by linarith, hsed.le⟩
  have hminF := realBrokenEndpointEnergy_isLocalMin g p hs he hd U V hU hV P Q
    hPU hQV hPcenter hQcenter hPends hQends hminr
  exact (not_localMin_of_broken_energy_mixed_positive
    (realBrokenCoefficient0_continuousAt g p s a θ₀ ha)
    (realBrokenCoefficient1_continuousAt g p y θ₀ hy)
    (hm0.differentiableAt (by simp)).hasFDerivAt
    (hm1.differentiableAt (by simp)).hasFDerivAt hm00 hm10 hfirst
    (w, 0) K hdir.1 hdir.2 rfl (realMetricInChart g.form y (chartPt y y))
    (by intro b h; rfl) (realMetricInChart_self_pos g y hK)) hminF

/-- Positivity is inherited from the regular initial Jacobi condition,
because actual minimizing segments have no interior singular differential. -/
theorem realMinimizingJacobiPositive (g : SmoothMetric M) : MinimizingJacobiPositiveTarget g := by
  intro p T hT hmin t ht
  letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
  letI := underlyingRealTangentInnerProductSpace g.form p.proj
  have hne := realGeodesicJacobiMatrix_det_ne_zero_of_minimizing g p hT hmin
  have hA : Continuous (fun u => realGeodesicJacobiMatrix g p u) :=
    continuous_pi fun i => continuous_pi fun j => continuous_iff_continuousAt.mpr
      (fun u => (realGeodesicJacobiMatrix_hasDerivAt g p u i j).continuousAt)
  have hD := hA.matrix_det
  have hsmall : ∀ᶠ c in 𝓝[>] (0 : ℝ), c < t :=
    (eventually_lt_nhds ht.1).filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ c in 𝓝[>] (0 : ℝ), 0 < c := self_mem_nhdsWithin
  obtain ⟨c, hc, hct, hcD⟩ :=
    (hpos.and (hsmall.and (realGeodesicJacobiMatrix_det_pos_near_zero g p))).exists
  by_contra hnot
  have htD : (realGeodesicJacobiMatrix g p t).det ≤ 0 := le_of_not_gt hnot
  obtain ⟨u, hu, hDu⟩ := intermediate_value_Icc' hct.le hD.continuousOn ⟨htD, hcD.le⟩
  exact hne u ⟨lt_of_lt_of_le hc hu.1, lt_of_le_of_lt hu.2 ht.2⟩ hDu

/-- The exact frozen Bishop--Gromov leaf, for the original complete Kähler
metric, its genuine length distance, and every genuine Riemannian volume. -/
theorem bishopGromov : Yau.LeafObligations.L12 :=
  bishopGromov_of_minimizingJacobiPositive (fun _ _ g => realMinimizingJacobiPositive g)

end Yau.LeafProofs.L12Aux
