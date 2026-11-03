import Yau.LeafProofs.L19EndpointEnergyBounds

/-! The actual Hopf--Rinow segment and its strict reverse midpoint yield
a genuine C1 endpoint branch about the required second half. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff Bundle ComplexOrder InnerProductSpace
namespace Yau.LeafProofs.L19Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

/-- Restrict the genuine two-endpoint branch to its fixed initial point,
using genuine terminal chart coordinates on an actual open neighborhood. -/
theorem exists_realEndpointChartBranch
    (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (d : ℝ)
    (U : Set (M.Carrier × M.Carrier)) (hU : IsOpen U)
    (hpU : realGeodesicEndpointMap g d p ∈ U)
    (P : M.Carrier × M.Carrier → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ContMDiffOn (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n)) (realPhaseModel n) 1 P U →
    P (realGeodesicEndpointMap g d p) = p →
    (∀ y ∈ U, (P y).proj = y.1 ∧ (realGeodesicFlow g (P y) d).proj = y.2) →
    ∃ O : Set (ComplexVector n), IsOpen O ∧
      chartPt (realGeodesicFlow g p d).proj (realGeodesicFlow g p d).proj ∈ O ∧
      ∃ Q : ComplexVector n → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier,
        ContMDiffOn 𝓘(ℝ, ComplexVector n) (realPhaseModel n) 1 Q O ∧
        Q (chartPt (realGeodesicFlow g p d).proj (realGeodesicFlow g p d).proj) = p ∧
        (∀ y ∈ O, (Q y).proj = p.proj ∧ (realGeodesicFlow g (Q y) d).proj =
          chartInv (realGeodesicFlow g p d).proj y) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  intro hP hPp hends
  let q := (realGeodesicFlow g p d).proj
  let z := chartPt q q
  let F := fun y : ComplexVector n => (p.proj, chartInv q y)
  let Q := P ∘ F
  have hF (y : ComplexVector n) (hy : y ∈ chartTarget q) :
      ContMDiffAt 𝓘(ℝ, ComplexVector n)
        (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n)) 1 F y :=
    contMDiffAt_const.prodMk ((contMDiffAt_chartInv_real q y hy).of_le (by simp))
  have hFz : F z = realGeodesicEndpointMap g d p := by
    change (p.proj, chartInv q (chartPt q q)) = (p.proj, q)
    exact Prod.ext rfl ((extChartAt (ComplexModel n) q).left_inv (mem_extChartAt_source q))
  let O := {y | y ∈ chartTarget q ∧ F y ∈ U}
  have hO : IsOpen O := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    exact inter_mem
      ((isOpen_extChartAt_target (I := ComplexModel n) q).mem_nhds hy.1)
      ((hF y hy.1).continuousAt.preimage_mem_nhds (hU.mem_nhds hy.2))
  have hz : z ∈ O := ⟨mem_extChartAt_target q, by rw [hFz]; exact hpU⟩
  refine ⟨O, hO, hz, Q, ?_, ?_, ?_⟩
  · intro y hy
    exact ((hP.contMDiffAt (hU.mem_nhds hy.2)).comp y (hF y hy.1)).contMDiffWithinAt
  · change P (F z) = p
    rw [hFz, hPp]
  · intro y hy
    exact hends (F y) hy.2

/-- The actual half-time phase of a genuinely minimizing time-one segment
has a C1 endpoint branch, because its reverse half lies strictly before
the endpoint of the reversed minimizing time-one segment. -/
theorem exists_realMinimizingMidpointBranch
    (g : SmoothMetric M) (x y : M.Carrier) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    letI : ∀ a : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) a) :=
      fun a => underlyingRealTangentNormedAddCommGroup g.form a
    letI : ∀ a : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) a) :=
      fun a => underlyingRealTangentInnerProductSpace g.form a
    ∃ p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier,
      ‖p.2‖ = inducedDistance g.form x y ∧ (realGeodesicFlow g p (1 / 2)).proj = y ∧
      inducedDistance g.form x p.proj = inducedDistance g.form x y / 2 ∧
      inducedDistance g.form p.proj y = inducedDistance g.form x y / 2 ∧
      ∃ O : Set (ComplexVector n), IsOpen O ∧
        chartPt (realGeodesicFlow g p (1 / 2)).proj (realGeodesicFlow g p (1 / 2)).proj ∈ O ∧
        ∃ Q : ComplexVector n → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier,
          ContMDiffOn 𝓘(ℝ, ComplexVector n) (realPhaseModel n) 1 Q O ∧
          Q (chartPt (realGeodesicFlow g p (1 / 2)).proj (realGeodesicFlow g p (1 / 2)).proj) = p ∧
          (∀ z ∈ O, (Q z).proj = p.proj ∧ (realGeodesicFlow g (Q z) (1 / 2)).proj =
            chartInv (realGeodesicFlow g p (1 / 2)).proj z) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI : ∀ a : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) a) :=
    fun a => underlyingRealTangentNormedAddCommGroup g.form a
  letI : ∀ a : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) a) :=
    fun a => underlyingRealTangentInnerProductSpace g.form a
  obtain ⟨v, hv, hnv⟩ := exists_minimizing_realExponential g x y
  let p₀ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier := ⟨x, v⟩
  let p := realGeodesicFlow g p₀ (1 / 2)
  let pR := realSegmentReverse g 1 p₀
  have hfull : (realGeodesicFlow g p₀ 1).proj = y := hv
  have hmin : inducedDistance g.form p₀.proj (realGeodesicFlow g p₀ 1).proj = 1 * ‖p₀.2‖ := by
    rw [hfull, one_mul]
    exact hnv.symm
  have hpn : ‖p.2‖ = inducedDistance g.form x y := by
    rw [realGeodesicFlow_velocity_norm]
    exact hnv
  have htail : (realGeodesicFlow g p (1 / 2)).proj = y := by
    dsimp only [p]
    rw [← realGeodesicFlow_add]
    convert hfull using 2 <;> norm_num
  have hRbase : pR.proj = y := hfull
  have hRend : (realGeodesicFlow g pR 1).proj = x := by
    rw [realSegmentReverse_terminal]
    rfl
  have hRE := realSegmentEnergy_reverse g 1 p₀
  dsimp only [realSegmentEnergy] at hRE
  have hRE' : realTangentEnergy g.form pR = realTangentEnergy g.form p₀ := by linarith
  rw [realTangentEnergy_eq_norm_sq, realTangentEnergy_eq_norm_sq] at hRE'
  have hRn : ‖pR.2‖ = inducedDistance g.form x y := by
    nlinarith [norm_nonneg pR.2, norm_nonneg p₀.2]
  have hRmin : inducedDistance g.form pR.proj (realGeodesicFlow g pR 1).proj = 1 * ‖pR.2‖ := by
    rw [hRn, one_mul, hRbase, hRend]
    exact g.induced_distance_symm _ _
  have hrev : realSegmentReverse g (1 / 2) p = pR := by
    dsimp only [realSegmentReverse, p, pR]
    rw [← realGeodesicFlow_add]
    congr 1
    norm_num
  have hdet : (realGeodesicJacobiMatrix g (realSegmentReverse g (1 / 2) p) (1 / 2)).det ≠ 0 := by
    rw [hrev]
    exact realGeodesicJacobiMatrix_det_ne_zero_of_minimizing g pR (by norm_num) hRmin
      (1 / 2) (by norm_num)
  obtain ⟨U, hU, hpU, P, hP, hPp, hPends, _⟩ :=
    exists_realGeodesic_endpointBranch_reversed g p (1 / 2) hdet
  have hfirst := realGeodesicFlow_dist_eq_of_minimizing g p₀ 1 hmin (1 / 2) (by norm_num)
  have hfirst' : inducedDistance g.form x p.proj = inducedDistance g.form x y / 2 := by
    rw [hnv] at hfirst
    convert hfirst using 1 <;> ring
  have hlast : inducedDistance g.form p.proj y = inducedDistance g.form x y / 2 := by
    have hu := realGeodesicFlow_distFrom_le g p (1 / 2)
    rw [htail, realTangentEnergy_eq_norm_sq, Real.sqrt_sq (norm_nonneg p.2), hpn] at hu
    norm_num at hu
    have htri := g.induced_distance_triangle x p.proj y
    rw [hfirst'] at htri
    linarith
  exact ⟨p, hpn, htail, hfirst', hlast,
    exists_realEndpointChartBranch g p (1 / 2) U hU hpU P hP hPp hPends⟩

end Yau.LeafProofs.L19Aux
