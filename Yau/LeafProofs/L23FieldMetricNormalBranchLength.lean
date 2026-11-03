import Yau.LeafProofs.L23FieldMetricGeodesicEnergy

/-! Each actual normal branch has exactly the original project distance as length. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold ENNReal
namespace Yau.LeafProofs.L23Aux
open L12Aux L23LocalDistanceContract
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 600000

theorem fieldNormalBranchCurve_actualSpeedSq_zero
    (h : HermitianField M) (c : M.Carrier) (O : Set M.Carrier)
    (B : Set (ComplexVector n)) (ρ ε : ℝ)
    (X : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n)
    (e : OpenPartialHomeomorph (ComplexVector n × ComplexVector n) (ComplexVector n × ComplexVector n))
    (H : FieldNormalEndpointData h c O B ρ ε X e)
    (q y : M.Carrier) (hq : q ∈ (chartAt (ComplexVector n) c).source)
    (hy : y ∈ (chartAt (ComplexVector n) c).source)
    (hpair : (chartPt c q,chartPt c y) ∈ e.target) :
    actualSpeedSq h (fieldNormalBranchCurve c X e q y) 0 = inducedDistance h q y^2 := by
  letI := manifold_realSmooth M
  have Hcurve := fieldNormalBranchCurve_data h c O B ρ ε X e H q y hq hy hpair
  rcases H with ⟨hB,hcB,hBsub,hρ,hε,hsource,heq,hX,hinv,hdata,hzero⟩
  let p := e.symm (chartPt c q,chartPt c y)
  have hp : p ∈ e.source := e.map_target hpair
  have h₀ : (0 : ℝ) ∈ Set.Ioo (-ε) (1+ε) := by constructor <;> linarith
  have hsrc : fieldNormalBranchCurve c X e q y 0 ∈ (chartAt (ComplexVector n) c).source := by
    rw [Hcurve.1]
    exact hq
  have HC : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 (fieldNormalBranchCurve c X e q y) 0 :=
    (((Hcurve.2.2.1).1 0 h₀).contMDiffAt (isOpen_Ioo.mem_nhds h₀)).of_le (by norm_num)
  have HA := actualSpeedSq_eq_chartEnergy h (fieldNormalBranchCurve c X e q y) c 0 hsrc HC
  have HS := geoChartState_normalFamilyPhase c X e.open_source isOpen_Ioo hX
    (fun p hp => (hdata p hp).2.2.1) p hp 0 h₀
  have HI := normalFamilyPhase_initial X e.open_source isOpen_Ioo h₀ hX
    (fun p hp => ⟨(hdata p hp).1,(hdata p hp).2.1⟩) p hp
  change geoChartState (fieldNormalBranchCurve c X e q y) c 0 = normalFamilyPhase X p 0 at HS
  rw [HS,HI] at HA
  have HD := normalEndpoint_distanceSq_eq_energy h c X e heq
    (fun p hp => (hdata p hp).2.2.2.2.2) hpair
  have hqinv : chartInv c (chartPt c q) = q :=
    (extChartAt (ComplexModel n) c).left_inv (by simpa only [extChartAt_source] using hq)
  have hyinv : chartInv c (chartPt c y) = y :=
    (extChartAt (ComplexModel n) c).left_inv (by simpa only [extChartAt_source] using hy)
  rw [hqinv,hyinv] at HD
  exact HA.trans HD.symm

theorem fieldNormalBranchCurve_pathELength
    (h : HermitianField M) (hh : MetricSmooth h) (c : M.Carrier) (O : Set M.Carrier)
    (B : Set (ComplexVector n)) (ρ ε : ℝ)
    (X : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n)
    (e : OpenPartialHomeomorph (ComplexVector n × ComplexVector n) (ComplexVector n × ComplexVector n))
    (H : FieldNormalEndpointData h c O B ρ ε X e)
    (q y : M.Carrier) (hq : q ∈ (chartAt (ComplexVector n) c).source)
    (hy : y ∈ (chartAt (ComplexVector n) c).source)
    (hpair : (chartPt c q,chartPt c y) ∈ e.target) :
    fieldPathELength h (fieldNormalBranchCurve c X e q y) 0 1 = ENNReal.ofReal (inducedDistance h q y) := by
  have Hcurve := fieldNormalBranchCurve_data h c O B ρ ε X e H q y hq hy hpair
  have HL := fieldGeodesic_unit_pathELength h hh (fieldNormalBranchCurve c X e q y) H.2.2.2.2.1 Hcurve.2.2.1
  rw [fieldNormalBranchCurve_actualSpeedSq_zero h c O B ρ ε X e H q y hq hy hpair,
    Real.sqrt_sq (inducedDistance_nonneg h hh q y)] at HL
  exact HL

end Yau.LeafProofs.L23Aux
