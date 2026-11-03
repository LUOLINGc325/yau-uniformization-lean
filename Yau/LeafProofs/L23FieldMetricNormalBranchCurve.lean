import Yau.LeafProofs.L23FieldMetricNormalData
import Yau.LeafProofs.L23FieldMetricNormalPhase

/-! The actual manifold geodesic selected by the inverse normal endpoint chart. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux L23LocalDistanceContract
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 800000

def fieldNormalBranchCurve (c : M.Carrier)
    (X : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n)
    (e : OpenPartialHomeomorph (ComplexVector n × ComplexVector n) (ComplexVector n × ComplexVector n))
    (q y : M.Carrier) (u : ℝ) : M.Carrier :=
  chartInv c (X (e.symm (chartPt c q,chartPt c y)) u)

theorem fieldNormalBranchCurve_data
    (h : HermitianField M) (c : M.Carrier) (O : Set M.Carrier)
    (B : Set (ComplexVector n)) (ρ ε : ℝ)
    (X : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n)
    (e : OpenPartialHomeomorph (ComplexVector n × ComplexVector n) (ComplexVector n × ComplexVector n))
    (H : FieldNormalEndpointData h c O B ρ ε X e)
    (q y : M.Carrier) (hq : q ∈ (chartAt (ComplexVector n) c).source)
    (hy : y ∈ (chartAt (ComplexVector n) c).source)
    (hpair : (chartPt c q,chartPt c y) ∈ e.target) :
    fieldNormalBranchCurve c X e q y 0 = q ∧ fieldNormalBranchCurve c X e q y 1 = y ∧
      FieldGeodesicOn h (fieldNormalBranchCurve c X e q y) (Set.Ioo (-ε) (1+ε)) ∧
      Set.MapsTo (fieldNormalBranchCurve c X e q y) (Set.Icc (0 : ℝ) 1) O := by
  rcases H with ⟨hB,hcB,hBsub,hρ,hε,hsource,heq,hX,hinv,hdata,hzero⟩
  let p := e.symm (chartPt c q,chartPt c y)
  have hp : p ∈ e.source := e.map_target hpair
  have Hcoord := (heq hp).symm.trans (e.right_inv hpair)
  have Hfirst := congrArg Prod.fst Hcoord
  have Hlast := congrArg Prod.snd Hcoord
  change p.1 = chartPt c q at Hfirst
  change X p 1 = chartPt c y at Hlast
  have hqinv : chartInv c (chartPt c q) = q :=
    (extChartAt (ComplexModel n) c).left_inv (by simpa only [extChartAt_source] using hq)
  have hyinv : chartInv c (chartPt c y) = y :=
    (extChartAt (ComplexModel n) c).left_inv (by simpa only [extChartAt_source] using hy)
  refine ⟨?_,?_,(hdata p hp).2.2.2.1,(hdata p hp).2.2.2.2.1⟩
  · change chartInv c (X p 0) = q
    rw [(hdata p hp).1,Hfirst,hqinv]
  · change chartInv c (X p 1) = y
    rw [Hlast,hyinv]

theorem fieldNormalBranchCurve_geoChartState
    (h : HermitianField M) (c b : M.Carrier) (O : Set M.Carrier)
    (B : Set (ComplexVector n)) (ρ ε : ℝ)
    (X : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n)
    (e : OpenPartialHomeomorph (ComplexVector n × ComplexVector n) (ComplexVector n × ComplexVector n))
    (H : FieldNormalEndpointData h c O B ρ ε X e)
    (q y : M.Carrier) (hpair : (chartPt c q,chartPt c y) ∈ e.target)
    (u : ℝ) (hu : u ∈ Set.Ioo (-ε) (1+ε))
    (hb : fieldNormalBranchCurve c X e q y u ∈ (extChartAt (ComplexModel n) b).source) :
    geoChartState (fieldNormalBranchCurve c X e q y) b u =
      realTangentChartChange c b (normalFamilyPhase X (e.symm (chartPt c q,chartPt c y)) u) := by
  rcases H with ⟨hB,hcB,hBsub,hρ,hε,hsource,heq,hX,hinv,hdata,hzero⟩
  let p := e.symm (chartPt c q,chartPt c y)
  have hp : p ∈ e.source := e.map_target hpair
  have htarget : ∀ p ∈ e.source, ∀ u ∈ Set.Ioo (-ε) (1+ε), X p u ∈ chartTarget c :=
    fun p hp => (hdata p hp).2.2.1
  have hgeo : ∀ p ∈ e.source,
      FieldGeodesicOn h (fun u => chartInv c (X p u)) (Set.Ioo (-ε) (1+ε)) :=
    fun p hp => (hdata p hp).2.2.2.1
  have Hsol := normalFamilyPhase_is_solution h c X e.open_source isOpen_Ioo hX htarget hgeo p hp u hu
  exact geoChartState_chart_solution_eq h c b (normalFamilyPhase X p) u (htarget p hp u hu) hb Hsol

theorem fieldNormalBranchCurve_initial_state
    (h : HermitianField M) (c b : M.Carrier) (O : Set M.Carrier)
    (B : Set (ComplexVector n)) (ρ ε : ℝ)
    (X : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n)
    (e : OpenPartialHomeomorph (ComplexVector n × ComplexVector n) (ComplexVector n × ComplexVector n))
    (H : FieldNormalEndpointData h c O B ρ ε X e)
    (q y : M.Carrier) (hq : q ∈ (chartAt (ComplexVector n) c).source)
    (hy : y ∈ (chartAt (ComplexVector n) c).source)
    (hpair : (chartPt c q,chartPt c y) ∈ e.target)
    (hb : q ∈ (chartAt (ComplexVector n) b).source) :
    geoChartState (fieldNormalBranchCurve c X e q y) b 0 =
      (chartPt b q,fderiv ℝ (realChartChange c b) (chartPt c q) (e.symm (chartPt c q,chartPt c y)).2) := by
  have Hcurve := fieldNormalBranchCurve_data h c O B ρ ε X e H q y hq hy hpair
  rcases H with ⟨hB,hcB,hBsub,hρ,hε,hsource,heq,hX,hinv,hdata,hzero⟩
  let p := e.symm (chartPt c q,chartPt c y)
  have hp : p ∈ e.source := e.map_target hpair
  have h₀ : (0 : ℝ) ∈ Set.Ioo (-ε) (1+ε) := by constructor <;> linarith
  have Hfull : FieldNormalEndpointData h c O B ρ ε X e :=
    ⟨hB,hcB,hBsub,hρ,hε,hsource,heq,hX,hinv,hdata,hzero⟩
  have Hstate := fieldNormalBranchCurve_geoChartState h c b O B ρ ε X e Hfull q y hpair 0 h₀
    (by rw [Hcurve.1]; simpa only [extChartAt_source] using hb)
  have Hinit := normalFamilyPhase_initial X e.open_source isOpen_Ioo h₀ hX
    (fun p hp => ⟨(hdata p hp).1,(hdata p hp).2.1⟩) p hp
  have Hcoord := (heq hp).symm.trans (e.right_inv hpair)
  have Hfirst := congrArg Prod.fst Hcoord
  change p.1 = chartPt c q at Hfirst
  have hinv : chartInv c (chartPt c q) = q :=
    (extChartAt (ComplexModel n) c).left_inv (by simpa only [extChartAt_source] using hq)
  change geoChartState (fieldNormalBranchCurve c X e q y) b 0 = realTangentChartChange c b (normalFamilyPhase X p 0) at Hstate
  rw [Hinit] at Hstate
  change geoChartState (fieldNormalBranchCurve c X e q y) b 0 =
    (realChartChange c b p.1,fderiv ℝ (realChartChange c b) p.1 p.2) at Hstate
  rw [Hfirst] at Hstate
  simpa only [realChartChange,hinv] using Hstate

theorem fieldNormalBranchCurve_terminal_state
    (h : HermitianField M) (c b : M.Carrier) (O : Set M.Carrier)
    (B : Set (ComplexVector n)) (ρ ε : ℝ)
    (X : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n)
    (e : OpenPartialHomeomorph (ComplexVector n × ComplexVector n) (ComplexVector n × ComplexVector n))
    (H : FieldNormalEndpointData h c O B ρ ε X e)
    (q y : M.Carrier) (hq : q ∈ (chartAt (ComplexVector n) c).source)
    (hy : y ∈ (chartAt (ComplexVector n) c).source)
    (hpair : (chartPt c q,chartPt c y) ∈ e.target)
    (hb : y ∈ (chartAt (ComplexVector n) b).source) :
    geoChartState (fieldNormalBranchCurve c X e q y) b 1 =
      (chartPt b y,fderiv ℝ (realChartChange c b) (chartPt c y)
        (normalFamilyPhase X (e.symm (chartPt c q,chartPt c y)) 1).2) := by
  have Hcurve := fieldNormalBranchCurve_data h c O B ρ ε X e H q y hq hy hpair
  rcases H with ⟨hB,hcB,hBsub,hρ,hε,hsource,heq,hX,hinv,hdata,hzero⟩
  let p := e.symm (chartPt c q,chartPt c y)
  have hp : p ∈ e.source := e.map_target hpair
  have h₁ : (1 : ℝ) ∈ Set.Ioo (-ε) (1+ε) := by constructor <;> linarith
  have Hfull : FieldNormalEndpointData h c O B ρ ε X e :=
    ⟨hB,hcB,hBsub,hρ,hε,hsource,heq,hX,hinv,hdata,hzero⟩
  have Hstate := fieldNormalBranchCurve_geoChartState h c b O B ρ ε X e Hfull q y hpair 1 h₁
    (by rw [Hcurve.2.1]; simpa only [extChartAt_source] using hb)
  have Hcoord := (heq hp).symm.trans (e.right_inv hpair)
  have Hlast := congrArg Prod.snd Hcoord
  change X p 1 = chartPt c y at Hlast
  have hinv : chartInv c (chartPt c y) = y :=
    (extChartAt (ComplexModel n) c).left_inv (by simpa only [extChartAt_source] using hy)
  change geoChartState (fieldNormalBranchCurve c X e q y) b 1 =
    (realChartChange c b (X p 1),fderiv ℝ (realChartChange c b) (X p 1) (normalFamilyPhase X p 1).2) at Hstate
  rw [Hlast] at Hstate
  simpa only [realChartChange,hinv] using Hstate

end Yau.LeafProofs.L23Aux
