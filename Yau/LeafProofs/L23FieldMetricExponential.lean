import Yau.LeafProofs.L23FieldMetricGeodesicUniqueness
import Yau.LeafProofs.L23FieldMetricNormalData
import Yau.LeafProofs.L23FieldMetricParallelFrame

/-! The actual exponential endpoint, defined from genuine unit geodesics and their uniqueness. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux L23LocalDistanceContract
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1000000

def FieldExpEndpoint (h : HermitianField M) (x : M.Carrier)
    (V : TangentSpace 𝓘(ℝ, ComplexVector n) x) (y : M.Carrier) : Prop :=
  ∃ (ε : ℝ) (γ : ℝ → M.Carrier), 0 < ε ∧
    FieldGeodesicOn h γ (Set.Ioo (-ε) (1+ε)) ∧ γ 0 = x ∧ γ 1 = y ∧
    ∀ c : M.Carrier, x ∈ (chartAt (ComplexVector n) c).source →
      geoChartState γ c 0 = (chartPt c x,realTangentCoords c x V)

theorem fieldExpEndpoint_unique (h : HermitianField M) (hh : MetricSmooth h)
    (x : M.Carrier) (V : TangentSpace 𝓘(ℝ, ComplexVector n) x)
    {y z : M.Carrier} (hy : FieldExpEndpoint h x V y) (hz : FieldExpEndpoint h x V z) : y = z := by
  rcases hy with ⟨ε,γ,hε,hγ,hγ0,hγ1,hγphase⟩
  rcases hz with ⟨δ,β,hδ,hβ,hβ0,hβ1,hβphase⟩
  let θ := min ε δ
  have hθ : 0 < θ := lt_min hε hδ
  have hsubγ : Set.Ioo (-θ) (1+θ) ⊆ Set.Ioo (-ε) (1+ε) := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2,min_le_left ε δ]
  have hsubβ : Set.Ioo (-θ) (1+θ) ⊆ Set.Ioo (-δ) (1+δ) := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2,min_le_right ε δ]
  have Hγ : FieldGeodesicOn h γ (Set.Ioo (-θ) (1+θ)) :=
    ⟨hγ.1.mono hsubγ,fun c t ht hc => hγ.2 c t (hsubγ ht) hc⟩
  have Hβ : FieldGeodesicOn h β (Set.Ioo (-θ) (1+θ)) :=
    ⟨hβ.1.mono hsubβ,fun c t ht hc => hβ.2 c t (hsubβ ht) hc⟩
  have H := fieldGeodesics_eqOn_Ioo_of_same_chart_phase h hh γ β Hγ Hβ
    (t₀ := 0) (by constructor <;> linarith) x
    (by rw [hγ0]; exact mem_extChartAt_source _)
    (by rw [hβ0]; exact mem_extChartAt_source _)
    ((hγphase x (mem_chart_source _ _)).trans (hβphase x (mem_chart_source _ _)).symm)
  have H1 := H (x := 1) (by constructor <;> linarith)
  simpa only [hγ1,hβ1] using H1

def fieldExp (h : HermitianField M) (x : M.Carrier)
    (V : TangentSpace 𝓘(ℝ, ComplexVector n) x) : M.Carrier := by
  classical
  exact if H : ∃ y, FieldExpEndpoint h x V y then H.choose else x

theorem fieldExp_eq_of_endpoint (h : HermitianField M) (hh : MetricSmooth h)
    (x : M.Carrier) (V : TangentSpace 𝓘(ℝ, ComplexVector n) x)
    (y : M.Carrier) (hy : FieldExpEndpoint h x V y) : fieldExp h x V = y := by
  have H : ∃ y, FieldExpEndpoint h x V y := ⟨y,hy⟩
  unfold fieldExp
  rw [dif_pos H]
  exact fieldExpEndpoint_unique h hh x V H.choose_spec hy

theorem fieldExpEndpoint_normal_coordinates
    (h : HermitianField M) (hh : MetricSmooth h) (c x : M.Carrier)
    (O : Set M.Carrier) (B : Set (ComplexVector n)) (ρ ε : ℝ)
    (X : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n)
    (e : OpenPartialHomeomorph (ComplexVector n × ComplexVector n) (ComplexVector n × ComplexVector n))
    (H : FieldNormalEndpointData h c O B ρ ε X e)
    (hx : x ∈ (chartAt (ComplexVector n) c).source)
    (V : TangentSpace 𝓘(ℝ, ComplexVector n) x)
    (hp : (chartPt c x,realTangentCoords c x V) ∈ e.source) :
    FieldExpEndpoint h x V (chartInv c (X (chartPt c x,realTangentCoords c x V) 1)) := by
  rcases H with ⟨hB,hcB,hBsub,hρ,hε,hsource,heq,hX,hinv,hdata,hzero⟩
  let p := (chartPt c x,realTangentCoords c x V)
  let γ := fun u => chartInv c (X p u)
  have h0 : (0 : ℝ) ∈ Set.Ioo (-ε) (1+ε) := by constructor <;> linarith
  have htarget : ∀ p ∈ e.source, ∀ u ∈ Set.Ioo (-ε) (1+ε), X p u ∈ chartTarget c :=
    fun p hp => (hdata p hp).2.2.1
  have hγ0 : γ 0 = x := by
    change chartInv c (X p 0) = x
    rw [(hdata p hp).1]
    exact (extChartAt (ComplexModel n) c).left_inv (by simpa only [extChartAt_source] using hx)
  refine ⟨ε,γ,hε,(hdata p hp).2.2.2.1,hγ0,rfl,?_⟩
  intro b hb
  have hγb : γ 0 ∈ (extChartAt (ComplexModel n) b).source := by rw [hγ0]; simpa only [extChartAt_source] using hb
  have Hsol := normalFamilyPhase_is_solution h c X e.open_source isOpen_Ioo hX htarget
    (fun p hp => (hdata p hp).2.2.2.1) p hp 0 h0
  have Hstate := geoChartState_chart_solution_eq h c b (normalFamilyPhase X p) 0 (htarget p hp 0 h0) hγb Hsol
  have Hinitial := normalFamilyPhase_initial X e.open_source isOpen_Ioo h0 hX
    (fun p hp => ⟨(hdata p hp).1,(hdata p hp).2.1⟩) p hp
  have Hγ : geoChartState γ b 0 = realTangentChartChange c b p := by
    change geoChartState γ b 0 = realTangentChartChange c b (normalFamilyPhase X p 0) at Hstate
    rwa [Hinitial] at Hstate
  have Hinv : chartInv c (chartPt c x) = x :=
    (extChartAt (ComplexModel n) c).left_inv (by simpa only [extChartAt_source] using hx)
  change geoChartState γ b 0 =
    (chartPt b (chartInv c (chartPt c x)),fderiv ℝ (realChartChange c b) (chartPt c x) (realTangentCoords c x V)) at Hγ
  rw [Hinv] at Hγ
  rw [← realTangentCoords_comp_realFrameCLM_change c b x hx hb,
    ContinuousLinearMap.comp_apply,realFrameCLM_realTangentCoords c x hx] at Hγ
  exact Hγ

theorem fieldExp_normal_coordinates
    (h : HermitianField M) (hh : MetricSmooth h) (c x : M.Carrier)
    (O : Set M.Carrier) (B : Set (ComplexVector n)) (ρ ε : ℝ)
    (X : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n)
    (e : OpenPartialHomeomorph (ComplexVector n × ComplexVector n) (ComplexVector n × ComplexVector n))
    (H : FieldNormalEndpointData h c O B ρ ε X e)
    (hx : x ∈ (chartAt (ComplexVector n) c).source)
    (V : TangentSpace 𝓘(ℝ, ComplexVector n) x)
    (hp : (chartPt c x,realTangentCoords c x V) ∈ e.source) :
    fieldExp h x V = chartInv c (X (chartPt c x,realTangentCoords c x V) 1) :=
  fieldExp_eq_of_endpoint h hh x V _
    (fieldExpEndpoint_normal_coordinates h hh c x O B ρ ε X e H hx V hp)

end Yau.LeafProofs.L23Aux
