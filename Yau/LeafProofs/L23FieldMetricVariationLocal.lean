import Yau.LeafProofs.L23FieldMetricExponential
import Yau.LeafProofs.L23FieldMetricParallelEndpoint

/-! The actual exponential variation has a joint C3 local representation at every zero vector. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux L23LocalDistanceContract
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1000000

def parallelExpVariation (h : HermitianField M) (γ : ℝ → M.Carrier)
    (P : (u : ℝ) → ComplexVector n →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) (γ u))
    (u : ℝ) (v : ComplexVector n) : M.Carrier := fieldExp h (γ u) (u • P u v)

theorem fieldExp_zero (h : HermitianField M) (hh : MetricSmooth h) (x : M.Carrier) :
    fieldExp h x 0 = x := by
  obtain ⟨B,ρ,ε,X,e,H⟩ := exists_fieldNormalEndpointData h hh x Set.univ isOpen_univ (Set.mem_univ _)
  rcases H with ⟨hB,hxB,hBsub,hρ,hε,hsource,heq,hX,hinv,hdata,hzero⟩
  have hp : (chartPt x x,realTangentCoords x x 0) ∈ e.source := by
    rw [hsource,map_zero]
    exact ⟨hxB,Metric.mem_ball_self hρ⟩
  have HE := fieldExp_normal_coordinates h hh x x Set.univ B ρ ε X e
    ⟨hB,hxB,hBsub,hρ,hε,hsource,heq,hX,hinv,hdata,hzero⟩ (mem_chart_source _ _) 0 hp
  rw [map_zero,(hzero _ hxB).1 1 (by constructor <;> linarith)] at HE
  exact HE.trans ((extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x))

theorem parallelExpVariation_zero
    (h : HermitianField M) (hh : MetricSmooth h) (γ : ℝ → M.Carrier)
    (P : (u : ℝ) → ComplexVector n →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) (γ u)) (u : ℝ) :
    parallelExpVariation h γ P u 0 = γ u := by simp only [parallelExpVariation,map_zero,smul_zero,fieldExp_zero h hh]

theorem parallelExpVariation_initial
    (h : HermitianField M) (hh : MetricSmooth h) (γ : ℝ → M.Carrier)
    (P : (u : ℝ) → ComplexVector n →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) (γ u)) (v : ComplexVector n) :
    parallelExpVariation h γ P 0 v = γ 0 := by simp only [parallelExpVariation,zero_smul,fieldExp_zero h hh]

theorem exists_parallelExpVariation_local
    (h : HermitianField M) (hh : MetricSmooth h) (γ : ℝ → M.Carrier)
    (P : (u : ℝ) → ComplexVector n →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) (γ u))
    (I : Set ℝ) (hI : IsOpen I) (HP : IsParallelFrameOn h γ P I)
    (O : Set M.Carrier) (hO : IsOpen O) :
    letI := manifold_realSmooth M
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 3 γ I →
    ∀ t ∈ I, γ t ∈ O →
    ∃ U : Set (ℝ × ComplexVector n), IsOpen U ∧ (t,0) ∈ U ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 𝓘(ℝ, ComplexVector n) 3
        (Function.uncurry (parallelExpVariation h γ P)) U ∧
      Set.MapsTo (Function.uncurry (parallelExpVariation h γ P)) U O := by
  letI := manifold_realSmooth M
  intro hγ t ht htO
  let c := γ t
  obtain ⟨B,ρ,ε,X,e,H⟩ := exists_fieldNormalEndpointData h hh c O hO htO
  rcases H with ⟨hB,hcB,hBsub,hρ,hε,hsource,heq,hX,hinv,hdata,hzero⟩
  have Hfull : FieldNormalEndpointData h c O B ρ ε X e :=
    ⟨hB,hcB,hBsub,hρ,hε,hsource,heq,hX,hinv,hdata,hzero⟩
  let K := I ∩ γ ⁻¹' (chartAt (ComplexVector n) c).source
  have hK : IsOpen K := hγ.continuousOn.isOpen_inter_preimage hI (chartAt (ComplexVector n) c).open_source
  have hcoord := curve_coordinates_contDiffOn_three γ c K hK (hγ.mono (fun u hu => hu.1)) (fun u hu => hu.2)
  have hZ := parallelFrame_coordinates_contDiffOn_three h hh γ P I hI HP c hγ
  let Z := fun u => (realTangentCoords c (γ u)).comp (P u)
  let F : ℝ × ComplexVector n → ComplexVector n × ComplexVector n :=
    fun p => (chartPt c (γ p.1),p.1 • Z p.1 p.2)
  let D := K ×ˢ (Set.univ : Set (ComplexVector n))
  have hD : IsOpen D := hK.prod isOpen_univ
  have HF : ContDiffOn ℝ 3 F D :=
    (hcoord.comp contDiffOn_fst (fun p hp => hp.1)).prodMk
      (contDiffOn_fst.smul ((hZ.comp contDiffOn_fst (fun p hp => hp.1)).clm_apply contDiffOn_snd))
  let U := D ∩ F ⁻¹' e.source
  have hU : IsOpen U := HF.continuousOn.isOpen_inter_preimage hD e.open_source
  have hpoint : (t,(0 : ComplexVector n)) ∈ U := by
    refine ⟨⟨⟨ht,mem_chart_source _ _⟩,Set.mem_univ _⟩,?_⟩
    rw [hsource]
    change (chartPt c (γ t),t • Z t 0) ∈ B ×ˢ Metric.ball 0 ρ
    simp only [map_zero,smul_zero]
    exact ⟨hcB,Metric.mem_ball_self hρ⟩
  have Hrep (p : ℝ × ComplexVector n) (hp : p ∈ U) :
      parallelExpVariation h γ P p.1 p.2 = chartInv c (X (F p) 1) := by
    have HM : realTangentCoords c (γ p.1) (p.1 • P p.1 p.2) = p.1 • Z p.1 p.2 := by simp only [map_smul,Z,ContinuousLinearMap.comp_apply]
    have HN := fieldExp_normal_coordinates h hh c (γ p.1) O B ρ ε X e Hfull hp.1.1.2
      (p.1 • P p.1 p.2) (by rw [HM]; exact hp.2)
    simpa only [parallelExpVariation,HM,F] using HN
  have HXF : ContDiffOn ℝ 3 (fun p => X (F p) 1) U :=
    hX.comp ((HF.mono (fun p hp => hp.1)).prodMk contDiffOn_const)
      (fun p hp => ⟨hp.2,by constructor <;> linarith⟩)
  have Htarget : Set.MapsTo (fun p => X (F p) 1) U (chartTarget c) :=
    fun p hp => (hdata (F p) hp.2).2.2.1 1 (by constructor <;> linarith)
  refine ⟨U,hU,hpoint,?_,?_⟩
  · rw [← modelWithCornersSelf_prod,chartedSpaceSelf_prod]
    exact ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, ComplexVector n)) (n := 3) c).comp
      HXF.contMDiffOn Htarget).congr (fun p hp => Hrep p hp)
  · intro p hp
    change parallelExpVariation h γ P p.1 p.2 ∈ O
    rw [Hrep p hp]
    exact (hdata (F p) hp.2).2.2.2.2.1 (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1)

end Yau.LeafProofs.L23Aux
