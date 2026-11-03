import Yau.Proofs.C05CompactInvariantFlowChart

noncomputable section
open scoped Manifold Topology
open Set Filter
namespace Yau.Proofs.C05CompactInvariantFlowAux
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [BoundarylessManifold I M]

 theorem exists_uniform_integral_curves_on_compact
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ,E)) 1 (fun x => (⟨x,v x⟩ : TangentBundle I M)))
    (K : Set M) (hK : IsCompact K) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K, ∃ γ : ℝ → M,
      γ 0 = x ∧ IsMIntegralCurveOn γ v (Ioo (-ε) ε) := by
  classical
  have hloc (x : M) := exists_uniform_nearby_integral_curves v x hv.contMDiffAt
  choose e he U hU hcurve using hloc
  obtain ⟨T,hTK,hcover⟩ := hK.elim_nhds_subcover U (fun x _ => hU x)
  have hmin : ∀ S : Finset M, ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ S, ε ≤ e x := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1,zero_lt_one,by simp⟩
    | @insert x S hx ih =>
      obtain ⟨ε,hε,hbound⟩ := ih
      refine ⟨min ε (e x),lt_min hε (he x),?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hbound y hy)
  obtain ⟨ε,hε,hbound⟩ := hmin T
  refine ⟨ε,hε,?_⟩
  intro x hx
  obtain ⟨y,hy,hxy⟩ := mem_iUnion₂.mp (hcover hx)
  obtain ⟨γ,hγ0,hγ⟩ := hcurve y x hxy
  exact ⟨γ,hγ0,hγ.mono (Ioo_subset_Ioo (neg_le_neg (hbound y hy)) (hbound y hy))⟩

end Yau.Proofs.C05CompactInvariantFlowAux
