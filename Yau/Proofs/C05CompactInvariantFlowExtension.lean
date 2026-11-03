import Yau.Proofs.C05CompactInvariantFlowCompact

/-! Forward continuation inside a compact invariant set, retaining the same
fixed negative-time interval at the original initial point. -/
noncomputable section
open scoped Manifold Topology
open Set Filter Function
namespace Yau.Proofs.C05CompactInvariantFlowAux
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [BoundarylessManifold I M] [T2Space M]

 theorem exists_forward_horizons_of_uniform_local_invariant
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ,E)) 1 (fun x => (⟨x,v x⟩ : TangentBundle I M)))
    (K : Set M) {ε : ℝ} (hε : 0 < ε)
    (hloc : ∀ x ∈ K, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ioo (-ε) ε))
    (hinv : ∀ (γ : ℝ → M) (δ : ℝ), 0 < δ → γ 0 ∈ K →
      IsMIntegralCurveOn γ v (Ioo (-δ) δ) → ∀ t ∈ Ico (0:ℝ) δ, γ t ∈ K)
    (x : M) (hx : x ∈ K) :
    ∀ a : ℝ, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ioo (-ε) a) ∧
      ∀ t ∈ Ico (0:ℝ) a, γ t ∈ K := by
  classical
  let S : Set ℝ := {a | ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ioo (-ε) a) ∧
    ∀ t ∈ Ico (0:ℝ) a, γ t ∈ K}
  obtain ⟨γ₀,hγ₀0,hγ₀⟩ := hloc x hx
  have hseed : ε ∈ S := ⟨γ₀,hγ₀0,hγ₀,hinv γ₀ ε hε (by simpa only [hγ₀0] using hx) hγ₀⟩
  have hunbdd : ¬ BddAbove S := by
    intro hbdd
    let asup := sSup S
    have hεsup : ε ≤ asup := le_csSup hbdd hseed
    obtain ⟨a,ha,hlt⟩ := Real.add_neg_lt_sSup (⟨ε,hseed⟩ : S.Nonempty)
      (ε := -(ε/2)) (by linarith)
    change asup-ε/2 < a at hlt
    obtain ⟨γ,hγ0,hγ,hγK⟩ := ha
    let τ := asup-ε/2
    have hτ0 : 0 < τ := by dsimp only [τ]; linarith
    have hτa : τ < a := hlt
    have hτK : γ τ ∈ K := hγK τ ⟨hτ0.le,hτa⟩
    obtain ⟨η,hη0,hη⟩ := hloc (γ τ) hτK
    have hηK := hinv η ε hε (by simpa only [hη0] using hτK) hη
    rw [← isMIntegralCurveOn_comp_sub (dt := τ)] at hη
    set β := η ∘ (·-τ) with hβdef
    change IsMIntegralCurveOn β v _ at hη
    simp_rw [Set.mem_Ioo,lt_sub_iff_add_lt,sub_lt_iff_lt_add,← Set.mem_Ioo] at hη
    have hβ0 : β τ = γ τ := by simp only [hβdef,Function.comp_apply,sub_self,hη0]
    let γext : ℝ → M := piecewise (Ioo (-ε) a) γ β
    have hγext0 : γext 0 = x := by
      dsimp only [γext]
      rw [piecewise,ite_eq_left ⟨by linarith,by linarith⟩,hγ0]
    have hγext : IsMIntegralCurveOn γext v (Ioo (-ε) (asup+ε/2)) := by
      apply (isMIntegralCurveOn_piecewise (t₀ := τ) hv hγ hη
        ⟨⟨by linarith,hτa⟩,⟨by linarith,by linarith⟩⟩ hβ0.symm).mono
      exact Ioo_subset_Ioo_union_Ioo le_rfl (by linarith) (by dsimp only [τ]; linarith)
    have hγextK : ∀ t ∈ Ico (0:ℝ) (asup+ε/2), γext t ∈ K := by
      intro t ht
      by_cases htold : t ∈ Ioo (-ε) a
      · dsimp only [γext]
        rw [piecewise,ite_eq_left htold]
        exact hγK t ⟨ht.1,htold.2⟩
      · dsimp only [γext]
        rw [piecewise,ite_eq_right htold]
        have hat : a ≤ t := by
          by_contra h
          exact htold ⟨by linarith [ht.1],by linarith⟩
        change η (t-τ) ∈ K
        apply hηK (t-τ)
        constructor
        · linarith
        · dsimp only [τ]
          linarith [ht.2]
    have hsup : asup+ε/2 ≤ asup := le_csSup hbdd ⟨γext,hγext0,hγext,hγextK⟩
    linarith
  rw [not_bddAbove_iff] at hunbdd
  intro a
  obtain ⟨b,⟨γ,hγ0,hγ,hγK⟩,hab⟩ := hunbdd a
  exact ⟨γ,hγ0,hγ.mono (Ioo_subset_Ioo le_rfl hab.le),fun t ht => hγK t ⟨ht.1,ht.2.trans hab⟩⟩

end Yau.Proofs.C05CompactInvariantFlowAux
