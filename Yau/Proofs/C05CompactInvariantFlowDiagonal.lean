import Yau.Proofs.C05CompactInvariantFlowExtension

noncomputable section
open scoped Manifold Topology
open Set Filter
namespace Yau.Proofs.C05CompactInvariantFlowAux
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [BoundarylessManifold I M] [T2Space M]

 theorem exists_forward_curve_of_horizons
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ,E)) 1 (fun x => (⟨x,v x⟩ : TangentBundle I M)))
    (K : Set M) {ε : ℝ} (hε : 0 < ε) (x : M)
    (hhor : ∀ a : ℝ, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ioo (-ε) a) ∧
      ∀ t ∈ Ico (0:ℝ) a, γ t ∈ K) :
    ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ioi (-ε)) ∧
      ∀ t, 0 ≤ t → γ t ∈ K := by
  classical
  choose γ hγ0 hγ hγK using hhor
  let Γ : ℝ → M := fun t => γ (|t|+1) t
  have heq (a : ℝ) (ha : 0 < a) : EqOn Γ (γ a) (Ioo (-ε) a) := by
    intro t ht
    let b := |t|+1
    have hb : 0 < b := by dsimp only [b]; positivity
    have htb : t < b := (le_abs_self t).trans_lt (lt_add_one _)
    change γ b t = γ a t
    apply isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
      (t₀ := 0) (a := -ε) (b := min b a) ⟨by linarith,lt_min hb ha⟩ hv
      ((hγ b).mono (Ioo_subset_Ioo le_rfl (min_le_left _ _)))
      ((hγ a).mono (Ioo_subset_Ioo le_rfl (min_le_right _ _)))
      (by rw [hγ0,hγ0])
    exact ⟨ht.1,lt_min htb ht.2⟩
  refine ⟨Γ,hγ0 _,?_,?_⟩
  · intro t ht
    have ht' : t ∈ Ioo (-ε) (|t|+1) := ⟨ht,(le_abs_self t).trans_lt (lt_add_one _)⟩
    apply HasMFDerivAt.hasMFDerivWithinAt
    apply HasMFDerivAt.congr_of_eventuallyEq_abuse (f := γ (|t|+1))
    · exact (hγ (|t|+1) t ht').hasMFDerivAt (Ioo_mem_nhds ht'.1 ht'.2)
    · exact Filter.eventuallyEq_iff_exists_mem.mpr
        ⟨Ioo (-ε) (|t|+1),Ioo_mem_nhds ht'.1 ht'.2,heq (|t|+1) (by positivity)⟩
  · intro t ht
    exact hγK (|t|+1) t ⟨ht,(le_abs_self t).trans_lt (lt_add_one _)⟩

end Yau.Proofs.C05CompactInvariantFlowAux
