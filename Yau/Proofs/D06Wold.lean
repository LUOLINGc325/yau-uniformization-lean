import Yau.Proofs.D06Elementary

/-! The pure-isometry decomposition used by the paper's weighted Hardy-space
construction. The proof is internal Hilbert-space geometry. -/

noncomputable section
namespace Yau.NodeProofs.D06Aux

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def wanderingOrbitSubmodule (S : E →ₗᵢ[ℂ] E) : Submodule ℂ E :=
  ⨆ k : ℕ, (S.rangeᗮ).map (S ^ k).toLinearMap

omit [CompleteSpace E] in
theorem wanderingOrbit_mem (S : E →ₗᵢ[ℂ] E) (k : ℕ) (w : E)
    (hw : w ∈ S.rangeᗮ) : (S ^ k) w ∈ wanderingOrbitSubmodule S := by
  apply (le_iSup (fun k : ℕ => (S.rangeᗮ).map (S ^ k).toLinearMap) k)
  exact ⟨w, hw, rfl⟩

theorem wanderingOrbit_orthogonal_preimage (S : E →ₗᵢ[ℂ] E) (x : E)
    (hx : x ∈ (wanderingOrbitSubmodule S)ᗮ) :
    ∃ y : E, S y = x ∧ y ∈ (wanderingOrbitSubmodule S)ᗮ := by
  have hclosed : IsClosed (S.range : Set E) := S.isometry.isClosedEmbedding.isClosed_range
  let : CompleteSpace S.range := hclosed.completeSpace_coe
  have hxW : x ∈ (S.rangeᗮ)ᗮ := by
    intro w hw
    apply hx w
    simpa only [pow_zero, LinearIsometry.coe_one, id_eq] using wanderingOrbit_mem S 0 w hw
  rw [Submodule.orthogonal_orthogonal] at hxW
  obtain ⟨y, hy⟩ := hxW
  refine ⟨y, hy, ?_⟩
  rw [wanderingOrbitSubmodule, ← Submodule.iInf_orthogonal]
  apply (Submodule.mem_iInf _).mpr
  intro k v hv
  obtain ⟨w, hw, rfl⟩ := hv
  have h := hx ((S ^ (k + 1)) w) (wanderingOrbit_mem S (k + 1) w hw)
  rw [pow_succ', LinearIsometry.coe_mul, Function.comp_apply, ← hy] at h
  change inner ℂ (S ((S ^ k) w)) (S y) = 0 at h
  rw [LinearIsometry.inner_map_map] at h
  exact h

/-- A pure isometry is generated densely by all shifts of the orthogonal
complement of its range. This is the basis-completeness step in D06. -/
theorem wanderingOrbit_dense_of_pure (S : E →ₗᵢ[ℂ] E)
    (hpure : (⨅ k : ℕ, (S ^ k).range) = ⊥) :
    (wanderingOrbitSubmodule S).topologicalClosure = ⊤ := by
  have htail : ∀ k : ℕ, ∀ x ∈ (wanderingOrbitSubmodule S)ᗮ, x ∈ (S ^ k).range := by
    intro k
    induction k with
    | zero =>
        intro x _
        exact ⟨x, rfl⟩
    | succ k ih =>
        intro x hx
        obtain ⟨y, hy, hyorth⟩ := wanderingOrbit_orthogonal_preimage S x hx
        obtain ⟨z, hz⟩ := ih y hyorth
        refine ⟨z, ?_⟩
        rw [pow_succ']
        change S ((S ^ k) z) = x
        exact (congrArg S hz).trans hy
  rw [Submodule.topologicalClosure_eq_top_iff]
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  have hxAll : x ∈ ⨅ k : ℕ, (S ^ k).range := (Submodule.mem_iInf _).mpr fun k => htail k x hx
  rwa [hpure, Submodule.mem_bot] at hxAll

end Yau.NodeProofs.D06Aux
