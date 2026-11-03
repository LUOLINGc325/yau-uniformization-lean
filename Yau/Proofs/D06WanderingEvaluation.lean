import Yau.Proofs.D06WoldBasis

/-! The wandering space has the dimension of the zeroth-coefficient quotient. -/

noncomputable section
namespace Yau.NodeProofs.D06Aux

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [AddCommGroup F] [Module ℂ F]

def wanderingEvaluation (S : E →ₗᵢ[ℂ] E) (C : E →ₗ[ℂ] F) : S.rangeᗮ →ₗ[ℂ] F :=
  C.comp (S.rangeᗮ).subtype

theorem wanderingEvaluation_bijective (S : E →ₗᵢ[ℂ] E) (C : E →ₗ[ℂ] F)
    (hker : C.ker = S.range) (hsurj : Function.Surjective C) :
    Function.Bijective (wanderingEvaluation S C) := by
  constructor
  · intro a b hab
    change C (a : E) = C (b : E) at hab
    have hz : (a : E) - (b : E) ∈ S.range := by
      have hk : (a : E) - (b : E) ∈ C.ker := by
        change C ((a : E) - (b : E)) = 0
        rw [map_sub, hab, sub_self]
      exact Eq.mp (congrArg (fun K : Submodule ℂ E => (a : E) - (b : E) ∈ K) hker) hk
    have hw := (S.rangeᗮ).sub_mem a.property b.property
    have heq : (a : E) - (b : E) = 0 := inner_self_eq_zero.mp (hw _ hz)
    apply Subtype.ext
    exact sub_eq_zero.mp heq
  · intro v
    obtain ⟨x, hx⟩ := hsurj v
    have hclosed : IsClosed (S.range : Set E) := S.isometry.isClosedEmbedding.isClosed_range
    let : CompleteSpace S.range := hclosed.completeSpace_coe
    obtain ⟨s, hs, w, hw, hsw⟩ := S.range.exists_add_mem_mem_orthogonal x
    refine ⟨⟨w, hw⟩, ?_⟩
    change C w = v
    have hCs : C s = 0 := by
      change s ∈ C.ker
      rwa [hker]
    rw [hsw, map_add, hCs, zero_add] at hx
    exact hx

def wanderingEvaluationEquiv (S : E →ₗᵢ[ℂ] E) (C : E →ₗ[ℂ] F)
    (hker : C.ker = S.range) (hsurj : Function.Surjective C) : S.rangeᗮ ≃ₗ[ℂ] F :=
  LinearEquiv.ofBijective (wanderingEvaluation S C) (wanderingEvaluation_bijective S C hker hsurj)

end Yau.NodeProofs.D06Aux
