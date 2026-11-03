import Yau.Proofs.D06WanderingEvaluation

/-! A finite-dimensional coefficient quotient produces the exact indexed
wandering orthonormal basis and the corresponding pure-shift Hilbert basis. -/

noncomputable section
namespace Yau.NodeProofs.D06Aux

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {r : ℕ}

def wanderingOrthonormalBasis (S : E →ₗᵢ[ℂ] E)
    (C : E →ₗ[ℂ] EuclideanSpace ℂ (Fin r))
    (hker : C.ker = S.range) (hsurj : Function.Surjective C) :
    OrthonormalBasis (Fin r) ℂ S.rangeᗮ := by
  let e := wanderingEvaluationEquiv S C hker hsurj
  letI : FiniteDimensional ℂ S.rangeᗮ := FiniteDimensional.of_injective e.toLinearMap e.injective
  have hd : Module.finrank ℂ S.rangeᗮ = r :=
    e.finrank_eq.trans (finrank_euclideanSpace_fin (𝕜 := ℂ) (n := r))
  exact (stdOrthonormalBasis ℂ S.rangeᗮ).reindex (finCongr hd)

def pureShiftBasisFromQuotient (S : E →ₗᵢ[ℂ] E)
    (C : E →ₗ[ℂ] EuclideanSpace ℂ (Fin r))
    (hker : C.ker = S.range) (hsurj : Function.Surjective C)
    (hpure : (⨅ k : ℕ, (S ^ k).range) = ⊥) : HilbertBasis (ℕ × Fin r) ℂ E :=
  pureShiftHilbertBasis S (wanderingOrthonormalBasis S C hker hsurj) hpure

end Yau.NodeProofs.D06Aux
