import spec.CHAIN.CONTRACTS
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! A complex unitary initial frame for the actual Hermitian tangent form.
Only the standard finite-dimensional orthonormal-basis construction is used. -/

noncomputable section
open scoped InnerProductSpace Manifold
namespace Yau.Blueprint.C02Proof

theorem exists_hermitianUnitaryEquiv {V : Type*} [AddCommGroup V] [Module ℂ V]
    {n : ℕ} (h : HermitianInnerProduct V) (b : Module.Basis (Fin n) ℂ V) :
    ∃ U : ComplexVector n ≃ₗ[ℂ] V,
      ∀ u v, h.toFun (U u) (U v) = ⟪u, v⟫_ℂ := by
  let core : InnerProductSpace.Core ℂ V :=
    { inner := h.toFun
      conj_inner_symm := fun u v => (h.conjugate_symmetric u v).symm
      re_inner_nonneg := fun u => (h.positive_definite u).1
      add_left := h.map_add_left
      smul_left := fun u v c => h.map_smul_left c u v
      definite := fun u hu => (h.positive_definite u).2.mp (by rw [hu]; rfl) }
  letI : InnerProductSpace.Core ℂ V := core
  letI : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ V :=
    InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ V)
  letI : FiniteDimensional ℂ V := b.finiteDimensional_of_finite
  have hdim : Module.finrank ℂ V = n := by simpa using Module.finrank_eq_card_basis b
  let c : OrthonormalBasis (Fin n) ℂ V :=
    (stdOrthonormalBasis ℂ V).reindex (finCongr hdim)
  refine ⟨c.repr.symm.toLinearEquiv, ?_⟩
  intro u v
  change ⟪c.repr.symm u, c.repr.symm v⟫_ℂ = ⟪u, v⟫_ℂ
  exact c.repr.symm.inner_map_map u v

theorem exists_unitaryTangentFrame {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (p : M.Carrier) :
    ∃ U : ComplexVector n ≃ₗ[ℂ] TangentVector M p,
      ∀ u v, (h p).toFun (U u) (U v) = ⟪u, v⟫_ℂ := by
  let b : Module.Basis (Fin n) ℂ (TangentVector M p) :=
    (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.map
      (tangentSpaceCastModel (ComplexModel n) p).symm.toLinearEquiv
  exact exists_hermitianUnitaryEquiv (h p) b

theorem unitaryTangentFrame_normSq {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (h p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) (u : ComplexVector n) :
    hermitianNormSq (h p) (U u) = ‖u‖ ^ 2 := by
  rw [hermitianNormSq, hU]
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) u).symm

end Yau.Blueprint.C02Proof
