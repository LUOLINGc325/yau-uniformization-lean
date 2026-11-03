import Yau.Geometry.Basic

noncomputable section

namespace Yau.LeafProofs.L17HermitianMatrixAssemblyAux

/-- Pull back a concrete Hermitian inner product along an injective complex linear map. -/
def pullbackHermitianInnerProduct {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (h : HermitianInnerProduct W)
    (L : V →ₗ[ℂ] W) (hL : Function.Injective L) : HermitianInnerProduct V where
  toFun u v := h.toFun (L u) (L v)
  map_add_left u v w := by rw [map_add, h.map_add_left]
  map_smul_left c u v := by rw [map_smul, h.map_smul_left]
  map_add_right u v w := by rw [map_add, h.map_add_right]
  map_smul_right c u v := by rw [map_smul, h.map_smul_right]
  conjugate_symmetric u v := h.conjugate_symmetric _ _
  self_adjoint u := h.self_adjoint _
  positive_definite u := by
    refine ⟨(h.positive_definite (L u)).1, ?_⟩
    rw [(h.positive_definite (L u)).2]
    exact ⟨fun hu => hL (hu.trans (map_zero L).symm), fun hu => by rw [hu, map_zero]⟩

theorem pullbackHermitianInnerProduct_apply {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (h : HermitianInnerProduct W)
    (L : V →ₗ[ℂ] W) (hL : Function.Injective L) (u v : V) :
    (pullbackHermitianInnerProduct h L hL).toFun u v = h.toFun (L u) (L v) := rfl

/-- The actual pairings determine the concrete Hermitian inner product. -/
theorem hermitianInnerProduct_ext {V : Type*} [AddCommGroup V] [Module ℂ V]
    {h k : HermitianInnerProduct V} (heq : ∀ u v, h.toFun u v = k.toFun u v) : h = k := by
  cases h with
  | mk f _ _ _ _ _ _ _ =>
    cases k with
    | mk g _ _ _ _ _ _ _ =>
      have : f = g := funext fun u => funext fun v => heq u v
      subst g
      rfl

end Yau.LeafProofs.L17HermitianMatrixAssemblyAux
