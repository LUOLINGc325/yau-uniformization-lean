import Yau.Proofs.F01SublevelTopology

/-! The open-sublevel inclusion is an actual holomorphic immersion. The
restricted metric is pulled back by its native manifold derivative. -/
open Set TopologicalSpace
open scoped Manifold ContDiff
noncomputable section
namespace Yau.NodeProofs.F01Aux
open Yau

variable {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

def pullbackInnerProduct (h : HermitianInnerProduct W) (A : V →ₗ[ℂ] W)
    (hA : Function.Injective A) : HermitianInnerProduct V where
  toFun u v := h.toFun (A u) (A v)
  map_add_left u₁ u₂ v := by rw [map_add, h.map_add_left]
  map_smul_left a u v := by rw [map_smul, h.map_smul_left]
  map_add_right u v₁ v₂ := by rw [map_add, h.map_add_right]
  map_smul_right a u v := by rw [map_smul, h.map_smul_right]
  conjugate_symmetric u v := h.conjugate_symmetric _ _
  self_adjoint u := h.self_adjoint _
  positive_definite u := by
    refine ⟨(h.positive_definite (A u)).1, ?_⟩
    rw [(h.positive_definite (A u)).2]
    exact ⟨fun hz => hA (by simpa using hz), fun hz => by rw [hz, map_zero]⟩

variable {n : ℕ} (M : ComplexManifold n)
  (S : Opens M.Carrier) (hS : IsConnected (S : Set M.Carrier))

def openInclusion : (openConnectedManifold M S hS).Carrier → M.Carrier := Subtype.val

theorem openInclusion_mdifferentiable :
    MDifferentiable (ComplexModel n) (ComplexModel n) (openInclusion M S hS) := by
  exact (contMDiff_subtype_val (I := ComplexModel n) (n := 1) (U := S)).mdifferentiable
    (by norm_num)

theorem openInclusion_mfderiv_injective (x : (openConnectedManifold M S hS).Carrier) :
    Function.Injective (mfderiv (ComplexModel n) (ComplexModel n) (openInclusion M S hS) x) := by
  exact (Manifold.IsImmersion.of_opens (I := ComplexModel n) (n := 1) S).mfderiv_injective
    (by norm_num) x

/-- The actual metric on the connected open submanifold, with no caller
choice of tangent identification or of a positive Hermitian matrix. -/
def openRestrictedField (h : HermitianField M) :
    HermitianField (openConnectedManifold M S hS) := fun x =>
  pullbackInnerProduct (h x.val)
    (mfderiv (ComplexModel n) (ComplexModel n) (openInclusion M S hS) x).toLinearMap
    (openInclusion_mfderiv_injective M S hS x)

theorem openRestrictedField_value (h : HermitianField M)
    (x : (openConnectedManifold M S hS).Carrier)
    (u v : TangentVector (openConnectedManifold M S hS) x) :
    (openRestrictedField M S hS h x).toFun u v =
      (h x.val).toFun
        (mfderiv (ComplexModel n) (ComplexModel n) (openInclusion M S hS) x u)
        (mfderiv (ComplexModel n) (ComplexModel n) (openInclusion M S hS) x v) := rfl

end Yau.NodeProofs.F01Aux
