import Yau.Proofs.F05CanonicalValue
import Yau.Proofs.F05JetExtensionLinear

/-! The concrete manifold extension is genuinely linear. Its target here is
the ordinary vector space of actual functions, with no artificial function norm. -/

noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport
variable {n : ℕ} {M : ComplexManifold n}

local instance f05_canonLinearDualGroup : NormedAddCommGroup (F05Dual n) := inferInstance
local instance f05_canonLinearDualSpace : NormedSpace ℝ (F05Dual n) := inferInstance
local instance f05_canonLinearHessianGroup : NormedAddCommGroup (F05Hessian n) := f05_jetHessianGroup
local instance f05_canonLinearHessianSpace : NormedSpace ℝ (F05Hessian n) := f05_jetHessianSpace

def F05CompatibleComponent (A : AtlasData M) (α : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (i : Fin A.count) : F05CompatibleJetGraph A α hT →L[ℝ] F05JetComponent α (F05Q A i T) :=
  (F05GlobalComponent A α hT i).comp (F05CompatibleJetGraph A α hT).subtypeL

theorem F05CompatibleComponent_apply (A : AtlasData M) (α : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (i : Fin A.count) (u : F05CompatibleJetGraph A α hT) :
    F05CompatibleComponent A α hT i u = (u.val i).val := rfl

def F05ChartTransferLinear (A : AtlasData M) (i : Fin A.count) (χ : M.Carrier → ℝ) :
    (Point n → ℝ) →ₗ[ℝ] (M.Carrier → ℝ → ℝ) where
  toFun := fun f x t => χ x * f (F05Coord A i x,t)
  map_add' f g := by
    funext x t
    simp only [Pi.add_apply,mul_add]
  map_smul' c f := by
    funext x t
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    ring

def F05CanonicalJetLinear (A : AtlasData M) (χ : Fin A.count → M.Carrier → ℝ)
    (α : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    F05CompatibleJetGraph A α hT →ₗ[ℝ] (M.Carrier → ℝ → ℝ) :=
  ∑ i, (F05ChartTransferLinear A i (χ i)).comp
    ((F05LocalExtensionLinear A i α T (F05InnerPlateau n)).comp
      (F05CompatibleComponent A α hT i).toLinearMap)

theorem F05CanonicalJetLinear_apply (A : AtlasData M) (χ : Fin A.count → M.Carrier → ℝ)
    (α : ℝ) {T : ℝ} (hT : 0 ≤ T) (u : F05CompatibleJetGraph A α hT)
    (x : M.Carrier) (t : ℝ) :
    F05CanonicalJetLinear A χ α hT u x t = F05CanonicalJetFunction A χ α hT u x t := by
  simp only [F05CanonicalJetLinear,LinearMap.sum_apply,Finset.sum_apply,LinearMap.comp_apply]
  change (∑ i,χ i x * F05LocalJetExtension A i (F05InnerPlateau n)
    (F05CompatibleComponent A α hT i u) (F05Coord A i x,t)) = _
  simp only [F05CompatibleComponent_apply]
  rfl

end Yau.Proofs.F05Aux
