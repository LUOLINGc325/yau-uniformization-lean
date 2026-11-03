import Yau.Proofs.F05JetExtension

/-! The concrete cutoff and three point reflection define an actual linear
map of jet data into ambient functions. No seminorm is imposed on unrestricted
functions; quantitative bounds are supplied separately. -/

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

local instance f05_extLinearDualGroup : NormedAddCommGroup (F05Dual n) := inferInstance
local instance f05_extLinearDualSpace : NormedSpace ℝ (F05Dual n) := inferInstance
local instance f05_extLinearHessianGroup : NormedAddCommGroup (F05Hessian n) := f05_jetHessianGroup
local instance f05_extLinearHessianSpace : NormedSpace ℝ (F05Hessian n) := f05_jetHessianSpace

theorem F05_reflection_add (e : Space n) (v w : Point n → ℝ) :
    halfSpaceSecondOrderExtension e (v+w) =
      halfSpaceSecondOrderExtension e v + halfSpaceSecondOrderExtension e w := by
  funext p
  simp only [halfSpaceSecondOrderExtension,Pi.add_apply]
  split_ifs <;> ring

theorem F05_reflection_smul (e : Space n) (c : ℝ) (v : Point n → ℝ) :
    halfSpaceSecondOrderExtension e (c • v) = c • halfSpaceSecondOrderExtension e v := by
  funext p
  simp only [halfSpaceSecondOrderExtension,Pi.smul_apply,smul_eq_mul]
  split_ifs <;> ring

theorem F05_cutoff_value_add {α : ℝ} {Q : Set (Point n)}
    (φ : Space n → ℝ) (u v : F05JetComponent α Q) :
    F05CutoffJetValue φ (u+v) = F05CutoffJetValue φ u + F05CutoffJetValue φ v := by
  funext p
  change φ p.1 * F05BCFFun (u.1+v.1) p =
    φ p.1 * F05BCFFun u.1 p + φ p.1 * F05BCFFun v.1 p
  rw [F05BCFFun_add,mul_add]

theorem F05_cutoff_value_smul {α : ℝ} {Q : Set (Point n)}
    (φ : Space n → ℝ) (c : ℝ) (u : F05JetComponent α Q) :
    F05CutoffJetValue φ (c • u) = c • F05CutoffJetValue φ u := by
  funext p
  change φ p.1 * F05BCFFun (c • u.1) p = c • (φ p.1 * F05BCFFun u.1 p)
  rw [F05BCFFun_smul]
  simp only [smul_eq_mul]
  ring

def F05LocalExtensionLinear (A : AtlasData M) (i : Fin A.count) (α T : ℝ)
    (φ : Space n → ℝ) : F05JetComponent α (F05Q A i T) →ₗ[ℝ] (Point n → ℝ) where
  toFun := F05LocalJetExtension A i φ
  map_add' u v := by
    cases hν : A.normal i with
    | none => simpa only [F05LocalJetExtension,hν] using F05_cutoff_value_add φ u v
    | some j =>
      simp only [F05LocalJetExtension,hν,F05_cutoff_value_add,F05_reflection_add]
  map_smul' c u := by
    cases hν : A.normal i with
    | none => simpa only [F05LocalJetExtension,hν,RingHom.id_apply] using F05_cutoff_value_smul φ c u
    | some j =>
      simp only [F05LocalJetExtension,hν,F05_cutoff_value_smul,F05_reflection_smul,RingHom.id_apply]

end Yau.Proofs.F05Aux
