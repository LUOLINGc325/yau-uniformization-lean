import Yau.Proofs.F05ActualJetGraph
import Yau.Proofs.F05FTCValueExt

/-! Encoding actual linear families of homogeneous Schauder functions gives
a genuine bounded operator into the original complete compatible jet graph. -/

open Set
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport
variable {n : ℕ} {M : ComplexManifold n}

theorem F05CompatibleJetGraph_ext_values (A : AtlasData M) (α : ℝ) {T : ℝ}
    (hT : 0 < T) {u v : F05CompatibleJetGraph A α hT.le}
    (hValue : ∀ i (p : F05Q A i T), (u.val i).val.1 p = (v.val i).val.1 p) : u = v := by
  apply Subtype.ext
  funext i
  apply Subtype.ext
  let ui : F05LocalFTCGraph A i α hT.le := ⟨(u.val i).val,(u.val i).property.1.1.1⟩
  let vi : F05LocalFTCGraph A i α hT.le := ⟨(v.val i).val,(v.val i).property.1.1.1⟩
  exact congrArg (fun q : F05LocalFTCGraph A i α hT.le => q.val)
    (F05LocalFTCGraph_ext_values A i α hT (u := ui) (v := vi) (hValue i))

def F05ActualJetLinearMap {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {O : Set M.Carrier} {A : AtlasData M} (hA : GenuineAtlas O A)
    {α C T : ℝ} (hα : 0 < α) (hT : 0 < T) (hC : 0 ≤ C)
    (F : Y → M.Carrier → ℝ → ℝ)
    (hF : ∀ f (i : Fin A.count), SchauderBound α (F05Q A i T) (pull A i (F f)) (C*‖f‖))
    (h0 : ∀ f x, x ∈ closure O → F f x 0 = 0)
    (hTime0 : ∀ f (i : Fin A.count) z, z ∈ F05D A i →
      timeD (F05Q A i T) (pull A i (F f)) (z,0) = 0)
    (hBoundary : ∀ f x, x ∈ frontier O → ∀ t ∈ Icc 0 T, F f x t = 0)
    (hAdd : ∀ f g x, x ∈ closure O → ∀ t ∈ Icc 0 T, F (f+g) x t = F f x t+F g x t)
    (hSmul : ∀ (d : ℝ) f x, x ∈ closure O → ∀ t ∈ Icc 0 T, F (d • f) x t = d*F f x t) :
    Y →L[ℝ] F05CompatibleJetGraph A α hT.le := by
  let encode (f : Y) : F05CompatibleJetGraph A α hT.le :=
    F05ActualJetGraph hA hα hT.le (F f) (hF f) (h0 f) (hTime0 f) (hBoundary f)
  have hValue (f : Y) (i : Fin A.count) (p : F05Q A i T) :
      ((encode f).val i).val.1 p = pull A i (F f) p.val := rfl
  let L : Y →ₗ[ℝ] F05CompatibleJetGraph A α hT.le :=
    { toFun := encode
      map_add' := by
        intro f g
        apply F05CompatibleJetGraph_ext_values A α hT
        intro i p
        change ((encode (f+g)).val i).val.1 p = ((encode f).val i).val.1 p+((encode g).val i).val.1 p
        rw [hValue,hValue,hValue]
        exact hAdd f g _ (F05D_lift_mem_closure hA p.property.1) _ p.property.2
      map_smul' := by
        intro d f
        apply F05CompatibleJetGraph_ext_values A α hT
        intro i p
        change ((encode (d • f)).val i).val.1 p = d*((encode f).val i).val.1 p
        rw [hValue,hValue]
        exact hSmul d f _ (F05D_lift_mem_closure hA p.property.1) _ p.property.2 }
  exact L.mkContinuous C (fun f =>
    F05ActualJetGraph_norm_le hA hα hT.le (F f) (hF f) (h0 f) (hTime0 f) (hBoundary f)
      (mul_nonneg hC (norm_nonneg _)))

end Yau.Proofs.F05Aux
