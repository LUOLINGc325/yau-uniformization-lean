import Yau.Proofs.F05SourceZero

/-! A genuinely Holder, linear family of actual initial-zero scalar functions
has its bounded linear encoding in the original physical source graph. -/

open Set
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

def F05ActualSourceZero {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {α T C : ℝ} (hα : 0 < α) (hT : 0 ≤ T)
    (f : M.Carrier → ℝ → ℝ) (hf : ∀ i, HolderBound α (F05Q A i T) (pull A i f) C)
    (h0 : ∀ x ∈ closure O, f x 0 = 0) : F05SourceZeroGraph A α T :=
  ⟨F05SourceAmbientOfActual hα f hf,F05SourceAmbientOfActual_compatible hα f hf,by
    intro i z hz
    rw [F05SourceAmbientOfActual_eval hα f hf i (z,0) ⟨hz,le_rfl,hT⟩]
    exact h0 _ (F05D_lift_mem_closure hA hz)⟩

theorem F05ActualSourceZero_eval {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {α T C : ℝ} (hα : 0 < α) (hT : 0 ≤ T)
    (f : M.Carrier → ℝ → ℝ) (hf : ∀ i, HolderBound α (F05Q A i T) (pull A i f) C)
    (h0 : ∀ x ∈ closure O, f x 0 = 0) (i : Fin A.count) (p : F05Q A i T) :
    holderGraphFun ((F05ActualSourceZero hA hα hT f hf h0).val i) p.val = pull A i f p.val :=
  F05SourceAmbientOfActual_eval hα f hf i p.val p.property

def F05ActualSourceLinear {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {O : Set M.Carrier} {A : AtlasData M} (hA : GenuineAtlas O A)
    {α C T : ℝ} (hα : 0 < α) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (F : E →ₗ[ℝ] (M.Carrier → ℝ → ℝ))
    (hF : ∀ u i, HolderBound α (F05Q A i T) (pull A i (F u)) (C*‖u‖))
    (h0 : ∀ u x, x ∈ closure O → F u x 0 = 0) : E →L[ℝ] F05SourceZeroGraph A α T := by
  let encode := fun u => F05ActualSourceZero hA hα hT (F u) (hF u) (h0 u)
  have hValue (u : E) (i : Fin A.count) (p : F05Q A i T) :
      holderGraphFun ((encode u).val i) p.val = pull A i (F u) p.val :=
    F05ActualSourceZero_eval hA hα hT (F u) (hF u) (h0 u) i p
  let L : E →ₗ[ℝ] F05SourceZeroGraph A α T :=
    { toFun := encode
      map_add' := by
        intro u v
        apply Subtype.ext
        funext i
        apply holderGraph_ext
        intro p
        change ((encode (u+v)).val i).val.1 p = ((encode u).val i).val.1 p+((encode v).val i).val.1 p
        rw [← holderGraphFun_apply _ p,← holderGraphFun_apply _ p,← holderGraphFun_apply _ p,
          hValue,hValue,hValue,map_add]
        rfl
      map_smul' := by
        intro d u
        apply Subtype.ext
        funext i
        apply holderGraph_ext
        intro p
        change ((encode (d • u)).val i).val.1 p = d*((encode u).val i).val.1 p
        rw [← holderGraphFun_apply _ p,← holderGraphFun_apply _ p,hValue,hValue,map_smul]
        rfl }
  exact L.mkContinuous C (by
    intro u
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC (norm_nonneg u))).mpr
    intro i
    exact holderGraphOfBound_norm_le hα (hF u i))

theorem F05ActualSourceLinear_eval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {O : Set M.Carrier} {A : AtlasData M} (hA : GenuineAtlas O A)
    {α C T : ℝ} (hα : 0 < α) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (F : E →ₗ[ℝ] (M.Carrier → ℝ → ℝ))
    (hF : ∀ u i, HolderBound α (F05Q A i T) (pull A i (F u)) (C*‖u‖))
    (h0 : ∀ u x, x ∈ closure O → F u x 0 = 0) (u : E) (i : Fin A.count) (p : F05Q A i T) :
    holderGraphFun ((F05ActualSourceLinear hA hα hT hC F hF h0 u).val i) p.val = pull A i (F u) p.val :=
  F05ActualSourceZero_eval hA hα hT (F u) (hF u) (h0 u) i p

theorem F05ActualSourceLinear_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {O : Set M.Carrier} {A : AtlasData M} (hA : GenuineAtlas O A)
    {α C T : ℝ} (hα : 0 < α) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (F : E →ₗ[ℝ] (M.Carrier → ℝ → ℝ))
    (hF : ∀ u i, HolderBound α (F05Q A i T) (pull A i (F u)) (C*‖u‖))
    (h0 : ∀ u x, x ∈ closure O → F u x 0 = 0) :
    ‖F05ActualSourceLinear hA hα hT hC F hF h0‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro u
  exact (pi_norm_le_iff_of_nonneg (mul_nonneg hC (norm_nonneg u))).mpr
    (fun i => holderGraphOfBound_norm_le hα (hF u i))

end Yau.Proofs.F05Aux
