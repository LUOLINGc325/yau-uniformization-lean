import Yau.Proofs.F05JetOperatorHolder
import Yau.Proofs.F05JetOperatorLinear
import Yau.Proofs.F05SourceZero

/-! The computed original operator is a genuine bounded linear map between
the actual complete jet and all-initial-zero source spaces. -/

open Set
noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

def F05JetSourceAmbient (A : AtlasData M) (c : M.Carrier → ℝ → ℝ)
    (h : ℝ → HermitianField M) {α C T : ℝ} (hα : 0 < α) (hT : 0 ≤ T)
    (hBound : ∀ u : F05CompatibleJetGraph A α hT, ∀ i : Fin A.count,
      HolderBound α (F05Q A i T) (F05JetOperator A c h α hT u i) (C*‖u‖))
    (u : F05CompatibleJetGraph A α hT) : F05SourceAmbient A α T :=
  fun i => holderGraphOfBound hα (hBound u i)

theorem F05JetSourceAmbient_eval (A : AtlasData M) (c : M.Carrier → ℝ → ℝ)
    (h : ℝ → HermitianField M) {α C T : ℝ} (hα : 0 < α) (hT : 0 ≤ T)
    (hBound : ∀ u : F05CompatibleJetGraph A α hT, ∀ i : Fin A.count,
      HolderBound α (F05Q A i T) (F05JetOperator A c h α hT u i) (C*‖u‖))
    (u : F05CompatibleJetGraph A α hT) (i : Fin A.count) (p : F05Q A i T) :
    holderGraphFun (F05JetSourceAmbient A c h hα hT hBound u i) p.val =
      F05JetOperator A c h α hT u i p.val :=
  holderGraphOfBound_eqOn hα (hBound u i) p.property

def F05JetSourceOfBound {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    (c : M.Carrier → ℝ → ℝ) (h : ℝ → HermitianField M)
    {α C T : ℝ} (hα : 0 < α) (hT : 0 < T)
    (hBound : ∀ u : F05CompatibleJetGraph A α hT.le, ∀ i : Fin A.count,
      HolderBound α (F05Q A i T) (F05JetOperator A c h α hT.le u i) (C*‖u‖))
    (u : F05CompatibleJetGraph A α hT.le) : F05SourceZeroGraph A α T :=
  ⟨F05JetSourceAmbient A c h hα hT.le hBound u, by
    intro i j z w t hz hw ht heq
    rw [F05JetSourceAmbient_eval A c h hα hT.le hBound u i ⟨(z,t),hz,ht⟩,
      F05JetSourceAmbient_eval A c h hα hT.le hBound u j ⟨(w,t),hw,ht⟩]
    exact F05JetOperator_compatible hA hχ c h α hT u ⟨i,j,⟨z,hz⟩,⟨w,hw⟩,⟨t,ht⟩,heq⟩, by
    intro i z hz
    rw [F05JetSourceAmbient_eval A c h hα hT.le hBound u i ⟨(z,0),hz,le_rfl,hT.le⟩]
    exact F05JetOperator_initial A c h α hT.le u i z⟩

def F05JetSourceOperatorOfBound {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    (c : M.Carrier → ℝ → ℝ) (h : ℝ → HermitianField M)
    {α C T : ℝ} (hα : 0 < α) (hT : 0 < T) (hC : 0 ≤ C)
    (hBound : ∀ u : F05CompatibleJetGraph A α hT.le, ∀ i : Fin A.count,
      HolderBound α (F05Q A i T) (F05JetOperator A c h α hT.le u i) (C*‖u‖)) :
    F05CompatibleJetGraph A α hT.le →L[ℝ] F05SourceZeroGraph A α T := by
  let encode := F05JetSourceOfBound hA hχ c h hα hT hBound
  have hValue (u : F05CompatibleJetGraph A α hT.le) (i : Fin A.count) (p : F05Q A i T) :
      holderGraphFun ((encode u).val i) p.val = F05JetOperator A c h α hT.le u i p.val :=
    F05JetSourceAmbient_eval A c h hα hT.le hBound u i p
  let L : F05CompatibleJetGraph A α hT.le →ₗ[ℝ] F05SourceZeroGraph A α T :=
    { toFun := encode
      map_add' := by
        intro u v
        apply Subtype.ext
        funext i
        apply holderGraph_ext
        intro p
        change ((encode (u+v)).val i).val.1 p = ((encode u).val i).val.1 p+((encode v).val i).val.1 p
        rw [← holderGraphFun_apply _ p,← holderGraphFun_apply _ p,← holderGraphFun_apply _ p,
          hValue,hValue,hValue]
        exact F05JetOperator_add A c h α hT.le u v i p
      map_smul' := by
        intro d u
        apply Subtype.ext
        funext i
        apply holderGraph_ext
        intro p
        change ((encode (d • u)).val i).val.1 p = d*((encode u).val i).val.1 p
        rw [← holderGraphFun_apply _ p,← holderGraphFun_apply _ p,hValue,hValue]
        exact F05JetOperator_smul A c h α hT.le d u i p }
  exact L.mkContinuous C (by
    intro u
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC (norm_nonneg u))).mpr
    intro i
    exact holderGraphOfBound_norm_le hα (hBound u i))

theorem F05_bounded_jet_operator {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    (h : ℝ → HermitianField M) (c : M.Carrier → ℝ → ℝ)
    {S : ℝ} (hS : 0 < S) (hh : MetricFamilySmooth h (Icc 0 S))
    (hc : SmoothSpaceTime c (Icc 0 S)) {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ) (hT : 0 < T), T ≤ S → T ≤ 1 →
      ∃ L : F05CompatibleJetGraph A α hT.le →L[ℝ] F05SourceZeroGraph A α T,
        ‖L‖ ≤ C ∧ ∀ u (i : Fin A.count) (p : F05Q A i T),
          holderGraphFun ((L u).val i) p.val = F05JetOperator A c h α hT.le u i p.val := by
  obtain ⟨C,hC,hBound⟩ := F05_jet_operator_holder_uniform hA hχ h c hS hh hc hα hα1
  refine ⟨C,hC,?_⟩
  intro T hT hTS hT1
  let L := F05JetSourceOperatorOfBound hA hχ c h hα hT hC.le (hBound T hT hTS hT1)
  refine ⟨L,?_,?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound L hC.le
    intro u
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC.le (norm_nonneg u))).mpr
    intro i
    exact holderGraphOfBound_norm_le hα (hBound T hT hTS hT1 u i)
  · intro u i p
    exact F05JetSourceAmbient_eval A c h hα hT.le (hBound T hT hTS hT1) u i p

end Yau.Proofs.F05Aux
