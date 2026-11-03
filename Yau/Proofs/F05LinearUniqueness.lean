import Yau.Proofs.F05ManifoldMaximum
import Yau.Proofs.F05CanonicalContinuity
import Yau.Proofs.F05CanonicalBoundary
import Yau.Proofs.F05CanonicalLinear
import Yau.Proofs.F05ActualJetLinear
import Yau.Proofs.F05SourceZero

/-! Uniqueness for the original operator follows from the actual compact
manifold maximum argument and the concrete realization of the closed jets. -/

open Set
noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_linear_kernel_nonpos {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    (h : ℝ → HermitianField M) (c : M.Carrier → ℝ → ℝ)
    {α T lam upper : ℝ} (hT : 0 < T)
    (hEll : ∀ i, Elliptic (F05Q A i T) (F05FlowPrincipal A i h c) lam upper)
    (L : F05CompatibleJetGraph A α hT.le →L[ℝ] F05SourceZeroGraph A α T)
    (hLValue : ∀ u (i : Fin A.count) (p : F05Q A i T),
      holderGraphFun ((L u).val i) p.val = F05JetOperator A c h α hT.le u i p.val)
    (u : F05CompatibleJetGraph A α hT.le) (hu : L u = 0) :
    ∀ x ∈ closure O, ∀ t ∈ Icc 0 T, F05CanonicalJetFunction A χ α hT.le u x t ≤ 0 := by
  apply F05_manifold_maximum hA h c hT
    (F05CanonicalJetFunction A χ α hT.le u)
    ((F05CanonicalJetFunction_continuousOn hA hχ α hT u).mono
      (prod_mono (subset_univ _) Subset.rfl))
    (fun i => (F05CanonicalJetFunction_realizes hA hχ α hT u i).1) hEll
  · intro x hx
    exact (F05CanonicalJetFunction_initial A χ α hT.le u x).le
  · intro x hx t ht
    exact (F05CanonicalJetFunction_lateral hA hχ α hT.le u hx ht).le
  · intro x hx t ht
    obtain ⟨i,z,hz,heq⟩ := F05_cover hA (subset_closure hx)
    have hp : (z,t) ∈ F05Q A i T := ⟨hz,ht.1.le,ht.2⟩
    have hEq := F05JetOperator_eq_intrinsic hA hχ c h α hT u i hp
    rw [heq] at hEq
    rw [← hEq,← hLValue u i ⟨(z,t),hp⟩,hu]
    change holderGraphFun (0 : holderGraph α (F05Q A i T)) (z,t) ≤ 0
    rw [holderGraphFun_zero]
    exact le_rfl

theorem F05_linear_kernel_zero {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    (h : ℝ → HermitianField M) (c : M.Carrier → ℝ → ℝ)
    {α T lam upper : ℝ} (hT : 0 < T)
    (hEll : ∀ i, Elliptic (F05Q A i T) (F05FlowPrincipal A i h c) lam upper)
    (L : F05CompatibleJetGraph A α hT.le →L[ℝ] F05SourceZeroGraph A α T)
    (hLValue : ∀ u (i : Fin A.count) (p : F05Q A i T),
      holderGraphFun ((L u).val i) p.val = F05JetOperator A c h α hT.le u i p.val)
    (u : F05CompatibleJetGraph A α hT.le) (hu : L u = 0) : u = 0 := by
  have hNonpos := F05_linear_kernel_nonpos hA hχ h c hT hEll L hLValue u hu
  have hNeg : L (-u) = 0 := by rw [map_neg,hu,neg_zero]
  have hNegNonpos := F05_linear_kernel_nonpos hA hχ h c hT hEll L hLValue (-u) hNeg
  have hCanonNeg (x : M.Carrier) (t : ℝ) :
      F05CanonicalJetFunction A χ α hT.le (-u) x t = -F05CanonicalJetFunction A χ α hT.le u x t := by
    simp only [← F05CanonicalJetLinear_apply,map_neg,Pi.neg_apply]
  have hValueZero (x : M.Carrier) (hx : x ∈ closure O) (t : ℝ) (ht : t ∈ Icc 0 T) :
      F05CanonicalJetFunction A χ α hT.le u x t = 0 := by
    have hh := hNegNonpos x hx t ht
    rw [hCanonNeg] at hh
    linarith [hNonpos x hx t ht]
  apply F05CompatibleJetGraph_ext_values A α hT
  intro i p
  have hValue := F05CanonicalJetFunction_value hA hχ α hT.le u i p.property.1 p.property.2
  rw [hValueZero _ (F05D_lift_mem_closure hA p.property.1) _ p.property.2] at hValue
  rw [F05BCFFun_apply (u.val i).val.1 p] at hValue
  exact hValue.symm

theorem F05_linear_operator_injective {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    (h : ℝ → HermitianField M) (c : M.Carrier → ℝ → ℝ)
    {α T lam upper : ℝ} (hT : 0 < T)
    (hEll : ∀ i, Elliptic (F05Q A i T) (F05FlowPrincipal A i h c) lam upper)
    (L : F05CompatibleJetGraph A α hT.le →L[ℝ] F05SourceZeroGraph A α T)
    (hLValue : ∀ u (i : Fin A.count) (p : F05Q A i T),
      holderGraphFun ((L u).val i) p.val = F05JetOperator A c h α hT.le u i p.val) :
    Function.Injective L := by
  intro u v huv
  have hZero : L (u-v) = 0 := by rw [map_sub,huv,sub_self]
  exact sub_eq_zero.mp (F05_linear_kernel_zero hA hχ h c hT hEll L hLValue (u-v) hZero)

end Yau.Proofs.F05Aux
