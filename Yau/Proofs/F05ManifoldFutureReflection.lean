import Yau.Proofs.F05FutureReflectionHolder
import Yau.Proofs.F05FutureReflectionZeroData
import Yau.Proofs.F05RelativeFullJetHolder

/-! The terminal reflection is one actual manifold function. Its genuine
chart jets retain the common bound and homogeneous physical/initial data.
No nonlinear equation is asserted on the reflected segment. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

def F05ManifoldFutureReflection (τ : ℝ) (w : M.Carrier → ℝ → ℝ) :
    M.Carrier → ℝ → ℝ := fun x t =>
  if t ≤ τ then w x t else 3*w x ((-1)*t+2*τ)-2*w x ((-2)*t+3*τ)

theorem F05_manifold_future_reflection_pull (A : AtlasData M) (i : Fin A.count)
    (τ : ℝ) (w : M.Carrier → ℝ → ℝ) :
    pull A i (F05ManifoldFutureReflection τ w) = F05FutureReflection τ (pull A i w) := rfl

theorem F05_manifold_future_reflection_jets {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {τ T α C : ℝ} (hτ : 0 < τ) (hτT : τ < T)
    (hBack : 0 ≤ 3*τ-2*T) (hα : 0 < α) (w : M.Carrier → ℝ → ℝ)
    (hC2 : ∀ i, C2 (F05Q A i τ) (pull A i w))
    (hTuple : ∀ i, HolderBound α (F05Q A i τ)
      (fun z => ((pull A i w z,spatialD (pull A i w) z),
        (spatialDD (pull A i w) z,timeD (F05Q A i τ) (pull A i w) z))) C)
    (h0 : ∀ x ∈ closure O, w x 0 = 0)
    (hTime0 : ∀ i z, z ∈ F05D A i → timeD (F05Q A i τ) (pull A i w) (z,0) = 0)
    (hBoundary : ∀ x ∈ frontier O, ∀ t ∈ Icc 0 τ, w x t = 0) :
    (∀ i, C2 (F05Q A i T) (pull A i (F05ManifoldFutureReflection τ w))) ∧
    (∀ i, HolderBound α (F05Q A i T)
      (fun z => ((pull A i (F05ManifoldFutureReflection τ w) z,
          spatialD (pull A i (F05ManifoldFutureReflection τ w)) z),
        (spatialDD (pull A i (F05ManifoldFutureReflection τ w)) z,
          timeD (F05Q A i T) (pull A i (F05ManifoldFutureReflection τ w)) z)))
      (C*(38+12*(2:ℝ)^(α/2)))) ∧
    (∀ x ∈ closure O, F05ManifoldFutureReflection τ w x 0 = 0) ∧
    (∀ i z, z ∈ F05D A i →
      timeD (F05Q A i T) (pull A i (F05ManifoldFutureReflection τ w)) (z,0) = 0) ∧
    (∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, F05ManifoldFutureReflection τ w x t = 0) := by
  have hSch i := F05_schauder_of_full_jet_holder (hC2 i) (hTuple i)
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i
    exact (F05_schauder_future_reflection (F05_region_isClosed (A.normal i) 2)
      hτ hτT hBack hα (hSch i)).1.1
  · intro i
    exact F05_future_reflection_full_holder hτ hτT hBack hα (hC2 i)
      (holderBound_fst (hTuple i)) (holderBound_fst (holderBound_snd (hTuple i)))
      (holderBound_snd (holderBound_snd (hTuple i)))
  · intro x hx
    simpa only [F05ManifoldFutureReflection,hτ.le,ite_true] using h0 x hx
  · intro i z hz
    exact (F05_future_reflection_zero_initial hτ hτT hBack (hC2 i)
      (fun z hz => h0 _ (F05D_lift_mem_closure hA hz)) (hTime0 i) z hz).2
  · intro x hx t ht
    obtain ⟨hMap1,hMap2⟩ := F05_future_reflection_time_maps hτT.le hBack
    by_cases htτ : t ≤ τ
    · simpa only [F05ManifoldFutureReflection,htτ,ite_true] using hBoundary x hx t ⟨ht.1,htτ⟩
    · have hRight : t ∈ Icc τ T := ⟨(not_le.mp htτ).le,ht.2⟩
      simp only [F05ManifoldFutureReflection,htτ,ite_false,
        hBoundary x hx _ (hMap1 hRight),hBoundary x hx _ (hMap2 hRight),mul_zero,sub_self]

end Yau.Proofs.F05Aux
