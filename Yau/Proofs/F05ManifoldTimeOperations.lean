import Yau.Proofs.F05TimeCutoffHolder
import Yau.Proofs.F05RelativeFullJetHolder

/-! Positive-time translation and a fixed time cutoff act on actual
manifold functions and their complete chart jets. The cutoff creates the
genuine homogeneous initial value and time jet required by the FTC graph. -/

open Set
open scoped ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

def F05ManifoldTimeShift (s : ℝ) (w : M.Carrier → ℝ → ℝ) : M.Carrier → ℝ → ℝ :=
  fun x t => w x (t+s)

theorem F05_manifold_time_shift_pull (A : AtlasData M) (i : Fin A.count)
    (s : ℝ) (w : M.Carrier → ℝ → ℝ) :
    pull A i (F05ManifoldTimeShift s w) = F05TimeAffine 1 s (pull A i w) := by
  funext z
  simp only [pull,F05ManifoldTimeShift,F05TimeAffine,F05TimeAffinePoint,one_mul]

theorem F05_manifold_time_shift_jets (A : AtlasData M) {O : Set M.Carrier}
    {l r T s α C : ℝ} (hT : 0 < T)
    (hMap : MapsTo (fun t : ℝ => t+s) (Icc 0 T) (Icc l r))
    (w : M.Carrier → ℝ → ℝ)
    (hC2 : ∀ i, C2 (cylinder (F05D A i) l r) (pull A i w))
    (hTuple : ∀ i, HolderBound α (cylinder (F05D A i) l r)
      (fun z => ((pull A i w z,spatialD (pull A i w) z),
        (spatialDD (pull A i w) z,timeD (cylinder (F05D A i) l r) (pull A i w) z))) C)
    (hBoundary : ∀ x ∈ frontier O, ∀ t ∈ Icc l r, w x t = 0) :
    (∀ i, C2 (F05Q A i T) (pull A i (F05ManifoldTimeShift s w))) ∧
    (∀ i, HolderBound α (F05Q A i T)
      (fun z => ((pull A i (F05ManifoldTimeShift s w) z,
          spatialD (pull A i (F05ManifoldTimeShift s w)) z),
        (spatialDD (pull A i (F05ManifoldTimeShift s w)) z,
          timeD (F05Q A i T) (pull A i (F05ManifoldTimeShift s w)) z))) (2*C)) ∧
    (∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, F05ManifoldTimeShift s w x t = 0) := by
  have hMap1 : MapsTo (fun t : ℝ => 1*t+s) (Icc 0 T) (Icc l r) := by
    simpa only [one_mul] using hMap
  refine ⟨?_,?_,?_⟩
  · intro i
    rw [F05_manifold_time_shift_pull]
    exact F05_c2_timeAffine hT hMap1 (hC2 i)
  · intro i
    rw [F05_manifold_time_shift_pull]
    exact F05_full_jet_holder_time_shift hT hMap (hC2 i) (hTuple i)
  · intro x hx t ht
    exact hBoundary x hx (t+s) (hMap ht)

def F05ManifoldTimeCutoff (θ : ℝ → ℝ) (w : M.Carrier → ℝ → ℝ) :
    M.Carrier → ℝ → ℝ := fun x t => θ t*w x t

theorem F05_manifold_time_cutoff_jets (A : AtlasData M) {O : Set M.Carrier}
    {T α E C : ℝ} (hT : 0 < T) (w : M.Carrier → ℝ → ℝ)
    (hC2 : ∀ i, C2 (F05Q A i T) (pull A i w))
    (hTuple : ∀ i, HolderBound α (F05Q A i T)
      (fun z => ((pull A i w z,spatialD (pull A i w) z),
        (spatialDD (pull A i w) z,timeD (F05Q A i T) (pull A i w) z))) C)
    (θ : ℝ → ℝ) (hθ : ContDiff ℝ 1 θ)
    (hθVal : HolderBound α (cylinder (n := n) univ 0 T) (fun z => θ z.2) E)
    (hθDer : HolderBound α (cylinder (n := n) univ 0 T) (fun z => deriv θ z.2) E)
    (hθZero : θ 0 = 0) (hθJetZero : deriv θ 0 = 0)
    (hBoundary : ∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, w x t = 0) :
    (∀ i, C2 (F05Q A i T) (pull A i (F05ManifoldTimeCutoff θ w))) ∧
    (∀ i, HolderBound α (F05Q A i T)
      (fun z => ((pull A i (F05ManifoldTimeCutoff θ w) z,
          spatialD (pull A i (F05ManifoldTimeCutoff θ w)) z),
        (spatialDD (pull A i (F05ManifoldTimeCutoff θ w)) z,
          timeD (F05Q A i T) (pull A i (F05ManifoldTimeCutoff θ w)) z))) (4*E*C)) ∧
    (∀ x, F05ManifoldTimeCutoff θ w x 0 = 0) ∧
    (∀ i z, z ∈ F05D A i →
      timeD (F05Q A i T) (pull A i (F05ManifoldTimeCutoff θ w)) (z,0) = 0) ∧
    (∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, F05ManifoldTimeCutoff θ w x t = 0) := by
  have hSub (i : Fin A.count) : F05Q A i T ⊆ cylinder univ 0 T := fun z hz => ⟨mem_univ _,hz.2⟩
  have hCut (i : Fin A.count) := F05_time_cutoff_full_holder hT (hC2 i) θ hθ
    (holderBound_mono hθVal (hSub i)) (holderBound_mono hθDer (hSub i))
    (holderBound_fst (hTuple i)) (holderBound_fst (holderBound_snd (hTuple i)))
    (holderBound_snd (holderBound_snd (hTuple i)))
  refine ⟨fun i => (hCut i).1,fun i => (hCut i).2,?_,?_,?_⟩
  · intro x
    simp only [F05ManifoldTimeCutoff,hθZero,zero_mul]
  · intro i z hz
    exact (F05_time_cutoff_zero_initial hT (hC2 i) θ hθ hθZero hθJetZero z hz).2
  · intro x hx t ht
    simp only [F05ManifoldTimeCutoff,hBoundary x hx t ht,mul_zero]

end Yau.Proofs.F05Aux
