import Yau.Proofs.F05CanonicalRealization
import Yau.Proofs.F05FlattenedLaplacian

/-! The computed chart operator on the Banach jet data is the actual
intrinsic parabolic operator of the concrete manifold realization. -/

open Set
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport
variable {n : ℕ} {M : ComplexManifold n}

def F05IntrinsicLinearOperator (c : M.Carrier → ℝ → ℝ) (h : ℝ → HermitianField M)
    (T : ℝ) (w : M.Carrier → ℝ → ℝ) (x : M.Carrier) (t : ℝ) : ℝ :=
  derivWithin (w x) (Icc 0 T) t - c x t * laplacian (h t) (fun y => w y t) x

def F05JetOperator (A : AtlasData M) (c : M.Carrier → ℝ → ℝ) (h : ℝ → HermitianField M)
    (α : ℝ) {T : ℝ} (hT : 0 ≤ T) (u : F05CompatibleJetGraph A α hT)
    (i : Fin A.count) (p : Point n) : ℝ :=
  F05BCFFun (u.val i).val.2.2.2.val.1 p - c (lift A i p.1) p.2 *
    ((∑ a, ∑ b, flatA (h p.2) A i p a b * F05BCFFun (u.val i).val.2.2.1.val.1 p (realVec a) (realVec b)) +
      ∑ a, flatB (h p.2) A i p a * F05BCFFun (u.val i).val.2.1 p (realVec a))

theorem F05_timeD_pull (A : AtlasData M) (i : Fin A.count) (T : ℝ)
    (w : M.Carrier → ℝ → ℝ) {p : Point n} (hp : p.1 ∈ F05D A i) :
    timeD (F05Q A i T) (fun q => w (lift A i q.1) q.2) p =
      derivWithin (w (lift A i p.1)) (Icc 0 T) p.2 := by
  have hFiber : {r | (p.1,r) ∈ F05Q A i T} = Icc 0 T := by
    ext r
    change (p.1 ∈ F05D A i ∧ r ∈ Icc 0 T) ↔ r ∈ Icc 0 T
    exact and_iff_right hp
  unfold timeD
  rw [hFiber]

theorem F05JetOperator_eq_intrinsic {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    (c : M.Carrier → ℝ → ℝ) (h : ℝ → HermitianField M)
    (α : ℝ) {T : ℝ} (hT : 0 < T) (u : F05CompatibleJetGraph A α hT.le)
    (i : Fin A.count) {p : Point n} (hp : p ∈ F05Q A i T) :
    F05JetOperator A c h α hT.le u i p =
      F05IntrinsicLinearOperator c h T (F05CanonicalJetFunction A χ α hT.le u) (lift A i p.1) p.2 := by
  have hReal := F05CanonicalJetFunction_realizes hA hχ α hT u i
  have hC2 := F05CanonicalJetFunction_spatial_C2 hA hχ α hT u i hp.1 hp.2
  have hLap := F05_flattened_laplacian_C2 hA (h p.2) i
    (fun x => F05CanonicalJetFunction A χ α hT.le u x p.2) (F05D_mem_ball hp.1) hC2
  change laplacian (h p.2) (fun x => F05CanonicalJetFunction A χ α hT.le u x p.2) (lift A i p.1) =
    ((∑ a, ∑ b, flatA (h p.2) A i (p.1,0) a b *
      spatialDD (F05CanonicalPull A χ α hT.le u i) p (realVec a) (realVec b)) +
      ∑ a, flatB (h p.2) A i (p.1,0) a * spatialD (F05CanonicalPull A χ α hT.le u i) p (realVec a)) at hLap
  have hA_time : flatA (h p.2) A i (p.1,0) = flatA (h p.2) A i p := rfl
  have hB_time : flatB (h p.2) A i (p.1,0) = flatB (h p.2) A i p := rfl
  rw [hA_time,hB_time,hReal.2.1 hp,hReal.2.2.1 hp] at hLap
  unfold F05JetOperator F05IntrinsicLinearOperator
  rw [← hLap,← hReal.2.2.2 hp]
  congr 1
  exact F05_timeD_pull A i T (F05CanonicalJetFunction A χ α hT.le u) hp.1

theorem F05JetOperator_compatible {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    (c : M.Carrier → ℝ → ℝ) (h : ℝ → HermitianField M)
    (α : ℝ) {T : ℝ} (hT : 0 < T) (u : F05CompatibleJetGraph A α hT.le)
    (p : F05OverlapPoint A T) :
    F05JetOperator A c h α hT.le u p.left p.leftPoint.val =
      F05JetOperator A c h α hT.le u p.right p.rightPoint.val := by
  rw [F05JetOperator_eq_intrinsic hA hχ c h α hT u p.left p.leftPoint.property,
    F05JetOperator_eq_intrinsic hA hχ c h α hT u p.right p.rightPoint.property]
  change F05IntrinsicLinearOperator c h T _ (lift A p.left p.leftCoord.val) p.time.val =
    F05IntrinsicLinearOperator c h T _ (lift A p.right p.rightCoord.val) p.time.val
  rw [p.samePoint]

theorem F05JetOperator_initial (A : AtlasData M) (c : M.Carrier → ℝ → ℝ)
    (h : ℝ → HermitianField M) (α : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (u : F05CompatibleJetGraph A α hT) (i : Fin A.count) (z : Space n) :
    F05JetOperator A c h α hT u i (z,0) = 0 := by
  have hInitial := F05LocalZeroFTCGraph_initial_total A i α hT (u.val i) z
  unfold F05JetOperator
  rw [hInitial.2.1,hInitial.2.2.1,hInitial.2.2.2]
  simp

end Yau.Proofs.F05Aux
