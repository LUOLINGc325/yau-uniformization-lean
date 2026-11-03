import Yau.Proofs.F05FiniteManifoldPatch
import Yau.Proofs.F05SupportedPoint

/-! Actual finite manifold patch sums preserve genuine zero traces and
pointwise linearity on the closed slab, before Banach-space encoding. -/

open Set
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05FiniteManifoldPatch_initial (A : AtlasData M)
    (β : Fin A.count → M.Carrier → ℝ) {v : Fin A.count → Point n → ℝ}
    (h0 : ∀ j z, v j (z,0) = 0) (x : M.Carrier) : F05FiniteManifoldPatch A β v x 0 = 0 := by
  simp only [F05FiniteManifoldPatch,F05ManifoldPatch_initial A _ _ (h0 _),Finset.sum_const_zero]

theorem F05FiniteManifoldPatch_lateral {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (β : Fin A.count → M.Carrier → ℝ)
    (hSupport : ∀ j, tsupport (β j) ⊆ lift A j '' Metric.closedBall 0 (3/4))
    {T : ℝ} {v : Fin A.count → Point n → ℝ}
    (hB : ∀ j z, z ∈ frontier (F05ModelOpen A j) → ∀ t ∈ Icc 0 T, v j (z,t) = 0)
    {x : M.Carrier} (hx : x ∈ frontier O) {t : ℝ} (ht : t ∈ Icc 0 T) :
    F05FiniteManifoldPatch A β v x t = 0 := by
  unfold F05FiniteManifoldPatch
  apply Finset.sum_eq_zero
  intro j hj
  exact F05ManifoldPatch_lateral hA j (hSupport j) (hB j) hx ht

theorem F05FiniteManifoldPatch_initial_time {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (β : Fin A.count → M.Carrier → ℝ)
    (hSupport : ∀ j, tsupport (β j) ⊆ lift A j '' Metric.closedBall 0 (3/4))
    {T : ℝ} (hT : 0 ≤ T) (v : Fin A.count → Point n → ℝ)
    (hC2 : ∀ j i, C2 (F05Q A i T) (pull A i (F05ManifoldPatch A j (β j) (v j))))
    (hTime0 : ∀ j z, z ∈ closure (F05ModelOpen A j) →
      timeD (cylinder (closure (F05ModelOpen A j)) 0 T) (v j) (z,0) = 0)
    (i : Fin A.count) {z : Space n} (hz : z ∈ F05D A i) :
    timeD (F05Q A i T) (pull A i (F05FiniteManifoldPatch A β v)) (z,0) = 0 := by
  have hFiber : {t : ℝ | (z,t) ∈ F05Q A i T} = Icc 0 T := by
    ext t
    change (z ∈ F05D A i ∧ t ∈ Icc 0 T) ↔ t ∈ Icc 0 T
    exact and_iff_right hz
  have hDiff (j : Fin A.count) :
      DifferentiableWithinAt ℝ (fun t => F05ManifoldPatch A j (β j) (v j) (lift A i z) t) (Icc 0 T) 0 := by
    have hh := (hC2 j i).2.2.2.2.2 (z,0) ⟨hz,le_rfl,hT⟩
    rw [hFiber] at hh
    exact hh
  unfold timeD
  rw [hFiber]
  change derivWithin (fun t => ∑ j,F05ManifoldPatch A j (β j) (v j) (lift A i z) t) (Icc 0 T) 0 = 0
  rw [derivWithin_fun_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin A.count))) => hDiff j)]
  apply Finset.sum_eq_zero
  intro j hj
  have hh := F05ManifoldPatch_initial_time hA i j (hSupport j) (hTime0 j) hz
  unfold timeD at hh
  rw [hFiber] at hh
  exact hh

theorem F05FiniteManifoldPatch_add {Y : Type*} [Add Y]
    (A : AtlasData M) (β : Fin A.count → M.Carrier → ℝ)
    {T : ℝ} (v : Fin A.count → Y → Point n → ℝ)
    (hAdd : ∀ j f g p, p ∈ cylinder univ 0 T → v j (f+g) p = v j f p+v j g p)
    (f g : Y) (x : M.Carrier) {t : ℝ} (ht : t ∈ Icc 0 T) :
    F05FiniteManifoldPatch A β (fun j => v j (f+g)) x t =
      F05FiniteManifoldPatch A β (fun j => v j f) x t+F05FiniteManifoldPatch A β (fun j => v j g) x t := by
  unfold F05FiniteManifoldPatch F05ManifoldPatch
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  dsimp only
  rw [hAdd j f g _ ⟨mem_univ _,ht⟩,mul_add]

theorem F05FiniteManifoldPatch_smul {Y : Type*} [SMul ℝ Y]
    (A : AtlasData M) (β : Fin A.count → M.Carrier → ℝ)
    {T : ℝ} (v : Fin A.count → Y → Point n → ℝ)
    (hSmul : ∀ j (d : ℝ) f p, p ∈ cylinder univ 0 T → v j (d • f) p = d*v j f p)
    (d : ℝ) (f : Y) (x : M.Carrier) {t : ℝ} (ht : t ∈ Icc 0 T) :
    F05FiniteManifoldPatch A β (fun j => v j (d • f)) x t =
      d*F05FiniteManifoldPatch A β (fun j => v j f) x t := by
  unfold F05FiniteManifoldPatch F05ManifoldPatch
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  dsimp only
  rw [hSmul j d f _ ⟨mem_univ _,ht⟩]
  ring

end Yau.Proofs.F05Aux
