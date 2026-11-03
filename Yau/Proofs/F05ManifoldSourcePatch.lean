import Yau.Proofs.F05ManifoldPatch
import Yau.Proofs.F05PhysicalHolderExtension
import Yau.Proofs.F05BufferedHolderComposition

/-! A physical source patch, with no lateral trace assumption, has one
actual Holder budget in all manifold charts before the endpoint or source. -/

open Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_physical_source_patch_equality {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (i j : Fin A.count) {β : M.Carrier → ℝ}
    (hSupport : tsupport β ⊆ lift A j '' Metric.closedBall 0 (3/4))
    (f : Point n → ℝ) {T : ℝ} {p : Point n} (hp : p ∈ F05Q A i T) :
    F05CrossCutoff A i β p.1 *
        F05PhysicalHolderExtension (A.normal j) f (F05Transition A i j p.1,p.2) =
      pull A i (F05ManifoldPatch A j β f) p := by
  have hNorm : ‖p.1‖ ≤ 21/10 := hp.1.1.trans (by norm_num)
  rw [F05CrossCutoff_eq i β hNorm]
  change β (lift A i p.1)*F05PhysicalHolderExtension (A.normal j) f
    (F05Coord A j (lift A i p.1),p.2) = β (lift A i p.1)*f (F05Coord A j (lift A i p.1),p.2)
  by_cases hβ : β (lift A i p.1) = 0
  · rw [hβ,zero_mul,zero_mul]
  obtain ⟨w,hw,heq⟩ := hSupport (subset_tsupport β hβ)
  have hn : ‖w‖ ≤ 3/4 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hw
  have hw3 : w ∈ Metric.ball (0 : Space n) 3 := Metric.closedBall_subset_ball (by norm_num : (3/4 : ℝ) < 3) hw
  obtain ⟨_,_,_,_,_,_,_,hPhysical⟩ := hA.1 j
  have hClosure := (hPhysical w hw3).2.1
  rw [heq] at hClosure
  have hwD : w ∈ F05D A j :=
    ⟨hn.trans (by norm_num),hClosure.mp (F05D_lift_mem_closure hA hp.1)⟩
  rw [← heq,F05Coord_lift hA hwD]
  congr 1
  exact F05PhysicalHolderExtension_eq (A.normal j) f (F05D_subset_model_closure A j hwD)

theorem F05_manifold_source_patch_budget {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (j : Fin A.count) {β : M.Carrier → ℝ}
    (hβ : SmoothFn β) (hSupport : tsupport β ⊆ lift A j '' Metric.closedBall 0 (3/4))
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T F : ℝ) (f : Point n → ℝ),
      HolderBound α (cylinder (closure (F05ModelOpen A j)) 0 T) f F →
      ∀ i : Fin A.count, HolderBound α (F05Q A i T)
        (pull A i (F05ManifoldPatch A j β f)) (C*F) := by
  classical
  have hLocal (i : Fin A.count) := F05_buffered_holder_composition_budget hα hα1
    (F05TransitionDomain_isOpen hA i j) ((F05Transition_contDiffOn hA i j).of_le (by simp))
    (F05CrossCutoff_contDiff hA i hβ) (F05CrossCutoff_compactSupport A i β)
    (F05CrossCutoff_tsupport_transition hA i j hSupport)
  choose C hC hBudget using hLocal
  let C₀ := 1+∑ i,C i
  have hSum : 0 ≤ ∑ i,C i := Finset.sum_nonneg (fun i _ => (hC i).le)
  have hC₀ : 0 < C₀ := by dsimp only [C₀]; positivity
  have hCi (i : Fin A.count) : C i ≤ C₀ := by
    have hh := Finset.single_le_sum
      (fun k (_ : k ∈ (Finset.univ : Finset (Fin A.count))) => (hC k).le) (Finset.mem_univ i)
    dsimp only [C₀]
    linarith
  refine ⟨5*C₀,by positivity,?_⟩
  intro T F f hf i
  have hExtension := F05PhysicalHolderExtension_holder (A.normal j) hα hf
  have hBound := hBudget i T (5*F) (F05PhysicalHolderExtension (A.normal j) f) hExtension
  have hSub : F05Q A i T ⊆ cylinder univ 0 T := fun p hp => ⟨mem_univ _,hp.2⟩
  have hActual := holderBound_congr_on (holderBound_mono hBound hSub)
    (fun p hp => F05_physical_source_patch_equality hA i j hSupport f hp)
  apply holderBound_mono_const hActual
  calc
    C i*(5*F) = 5*(C i*F) := by ring
    _ ≤ 5*(C₀*F) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hCi i) hf.1) (by norm_num)
    _ = (5*C₀)*F := by ring

end Yau.Proofs.F05Aux
