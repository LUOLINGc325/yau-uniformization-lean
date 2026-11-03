import Yau.Proofs.F05TransitionJetHolder
import Yau.Proofs.F05HolderTransitionNeighborhood
import Yau.Proofs.F05LocalHolderGluing
import Yau.Proofs.F05BootstrapRelativeRestriction

/-! The buffered radius-one atlas cover transfers a common physical
Schauder budget onto the entire radius-two receiving charts. Both the
actual normal/tangential Hessian transformation and terminal jets survive. -/

open Set
open scoped Topology ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_inner_jet_neighborhood {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (i : Fin A.count) (z : Space n) (hz : z ∈ F05D A i)
    {α s : ℝ} (hα : 0 < α) (hα1 : α < 1) (hs : 0 ≤ s) :
    ∃ (j : Fin A.count) (r C : ℝ), 0 < r ∧ 0 < C ∧
      ∀ (T P : ℝ) (w : M.Carrier → ℝ → ℝ),
      (∀ k, C2 (F05Q A k T) (pull A k w)) →
      F05RelSchauder α (region (A.normal j) (3/2)) (Icc s T) (pull A j w) P →
      HolderBound α (cylinder (F05D A i∩Metric.closedBall z r) s T)
        (fun p => ((pull A i w p,spatialD (pull A i w) p),
          (spatialDD (pull A i w) p,F05RelT (Icc s T) (pull A i w) p))) (C*P) := by
  obtain ⟨j,r0,L,hr0,hL,hMap,hLip⟩ := F05_inner_holder_neighborhood hA i z hz
  have hzBall : z ∈ Metric.closedBall z r0 := Metric.mem_closedBall_self hr0.le
  have hAt := hMap z ⟨hz,hzBall⟩
  have hzV : z ∈ F05TransitionDomain A i j := by
    refine ⟨F05D_mem_ball hz,F05Transition A i j z,?_,hAt.2⟩
    simpa only [Metric.mem_ball,dist_zero_right] using hAt.1.1.trans_lt (by norm_num : (3/2 : ℝ) < 3)
  obtain ⟨ε,hε,hBall⟩ := Metric.mem_nhds_iff.mp ((F05TransitionDomain_isOpen hA i j).mem_nhds hzV)
  let r := min r0 (ε/2)
  have hr : 0 < r := lt_min hr0 (by positivity)
  have hSmall : Metric.closedBall z r ⊆ Metric.closedBall z r0 :=
    Metric.closedBall_subset_closedBall (min_le_left _ _)
  have hDomain : Metric.closedBall z r ⊆ F05TransitionDomain A i j :=
    (Metric.closedBall_subset_ball (by dsimp only [r]; have h := min_le_right r0 (ε/2); linarith)).trans hBall
  have hMap' : MapsTo (F05Transition A i j) (F05D A i∩Metric.closedBall z r)
      (region (A.normal j) (3/2)) := fun y hy => (hMap y ⟨hy.1,hSmall hy.2⟩).1
  obtain ⟨C,hC,hBudget⟩ := F05_transition_local_jet_holder hA i j (isCompact_closedBall z r)
    (convex_closedBall z r) hDomain hMap' hα hα1 hs
  exact ⟨j,r,C,hr,hC,hBudget⟩

theorem F05_inner_schauder_to_full_one {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (i : Fin A.count) {α s : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hs : 0 ≤ s) (S : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T P : ℝ) (w : M.Carrier → ℝ → ℝ), s < T → T ≤ S → 0 ≤ P →
      (∀ k, C2 (F05Q A k T) (pull A k w)) →
      (∀ j, F05RelSchauder α (region (A.normal j) (3/2)) (Icc s T) (pull A j w) P) →
      F05RelSchauder α (F05D A i) (Icc s T) (pull A i w) (C*P) := by
  classical
  letI : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
  letI : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
  letI : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
  letI : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
  have hLocal (z : F05D A i) := F05_inner_jet_neighborhood hA i z.val z.property hα hα1 hs
  choose j r C hr hC hBudget using hLocal
  obtain ⟨CG,hCG,hGlue⟩ := F05_uniform_compact_holder_glue_interval
    (E := (ℝ × (Space n →L[ℝ] ℝ)) × ((Space n →L[ℝ] Space n →L[ℝ] ℝ) × ℝ))
    (F05_region_isCompact (A.normal i) 2) hα.le s S r C hr (fun z => (hC z).le)
  refine ⟨CG,hCG,?_⟩
  intro T P w hsT hTS hP hw hInner
  have hHolder := hGlue T hsT.le hTS
    (fun z => ((pull A i w z,spatialD (pull A i w) z),
      (spatialDD (pull A i w) z,F05RelT (Icc s T) (pull A i w) z))) P hP
    (fun z => hBudget z T P w hw (hInner (j z)))
  have hX := F05_region_uniqueDiffOn (A.normal i) (by norm_num : (0 : ℝ) < 2)
  have hTime : Icc s T ⊆ Icc (0 : ℝ) T := fun t ht => ⟨hs.trans ht.1,ht.2⟩
  have hC2 := F05_relative_c2_restrict hX hX (uniqueDiffOn_Icc hsT) subset_rfl hTime
    (F05_native_c2_to_relative hX (hw i))
  have hD (z : Point n) (hz : z ∈ F05D A i ×ˢ Icc s T) :
      F05RelD (F05D A i) (pull A i w) z = spatialD (pull A i w) z :=
    F05RelD_eq_spatialD (hX z.1 hz.1)
      (((hw i).2.2.2.2.1 z ⟨hz.1,hTime hz.2⟩).differentiableAt (by norm_num))
  have hDD (z : Point n) (hz : z ∈ F05D A i ×ˢ Icc s T) :
      F05RelDD (F05D A i) (pull A i w) z = spatialDD (pull A i w) z :=
    F05RelDD_eq_spatialDD hX hz.1
      (fun x hx => (hw i).2.2.2.2.1 (x,z.2) ⟨hx,hTime hz.2⟩)
  refine ⟨hC2,?_,?_,holderBound_snd (holderBound_snd hHolder)⟩
  · apply holderBound_congr_on (holderBound_fst hHolder)
    intro z hz
    change (pull A i w z,spatialD (pull A i w) z) =
      (pull A i w z,F05RelD (F05D A i) (pull A i w) z)
    rw [hD z hz]
  · exact holderBound_congr_on (holderBound_fst (holderBound_snd hHolder)) (fun z hz => (hDD z hz).symm)

theorem F05_inner_schauder_to_full {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {α s : ℝ} (hα : 0 < α) (hα1 : α < 1) (hs : 0 ≤ s) (S : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T P : ℝ) (w : M.Carrier → ℝ → ℝ), s < T → T ≤ S → 0 ≤ P →
      (∀ k, C2 (F05Q A k T) (pull A k w)) →
      (∀ j, F05RelSchauder α (region (A.normal j) (3/2)) (Icc s T) (pull A j w) P) →
      ∀ i, F05RelSchauder α (F05D A i) (Icc s T) (pull A i w) (C*P) := by
  classical
  have hOne (i : Fin A.count) := F05_inner_schauder_to_full_one hA i hα hα1 hs S
  choose Ci hCi hBudget using hOne
  let C := 1+∑ i,Ci i
  have hSum : 0 ≤ ∑ i,Ci i := Finset.sum_nonneg (fun i _ => (hCi i).le)
  have hC : 0 < C := by dsimp only [C]; linarith
  refine ⟨C,hC,?_⟩
  intro T P w hsT hTS hP hw hInner i
  have hOut := hBudget i T P w hsT hTS hP hw hInner
  have hBound : Ci i*P ≤ C*P := by
    apply mul_le_mul_of_nonneg_right _ hP
    have hSingle := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin A.count))) => (hCi j).le)
      (Finset.mem_univ i)
    dsimp only [C]
    linarith
  exact ⟨hOut.1,holderBound_mono_const hOut.2.1 hBound,
    holderBound_mono_const hOut.2.2.1 hBound,holderBound_mono_const hOut.2.2.2 hBound⟩

end Yau.Proofs.F05Aux
