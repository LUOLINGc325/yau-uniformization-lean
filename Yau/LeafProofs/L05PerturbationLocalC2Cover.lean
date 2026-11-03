import Yau.LeafProofs.L05PerturbationGeometry

open Filter Set Metric
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_patch_mem_nhdsWithin {n : ℕ} {Q V P : Set (Point n)}
    (hV : IsOpen V) {p : Point n} (hp : p∈Q) (hpV : p∈V) (hSub : Q∩V⊆P) :
    P∈𝓝[Q] p := by
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hpV)] with q hqQ hqV
  exact hSub ⟨hqQ,hqV⟩

theorem perturb_fiber_patch_mem_nhdsWithin {n : ℕ} {Q V P : Set (Point n)}
    (hV : IsOpen V) {p : Point n} (hpV : p∈V) (hSub : Q∩V⊆P) :
    {t : ℝ | (p.1,t)∈P}∈𝓝[{t : ℝ | (p.1,t)∈Q}] p.2 := by
  have hCont : Continuous (fun t : ℝ => (p.1,t)) := continuous_const.prodMk continuous_id
  have hVN : {t : ℝ | (p.1,t)∈V}∈𝓝 p.2 := hCont.continuousAt.preimage_mem_nhds (hV.mem_nhds hpV)
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds hVN] with t htQ htV
  exact hSub ⟨htQ,htV⟩

theorem perturb_timeD_of_relative_patch {n : ℕ} {Q V P : Set (Point n)} {u : Point n → ℝ}
    (hu : C2 P u) (hV : IsOpen V) (hSub : Q∩V⊆P) {p : Point n}
    (hp : p∈Q) (hpV : p∈V)
    (hUnique : UniqueDiffWithinAt ℝ {t : ℝ | (p.1,t)∈Q} p.2) :
    timeD Q u p=timeD P u p := by
  have hDeriv := (hu.2.2.2.2.2 p (hSub ⟨hp,hpV⟩)).hasDerivWithinAt
  exact (hDeriv.mono_of_mem_nhdsWithin (perturb_fiber_patch_mem_nhdsWithin hV hpV hSub)).derivWithin hUnique

theorem perturb_continuousOn_of_relative_cover {n : ℕ} {W : Type*} [TopologicalSpace W]
    {Q : Set (Point n)} (v : Point n → W)
    (hCover : ∀ p∈Q, ∃ V P : Set (Point n), IsOpen V ∧ p∈V ∧ Q∩V⊆P ∧ ContinuousOn v P) :
    ContinuousOn v Q := by
  intro p hp
  obtain ⟨V,P,hV,hpV,hSub,hC⟩ := hCover p hp
  exact (hC p (hSub ⟨hp,hpV⟩)).mono_of_mem_nhdsWithin (perturb_patch_mem_nhdsWithin hV hp hpV hSub)

theorem perturb_c2_of_relative_cover {n : ℕ} {Q : Set (Point n)} {u : Point n → ℝ}
    (hUnique : ∀ p∈Q, UniqueDiffWithinAt ℝ {t : ℝ | (p.1,t)∈Q} p.2)
    (hCover : ∀ p∈Q, ∃ V P : Set (Point n), IsOpen V ∧ p∈V ∧ Q∩V⊆P ∧ C2 P u) :
    C2 Q u := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · apply perturb_continuousOn_of_relative_cover u
    intro p hp
    obtain ⟨V,P,hV,hpV,hSub,huP⟩ := hCover p hp
    exact ⟨V,P,hV,hpV,hSub,huP.1⟩
  · apply perturb_continuousOn_of_relative_cover (spatialD u)
    intro p hp
    obtain ⟨V,P,hV,hpV,hSub,huP⟩ := hCover p hp
    exact ⟨V,P,hV,hpV,hSub,huP.2.1⟩
  · apply perturb_continuousOn_of_relative_cover (spatialDD u)
    intro p hp
    obtain ⟨V,P,hV,hpV,hSub,huP⟩ := hCover p hp
    exact ⟨V,P,hV,hpV,hSub,huP.2.2.1⟩
  · intro p hp
    obtain ⟨V,P,hV,hpV,hSub,huP⟩ := hCover p hp
    have hContinuous := (huP.2.2.2.1 p (hSub ⟨hp,hpV⟩)).mono_of_mem_nhdsWithin
      (perturb_patch_mem_nhdsWithin hV hp hpV hSub)
    apply hContinuous.congr_of_eventuallyEq_of_mem _ hp
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hpV)] with q hqQ hqV
    exact perturb_timeD_of_relative_patch huP hV hSub hqQ hqV (hUnique q hqQ)
  · intro p hp
    obtain ⟨V,P,hV,hpV,hSub,huP⟩ := hCover p hp
    exact huP.2.2.2.2.1 p (hSub ⟨hp,hpV⟩)
  · intro p hp
    obtain ⟨V,P,hV,hpV,hSub,huP⟩ := hCover p hp
    exact (huP.2.2.2.2.2 p (hSub ⟨hp,hpV⟩)).mono_of_mem_nhdsWithin
      (perturb_fiber_patch_mem_nhdsWithin hV hpV hSub)

end Yau.LeafProofs.L05Aux
