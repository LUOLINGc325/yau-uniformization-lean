import Yau.Proofs.D05ProjectedBundle
import Yau.Proofs.D05SplitAlgebra

/-! Local holomorphic projections and generators for the genuine kernel
subbundle obtained by splitting off one section. -/

open Set
open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.D05Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem LocallyProjectedOn.mono {B : ℂ → Submodule ℂ E} {U V : Set ℂ}
    (hB : LocallyProjectedOn B U) (hV : IsOpen V) (hVU : V ⊆ U) :
    LocallyProjectedOn B V := by
  intro p hp
  obtain ⟨O, hO, hpO, hOU, P, hP, hPrange, hPfix⟩ := hB p (hVU hp)
  exact ⟨O ∩ V, hO.inter hV, ⟨hpO, hp⟩, Set.inter_subset_right,
    P, hP.mono Set.inter_subset_left,
    fun z hz => hPrange z hz.1, fun z hz => hPfix z hz.1⟩

theorem splitProjection_contDiffOn {U : Set ℂ} {e : ℂ → E}
    (he : ContDiffOn ℂ ∞ e U) {a : ℂ → E →L[ℂ] ℂ}
    (ha : ContDiffOn ℂ ∞ a U) :
    ContDiffOn ℂ ∞ (fun z => splitProjection (e z) (a z)) U :=
  contDiffOn_const.sub (ha.smulRight he)

theorem kernelPart_locallyProjected {B : ℂ → Submodule ℂ E} {U : Set ℂ}
    (hB : LocallyProjectedOn B U) {e : ℂ → E} (he : ContDiffOn ℂ ∞ e U)
    {a : ℂ → E →L[ℂ] ℂ} (ha : ContDiffOn ℂ ∞ a U)
    (hem : ∀ z ∈ U, e z ∈ B z) (hae : ∀ z ∈ U, a z (e z) = 1) :
    LocallyProjectedOn (fun z => kernelPart (B z) (a z)) U := by
  intro p hp
  obtain ⟨V, hV, hpV, hVU, P, hP, hPrange, hPfix⟩ := hB p hp
  refine ⟨V, hV, hpV, hVU,
    fun z => (splitProjection (e z) (a z)).comp (P z),
    (splitProjection_contDiffOn (he.mono hVU) (ha.mono hVU)).clm_comp hP, ?_, ?_⟩
  · intro z hz v
    exact splitProjection_mem (hem z (hVU hz)) (hae z (hVU hz)) (hPrange z hz v)
  · intro z hz v hv
    change splitProjection (e z) (a z) (P z v) = v
    rw [hPfix z hz v hv.1]
    exact splitProjection_fix hv

theorem split_generator_contDiffOn {U : Set ℂ} {e s : ℂ → E}
    (he : ContDiffOn ℂ ∞ e U) (hs : ContDiffOn ℂ ∞ s U)
    {a : ℂ → E →L[ℂ] ℂ} (ha : ContDiffOn ℂ ∞ a U) :
    ContDiffOn ℂ ∞ (fun z => splitProjection (e z) (a z) (s z)) U :=
  (splitProjection_contDiffOn he ha).clm_apply hs

theorem split_generated_bundle {ι : Type*} {B : ℂ → Submodule ℂ E} {U : Set ℂ}
    {e : ℂ → E} (he : ContDiffOn ℂ ∞ e U) {a : ℂ → E →L[ℂ] ℂ}
    (ha : ContDiffOn ℂ ∞ a U) (hem : ∀ z ∈ U, e z ∈ B z)
    (hae : ∀ z ∈ U, a z (e z) = 1) {s : ι → ℂ → E}
    (hs : ∀ i, ContDiffOn ℂ ∞ (s i) U)
    (hspan : ∀ z ∈ U, Submodule.span ℂ (Set.range fun i => s i z) = B z) :
    (∀ i, ContDiffOn ℂ ∞ (fun z => splitProjection (e z) (a z) (s i z)) U) ∧
    ∀ z ∈ U, Submodule.span ℂ
      (Set.range fun i => splitProjection (e z) (a z) (s i z)) = kernelPart (B z) (a z) :=
  ⟨fun i => split_generator_contDiffOn he (hs i) ha,
    fun z hz => split_generators_span (hem z hz) (hae z hz) (hspan z hz)⟩

end Yau.Blueprint.D05Proof
