import Yau.Proofs.F05AtlasCompactness
import Yau.Proofs.F05CompactContact

/-! Upper semicontinuity and the actual physical boundary isolate a genuine
interior space-time upper contact; no smoothness of the subsolution is used. -/

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_interior_upper_contact {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {s : ℝ} (hs : 0 < s) (F : M.Carrier → ℝ → ℝ)
    (hF : UpperSemicontinuousOn (fun q : M.Carrier × ℝ => F q.1 q.2) (closure O ×ˢ Icc 0 s))
    (hInitial : ∀ x ∈ closure O, F x 0 ≤ 0)
    (hBoundary : ∀ x ∈ frontier O, ∀ t ∈ Icc 0 s, F x t ≤ 0)
    (hFinal : ∀ x ∈ closure O, F x s ≤ 0)
    (hPos : ∃ x ∈ closure O, ∃ t ∈ Icc 0 s, 0 < F x t) :
    ∃ x ∈ O, ∃ t ∈ Ioo 0 s, 0 < F x t ∧ IsLocalMax (fun q : M.Carrier × ℝ => F q.1 q.2) (x,t) := by
  obtain ⟨x,hx,t,ht,hPos⟩ := hPos
  obtain ⟨q,hq,hMax⟩ := UpperSemicontinuousOn.exists_isMaxOn
    (show (closure O ×ˢ Icc 0 s).Nonempty from ⟨(x,t),hx,ht⟩)
    ((F05_atlas_closure_compact hA).prod isCompact_Icc) hF
  have hQPos : 0 < F q.1 q.2 := hPos.trans_le (hMax (show (x,t) ∈ closure O ×ˢ Icc 0 s from ⟨hx,ht⟩))
  have hOpen := F05_atlas_domain_isOpen hA
  have hQO : q.1 ∈ O := by
    by_contra hOut
    have hFrontier : q.1 ∈ frontier O := ⟨hq.1,by simpa only [hOpen.interior_eq] using hOut⟩
    exact not_lt_of_ge (hBoundary q.1 hFrontier q.2 hq.2) hQPos
  have hQ0 : 0 < q.2 := by
    by_contra hn
    have hZero : q.2 = 0 := le_antisymm (le_of_not_gt hn) hq.2.1
    exact not_lt_of_ge (show F q.1 q.2 ≤ 0 by simpa only [hZero] using hInitial q.1 hq.1) hQPos
  have hQs : q.2 < s := by
    by_contra hn
    have hEnd : q.2 = s := le_antisymm hq.2.2 (le_of_not_gt hn)
    exact not_lt_of_ge (show F q.1 q.2 ≤ 0 by simpa only [hEnd] using hFinal q.1 hq.1) hQPos
  refine ⟨q.1,hQO,q.2,⟨hQ0,hQs⟩,hQPos,hMax.isLocalMax ?_⟩
  apply mem_of_superset ((hOpen.prod isOpen_Ioo).mem_nhds (show q ∈ O ×ˢ Ioo 0 s from ⟨hQO,hQ0,hQs⟩))
  intro p hp
  exact ⟨subset_closure hp.1,hp.2.1.le,hp.2.2.le⟩

end Yau.Proofs.F05Aux
