import Yau.Proofs.V03Envelope

/-! A finite contact with the genuine neighborhood liminf supplies raw
competitors arbitrarily close to the test, with centers in any prescribed
neighborhood. -/

open scoped Topology
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem exists_near_liminf_contact {α : Type*} [TopologicalSpace α]
    {f : α → EReal} {φ : α → ℝ} {S U : Set α} {c : α}
    (hcontact : liminf f (𝓝[S] c) = (φ c : EReal))
    (hφ : ContinuousWithinAt φ S c) (hU : U ∈ 𝓝[S] c)
    {η : ℝ} (hη : 0 < η) :
    ∃ x ∈ U ∩ S, f x < ((φ x + η : ℝ) : EReal) := by
  by_contra hn
  have hnot : ∀ x ∈ U ∩ S, ((φ x + η : ℝ) : EReal) ≤ f x := by
    intro x hx
    exact le_of_not_gt (fun hh => hn ⟨x, hx, hh⟩)
  have hφnear : ∀ᶠ x in 𝓝[S] c, φ c - η / 2 < φ x :=
    hφ (Ioi_mem_nhds (by linarith))
  have hbound : ∀ᶠ x in 𝓝[S] c, ((φ c + η / 2 : ℝ) : EReal) ≤ f x := by
    filter_upwards [hφnear, hU, self_mem_nhdsWithin] with x hx hxU hxS
    exact (EReal.coe_le_coe_iff.mpr (by linarith)).trans (hnot x ⟨hxU, hxS⟩)
  have hle : ((φ c + η / 2 : ℝ) : EReal) ≤ liminf f (𝓝[S] c) :=
    le_sSup hbound
  rw [hcontact] at hle
  have := EReal.coe_le_coe_iff.mp hle
  linarith

end Yau.Blueprint.V03Proof
