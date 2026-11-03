import Yau.Proofs.F05OuterCutoffs

/-! A smooth map on an open neighborhood has a genuine global smooth
representative on each compact buffer. This uses an actual smooth cutoff. -/

open Set Filter
open scoped Topology ContDiff Manifold
noncomputable section
set_option maxHeartbeats 1800000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic

theorem F05_compact_smooth_extension {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V K : Set (Space n)} (hV : IsOpen V) (hK : IsCompact K) (hKV : K ⊆ V)
    {g : Space n → E} {k : ℕ∞} (hg : ContDiffOn ℝ k g V) :
    ∃ G : Space n → E, ContDiff ℝ k G ∧ EqOn G g K := by
  classical
  let U : Unit → Set (Space n) := fun _ => V
  have hCover : K ⊆ ⋃ j,U j := fun x hx => mem_iUnion.mpr ⟨(),hKV hx⟩
  obtain ⟨p,hp⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ,Space n)) hK.isClosed U (fun _ => hV) hCover
  have hθ : ContDiff ℝ ∞ (p ()) := (p ()).contMDiff.contDiff
  let G : Space n → E := fun x => p () x • g x
  refine ⟨G,?_,?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport (p ())
    · exact (hθ.of_le (by simp)).contDiffAt.smul
        (hg.contDiffAt (hV.mem_nhds (hp () hx)))
    · have hz : (p () : Space n → ℝ) =ᶠ[𝓝 x] 0 :=
        notMem_tsupport_iff_eventuallyEq.mp hx
      have hG : G =ᶠ[𝓝 x] 0 := by
        filter_upwards [hz] with y hy
        simp only [G,hy,Pi.zero_apply,zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq hG
  · intro x hx
    have hOne : p () x = 1 := by
      simpa [finsum_eq_sum_of_fintype] using p.sum_eq_one hx
    simp only [G,hOne,one_smul]

end Yau.Proofs.F05Aux
