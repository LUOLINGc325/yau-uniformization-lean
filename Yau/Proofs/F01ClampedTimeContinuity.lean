import Yau.Proofs.F01InitialTimeGlue

/-! A zero initial value identifies the actual zero extension with
evaluation at the continuous clamped time. This gives continuity across zero
without asserting joint second time differentiability. -/
noncomputable section
open Set
namespace Yau.NodeProofs.F01Aux
variable {E V : Type*} [TopologicalSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def forwardZeroSpaceTime (F : E × ℝ → V) (p : E × ℝ) : V :=
  forwardZeroExtension (fun t => F (p.1, t)) p.2

theorem forwardZeroSpaceTime_eq_clamped {F : E × ℝ → V} {S : Set E}
    (hF0 : ∀ x ∈ S, F (x, 0) = 0) {x : E} (hx : x ∈ S) (t : ℝ) :
    forwardZeroSpaceTime F (x, t) = F (x, max t 0) := by
  by_cases ht : t ≤ 0
  · simp only [forwardZeroSpaceTime, forwardZeroExtension, if_pos ht, max_eq_right ht, hF0 x hx]
  · simp only [forwardZeroSpaceTime, forwardZeroExtension, if_neg ht,
      max_eq_left (le_of_not_ge ht)]

theorem forwardZeroSpaceTime_continuousOn {F : E × ℝ → V} {S : Set E} {a T : ℝ}
    (hT : 0 ≤ T) (hF : ContinuousOn F (S ×ˢ Icc 0 T))
    (hF0 : ∀ x ∈ S, F (x, 0) = 0) :
    ContinuousOn (forwardZeroSpaceTime F) (S ×ˢ Icc a T) := by
  have hp : Continuous (fun p : E × ℝ => (p.1, max p.2 0)) :=
    continuous_fst.prodMk (continuous_snd.max continuous_const)
  have hm : MapsTo (fun p : E × ℝ => (p.1, max p.2 0)) (S ×ˢ Icc a T) (S ×ˢ Icc 0 T) :=
    fun p hp => ⟨hp.1, le_max_right _ _, max_le hp.2.2 hT⟩
  apply (hF.comp hp.continuousOn hm).congr
  intro p hp
  exact forwardZeroSpaceTime_eq_clamped hF0 hp.1 p.2

end Yau.NodeProofs.F01Aux
