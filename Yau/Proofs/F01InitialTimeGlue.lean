import spec.CHAIN.CONTRACTS

/-! Uncompiled F01 scratch: only the actual first time derivative is glued.
This does not claim that zero extension is jointly C2 in space-time, nor that
its second time derivative exists across the initial face. -/
open Set Filter
open scoped Topology
noncomputable section
namespace Yau.NodeProofs.F01Aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def forwardZeroExtension (u : ℝ → E) (t : ℝ) : E := if t ≤ 0 then 0 else u t

theorem forwardZeroExtension_eq_of_nonpos (u : ℝ → E) {t : ℝ} (ht : t ≤ 0) :
    forwardZeroExtension u t = 0 := if_pos ht

theorem forwardZeroExtension_eq_of_nonneg {u : ℝ → E} (hu0 : u 0 = 0)
    {t : ℝ} (ht : 0 ≤ t) : forwardZeroExtension u t = u t := by
  by_cases hn : t ≤ 0
  · have he : t = 0 := le_antisymm hn ht
    subst t
    simp [forwardZeroExtension, hu0]
  · exact if_neg hn

/-- Zero initial value and zero one-sided first time jet give a genuine
first derivative at the initial interior point of the extended interval. -/
theorem forwardZeroExtension_hasDerivAt_zero {u : ℝ → E} (hu0 : u 0 = 0)
    (hu : HasDerivWithinAt u 0 (Ici 0) 0) :
    HasDerivAt (forwardZeroExtension u) 0 0 := by
  have hR : HasDerivWithinAt (forwardZeroExtension u) 0 (Ici 0) 0 :=
    hu.congr (fun t ht => forwardZeroExtension_eq_of_nonneg hu0 ht)
      (forwardZeroExtension_eq_of_nonneg hu0 le_rfl)
  have hL : HasDerivWithinAt (forwardZeroExtension u) 0 (Iic 0) 0 :=
    (hasDerivWithinAt_const (0 : ℝ) (Iic 0) (0 : E)).congr
      (fun t ht => forwardZeroExtension_eq_of_nonpos u ht)
      (forwardZeroExtension_eq_of_nonpos u le_rfl)
  have hU : HasDerivWithinAt (forwardZeroExtension u) 0 univ 0 := by
    simpa only [Iic_union_Ici] using hL.union hR
  exact hU.hasDerivAt (by simp)

/-- The genuine L17 closed interval at zero determines the same right-hand
jet on Ici0 because the positive upper endpoint is a neighborhood of zero. -/
theorem initial_Ici_jet_of_Icc {u : ℝ → E} {T : ℝ} (hT : 0 < T)
    (hu : HasDerivWithinAt u 0 (Icc 0 T) 0) :
    HasDerivWithinAt u 0 (Ici 0) 0 := by
  have hN : Iic T ∈ 𝓝 (0 : ℝ) := Iic_mem_nhds hT
  apply (hasDerivWithinAt_inter hN).mp
  simpa only [Ici_inter_Iic] using hu

/-- Restrict the glued first derivative to any actual closed cylinder time
slice; uniqueness of a derivative at a boundary is handled by its real set. -/
theorem forwardZeroExtension_hasDerivWithinAt_zero {u : ℝ → E} (hu0 : u 0 = 0)
    (hu : HasDerivWithinAt u 0 (Ici 0) 0) (I : Set ℝ) :
    HasDerivWithinAt (forwardZeroExtension u) 0 I 0 :=
  (forwardZeroExtension_hasDerivAt_zero hu0 hu).hasDerivWithinAt

end Yau.NodeProofs.F01Aux
