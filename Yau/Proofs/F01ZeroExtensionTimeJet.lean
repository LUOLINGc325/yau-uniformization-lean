import Yau.Proofs.F01InitialTimeGlue

/-! The actual zero extension has the clamped first time jet on every
larger initial cylinder. The zero jet at zero is glued from the two genuine
one-sided derivatives, with locality at positive and negative times. -/
noncomputable section
open Set Filter
open scoped Topology
namespace Yau.NodeProofs.F01Aux
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem forwardZeroExtension_time_jet {u d : ℝ → V} {a T : ℝ} (hT : 0 < T)
    (hu0 : u 0 = 0) (hd0 : d 0 = 0)
    (hu : ∀ s ∈ Icc 0 T, HasDerivWithinAt u (d s) (Icc 0 T) s)
    {t : ℝ} (ht : t ∈ Icc a T) :
    HasDerivWithinAt (forwardZeroExtension u) (forwardZeroExtension d t) (Icc a T) t := by
  by_cases hneg : t < 0
  · rw [forwardZeroExtension_eq_of_nonpos d hneg.le]
    have heq : forwardZeroExtension u =ᶠ[𝓝 t] (fun _ => (0 : V)) := by
      filter_upwards [Iio_mem_nhds hneg] with s hs
      exact forwardZeroExtension_eq_of_nonpos u hs.le
    exact ((hasDerivAt_const t (0 : V)).congr_of_eventuallyEq heq).hasDerivWithinAt
  by_cases hzero : t = 0
  · subst t
    rw [forwardZeroExtension_eq_of_nonpos d le_rfl]
    have hjet := hu 0 ⟨le_rfl, hT.le⟩
    rw [hd0] at hjet
    exact (forwardZeroExtension_hasDerivAt_zero hu0 (initial_Ici_jet_of_Icc hT hjet)).hasDerivWithinAt
  have hpos : 0 < t := lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hzero)
  rw [forwardZeroExtension_eq_of_nonneg hd0 hpos.le]
  have hgiven : HasDerivWithinAt (forwardZeroExtension u) (d t) (Icc 0 T) t :=
    (hu t ⟨hpos.le, ht.2⟩).congr
      (fun s hs => forwardZeroExtension_eq_of_nonneg hu0 hs.1)
      (forwardZeroExtension_eq_of_nonneg hu0 hpos.le)
  apply hgiven.mono_of_mem_nhdsWithin
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hpos), self_mem_nhdsWithin] with s hspos hs
  exact ⟨hspos.le, hs.2⟩

end Yau.NodeProofs.F01Aux
