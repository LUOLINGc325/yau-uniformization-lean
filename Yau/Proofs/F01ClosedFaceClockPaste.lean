import Yau.Proofs.F01TimeFacePaste

/-! Clock equations on the two genuine sides paste by the actual
left derivative limit and the actual right closed-domain derivative. -/
noncomputable section
open Set Filter
open scoped Topology
namespace Yau.NodeProofs.F01Aux
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem closed_face_clock_equations_paste
    (f g P Q : E × ℝ → F) {O : Set E} {l T r : ℝ}
    (hlT : l < T) (hTr : T < r)
    (hMatch : ∀ x ∈ O, f (x, T) = g (x, T))
    (hPMatch : ∀ x ∈ O, P (x, T) = Q (x, T))
    (hf : ContinuousOn f (O ×ˢ Ioc l T))
    (hP : ContinuousOn P (O ×ˢ Ioc l T))
    (hLeft : ∀ x ∈ O, ∀ t ∈ Ioo l T, HasDerivAt (fun s => f (x, s)) (P (x, t)) t)
    (hRight : ∀ x ∈ O, ∀ t ∈ Ico T r,
      HasDerivWithinAt (fun s => g (x, s)) (Q (x, t)) (Ico T r) t) :
    ∀ p ∈ O ×ˢ Ioo l r, HasDerivAt (fun t => timeFacePaste f g T (p.1, t))
      (timeFacePaste P Q T p) p.2 := by
  intro p hp
  rcases lt_trichotomy p.2 T with hlt | he | hgt
  · have hEq : (fun t => timeFacePaste f g T (p.1, t)) =ᶠ[𝓝 p.2]
        (fun t => f (p.1, t)) := by
      filter_upwards [Iio_mem_nhds hlt] with t ht
      exact if_pos ht.le
    have hh := (hLeft p.1 hp.1 p.2 ⟨hp.2.1, hlt⟩).congr_of_eventuallyEq hEq
    simpa only [timeFacePaste, if_pos hlt.le] using hh
  · have hFC : ContinuousWithinAt (fun t => f (p.1, t)) (Ioc l T) T :=
      (hf.comp (continuousOn_const.prodMk continuousOn_id)
        (fun t ht => ⟨hp.1, ht⟩)) T ⟨hlT, le_rfl⟩
    have hPC : ContinuousWithinAt (fun t => P (p.1, t)) (Ioc l T) T :=
      (hP.comp (continuousOn_const.prodMk continuousOn_id)
        (fun t ht => ⟨hp.1, ht⟩)) T ⟨hlT, le_rfl⟩
    have hPL : Tendsto (fun t => P (p.1, t)) (𝓝[<] T) (𝓝 (P (p.1, T))) := by
      have hh := (hPC.mono Ioo_subset_Ioc_self).tendsto
      rwa [nhdsWithin_Ioo_eq_nhdsLT hlT] at hh
    have hL := terminal_left_time_jet (fun t => f (p.1, t)) (fun t => P (p.1, t))
      hlT (hFC.mono Ioo_subset_Ioc_self) (hLeft p.1 hp.1) hPL
    have hR : HasDerivWithinAt (fun t => g (p.1, t)) (Q (p.1, T)) (Ici T) T := by
      apply (hasDerivWithinAt_inter (Iio_mem_nhds hTr)).mp
      simpa only [Ici_inter_Iio] using hRight p.1 hp.1 T ⟨le_rfl, hTr⟩
    rw [← hPMatch p.1 hp.1] at hR
    have hh := timeFacePaste_hasDerivAt_face f g p.1 T (P (p.1, T))
      (hMatch p.1 hp.1) hL hR
    have hVal : P (p.1, T) = P p := congrArg P (Prod.ext rfl he.symm)
    rw [hVal] at hh
    simpa only [timeFacePaste, he, ite_true, le_refl] using hh
  · have hEq : (fun t => timeFacePaste f g T (p.1, t)) =ᶠ[𝓝 p.2]
        (fun t => g (p.1, t)) := by
      filter_upwards [Ioi_mem_nhds hgt] with t ht
      exact if_neg (not_le.mpr ht)
    have hN : Ico T r ∈ 𝓝 p.2 :=
      mem_of_superset (Ioo_mem_nhds hgt hp.2.2) Ioo_subset_Ico_self
    have hh := ((hRight p.1 hp.1 p.2 ⟨hgt.le, hp.2.2⟩).hasDerivAt hN).congr_of_eventuallyEq hEq
    simpa only [timeFacePaste, if_neg (not_le.mpr hgt)] using hh

end Yau.NodeProofs.F01Aux
