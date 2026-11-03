import Yau.LeafProofs.L05DiniKernelDefinitions

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L05Aux

theorem dini_interval_norm_le_recent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → E} {J : ℝ → ℝ} {a b R : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ R)
    (hJI : IntervalIntegrable J volume 0 R) (hJ : ∀ s ∈ Set.Ioc 0 R, 0 ≤ J s)
    (hbound : ∀ᵐ s : ℝ, s ∈ Set.Ioc a b → ‖F s‖ ≤ J s) :
    ‖∫ s in a..b, F s‖ ≤ ∫ s in (0:ℝ)..R, J s := by
  have hR : 0 ≤ R := ha.trans (hab.trans hb)
  have hJab : IntervalIntegrable J volume a b := hJI.mono_set (by
    rw [Set.uIcc_of_le hab,Set.uIcc_of_le hR]
    exact Set.Icc_subset_Icc ha hb)
  apply (intervalIntegral.norm_integral_le_of_norm_le hab hbound hJab).trans
  apply intervalIntegral.integral_mono_interval ha hab hb _ hJI
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact hJ s hs

theorem dini_interval_norm_le_tail {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → E} {J : ℝ → ℝ} {a b c : ℝ} (hca : c ≤ a) (hab : a ≤ b)
    (hJI : IntegrableOn J (Set.Ioi c)) (hJ : ∀ s ∈ Set.Ioi c, 0 ≤ J s)
    (hbound : ∀ᵐ s : ℝ, s ∈ Set.Ioc a b → ‖F s‖ ≤ J s) :
    ‖∫ s in a..b, F s‖ ≤ ∫ s in Set.Ioi c, J s := by
  have hSub : Set.Ioc a b ⊆ Set.Ioi c := fun _ hs => hca.trans_lt hs.1
  have hJab : IntervalIntegrable J volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr (hJI.mono_set hSub)
  apply (intervalIntegral.norm_integral_le_of_norm_le hab hbound hJab).trans
  rw [intervalIntegral.integral_of_le hab]
  apply setIntegral_mono_set hJI _ (ae_of_all _ (fun _ hs => hSub hs))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact hJ s hs

theorem dini_near_far_integral_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → E} {J K : ℝ → ℝ} {d t A B : ℝ} (hd : 0 < d) (ht : 0 ≤ t) (hB : 0 ≤ B)
    (hFI : IntervalIntegrable F volume 0 t) (hJI : IntervalIntegrable J volume 0 d)
    (hKI : IntegrableOn K (Set.Ioi d)) (hJ : ∀ a ∈ Set.Ioc 0 d, 0 ≤ J a)
    (hK : ∀ a ∈ Set.Ioi d, 0 ≤ K a)
    (hnear : ∀ a ∈ Set.Ioc 0 t, ‖F a‖ ≤ J a)
    (hfar : ∀ a ∈ Set.Ioc d t, ‖F a‖ ≤ K a)
    (hJA : (∫ a in (0:ℝ)..d, J a) ≤ A) (hKB : (∫ a in Set.Ioi d, K a) ≤ B) :
    ‖∫ a in (0:ℝ)..t, F a‖ ≤ A+B := by
  by_cases htd : t ≤ d
  · have hn := dini_interval_norm_le_recent le_rfl ht htd hJI hJ (ae_of_all _ hnear)
    linarith only [hn,hJA,hB]
  · have hdt : d < t := lt_of_not_ge htd
    have hFd : IntervalIntegrable F volume 0 d := hFI.mono_set (by
      rw [Set.uIcc_of_le hd.le,Set.uIcc_of_le ht]
      exact Set.Icc_subset_Icc le_rfl hdt.le)
    have hFt : IntervalIntegrable F volume d t := hFI.mono_set (by
      rw [Set.uIcc_of_le hdt.le,Set.uIcc_of_le ht]
      exact Set.Icc_subset_Icc hd.le le_rfl)
    have hn := dini_interval_norm_le_recent le_rfl hd.le le_rfl hJI hJ
      (ae_of_all _ (fun a ha => hnear a ⟨ha.1,ha.2.trans hdt.le⟩))
    have hf := dini_interval_norm_le_tail le_rfl hdt.le hKI hK (ae_of_all _ hfar)
    rw [← intervalIntegral.integral_add_adjacent_intervals hFd hFt]
    exact (norm_add_le _ _).trans (add_le_add (hn.trans hJA) (hf.trans hKB))

theorem dini_causal_interval_decomposition {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N O : ℝ → E} {b s t : ℝ} (hb : 0 ≤ b) (hbs : b ≤ s) (hst : s ≤ t)
    (hN : IntervalIntegrable N volume 0 t) (hO : IntervalIntegrable O volume 0 s) :
    (∫ a in (0:ℝ)..t, N a)-(∫ a in (0:ℝ)..s, O a) =
      (∫ a in (0:ℝ)..b, N a-O a)+(∫ a in b..t, N a)-(∫ a in b..s, O a) := by
  have hs : 0 ≤ s := hb.trans hbs
  have ht : 0 ≤ t := hs.trans hst
  have hbt : b ≤ t := hbs.trans hst
  have hNb : IntervalIntegrable N volume 0 b := hN.mono_set (by
    rw [Set.uIcc_of_le hb,Set.uIcc_of_le ht]
    exact Set.Icc_subset_Icc le_rfl hbt)
  have hNt : IntervalIntegrable N volume b t := hN.mono_set (by
    rw [Set.uIcc_of_le hbt,Set.uIcc_of_le ht]
    exact Set.Icc_subset_Icc hb le_rfl)
  have hOb : IntervalIntegrable O volume 0 b := hO.mono_set (by
    rw [Set.uIcc_of_le hb,Set.uIcc_of_le hs]
    exact Set.Icc_subset_Icc le_rfl hbs)
  have hOs : IntervalIntegrable O volume b s := hO.mono_set (by
    rw [Set.uIcc_of_le hbs,Set.uIcc_of_le hs]
    exact Set.Icc_subset_Icc hb le_rfl)
  rw [← intervalIntegral.integral_add_adjacent_intervals hNb hNt,
    ← intervalIntegral.integral_add_adjacent_intervals hOb hOs,
    intervalIntegral.integral_sub hNb hOb]
  abel

theorem dini_causal_time_geometry {r s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (hdelta : t-s ≤ r^2) :
    0 ≤ max 0 (s-r^2) ∧ max 0 (s-r^2) ≤ s ∧ max 0 (s-r^2) ≤ t ∧
      t-max 0 (s-r^2) ≤ 2*r^2 ∧ s-max 0 (s-r^2) ≤ r^2 ∧
      (0 < max 0 (s-r^2) → s-max 0 (s-r^2)=r^2) := by
  have hb0 : 0 ≤ max 0 (s-r^2) := le_max_left _ _
  have hbs : max 0 (s-r^2) ≤ s := max_le hs (sub_le_self _ (sq_nonneg _))
  have hb : s-r^2 ≤ max 0 (s-r^2) := le_max_right _ _
  refine ⟨hb0,hbs,hbs.trans hst,?_,?_,?_⟩
  · linarith only [hb,hdelta]
  · linarith only [hb]
  · intro hpos
    have hlt : 0 < s-r^2 := (lt_max_iff.mp hpos).resolve_left (lt_irrefl _)
    rw [max_eq_right hlt.le]
    ring

end Yau.LeafProofs.L05Aux
