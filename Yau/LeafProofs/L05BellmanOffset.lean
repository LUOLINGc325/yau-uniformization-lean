import Yau.LeafProofs.L05ChuSupporting

noncomputable section

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic Yau.ParabolicCandidates

theorem tracePair_continuous_left {n : ℕ} (H : Sym n) : Continuous (fun A : Sym n => tracePair A H) := by
  unfold tracePair
  fun_prop

theorem tracePair_continuous_right {n : ℕ} (A : Sym n) : Continuous (fun H : Sym n => tracePair A H) := by
  unfold tracePair
  fun_prop

theorem tracePair_sub_left {n : ℕ} (A B H : Sym n) : tracePair A H-tracePair B H=tracePair (A-B) H := by
  simp only [tracePair,AddSubgroup.coe_sub,Matrix.sub_mul,Matrix.trace_sub]

def bellmanOffset {n : ℕ} (E : Set (Sym n)) (F : Sym n → Point n → ℝ) (A : Sym n) (p : Point n) : ℝ :=
  sSup ((fun M => F M p-tracePair A M) '' E)

theorem bellmanOffset_attained {n : ℕ} {E : Set (Sym n)} (hE : IsCompact E) (hne : E.Nonempty)
    {F : Sym n → Point n → ℝ} {p : Point n} (hF : ContinuousOn (fun M => F M p) E) (A : Sym n) :
    ∃ M ∈ E, bellmanOffset E F A p=F M p-tracePair A M := by
  have hc := hF.sub (tracePair_continuous_right A).continuousOn
  obtain ⟨M,hM,hmax⟩ := hE.exists_isMaxOn hne hc
  refine ⟨M,hM,le_antisymm ?_ ?_⟩
  · apply csSup_le (hne.image (fun M => F M p-tracePair A M))
    rintro r ⟨N,hN,rfl⟩
    exact hmax hN
  · exact le_csSup (hE.bddAbove_image hc) (Set.mem_image_of_mem _ hM)

theorem le_bellmanOffset {n : ℕ} {E : Set (Sym n)} (hE : IsCompact E)
    {F : Sym n → Point n → ℝ} {p : Point n} (hF : ContinuousOn (fun M => F M p) E)
    (A : Sym n) {M : Sym n} (hM : M ∈ E) : F M p-tracePair A M ≤ bellmanOffset E F A p := by
  exact le_csSup (hE.bddAbove_image (hF.sub (tracePair_continuous_right A).continuousOn))
    (Set.mem_image_of_mem _ hM)

theorem bellmanOffset_le {n : ℕ} {E : Set (Sym n)} (hne : E.Nonempty)
    {F : Sym n → Point n → ℝ} {p : Point n} {A : Sym n} {c : ℝ}
    (hb : ∀ M ∈ E, F M p-tracePair A M ≤ c) : bellmanOffset E F A p ≤ c := by
  apply csSup_le (hne.image _)
  rintro r ⟨M,hM,rfl⟩
  exact hb M hM

theorem bellmanOffset_chuSlope {n : ℕ} {E U : Set (Sym n)}
    (hne : E.Nonempty) (hE : Convex ℝ E) {F : Sym n → Point n → ℝ}
    {ell L K beta : ℝ} (hF : ChuH1 E U F ell L K beta)
    {N : Sym n} (hN : N ∈ E) {p : Point n} (hp : p ∈ backward 1) :
    bellmanOffset E F (chuSlope F N p) p=F N p-tracePair (chuSlope F N p) N := by
  apply le_antisymm
  · apply bellmanOffset_le hne
    intro M hM
    have hh := chu_supporting_plane hE hF hN hM hp
    rw [← tracePair_sub] at hh
    linarith only [hh]
  · apply le_csSup
    · refine ⟨F N p-tracePair (chuSlope F N p) N,?_⟩
      rintro r ⟨M,hM,rfl⟩
      have hh := chu_supporting_plane hE hF hN hM hp
      rw [← tracePair_sub] at hh
      linarith only [hh]
    · exact Set.mem_image_of_mem _ hN

theorem bellmanOffset_time_holder {n : ℕ} {E U : Set (Sym n)}
    (hE : IsCompact E) (hne : E.Nonempty) {F : Sym n → Point n → ℝ}
    {ell L K beta : ℝ} (hF : ChuH1 E U F ell L K beta)
    (A : Sym n) {p q : Point n} (hp : p ∈ backward 1) (hq : q ∈ backward 1) :
    |bellmanOffset E F A p-bellmanOffset E F A q| ≤ K*holderWeight beta p q := by
  obtain ⟨M,hM,hm⟩ := bellmanOffset_attained hE hne (chu_matrix_continuousOn hF hp) A
  obtain ⟨N,hN,hn⟩ := bellmanOffset_attained hE hne (chu_matrix_continuousOn hF hq) A
  have hlp := le_bellmanOffset hE (chu_matrix_continuousOn hF hp) A hN
  have hlq := le_bellmanOffset hE (chu_matrix_continuousOn hF hq) A hM
  rw [hm] at hlp
  rw [hn] at hlq
  have hMf := abs_le.mp (hF.2.2.2.2.2.1 M hM p hp q hq)
  have hNf := abs_le.mp (hF.2.2.2.2.2.1 N hN p hp q hq)
  rw [hm,hn]
  exact abs_le.mpr ⟨by linarith only [hlp,hNf.1],by linarith only [hlq,hMf.2]⟩

theorem bellmanOffset_slope_sub_le {n : ℕ} {E : Set (Sym n)}
    (hE : IsCompact E) (hne : E.Nonempty) {F : Sym n → Point n → ℝ}
    {p : Point n} (hF : ContinuousOn (fun M => F M p) E) {D : ℝ}
    (hb : ∀ M ∈ E, ‖M‖ ≤ D) (A B : Sym n) :
    |bellmanOffset E F A p-bellmanOffset E F B p| ≤
      Real.sqrt (Fintype.card (RIdx n))*‖A-B‖*D := by
  obtain ⟨M,hM,hm⟩ := bellmanOffset_attained hE hne hF A
  obtain ⟨N,hN,hn⟩ := bellmanOffset_attained hE hne hF B
  have hlA := le_bellmanOffset hE hF A hN
  have hlB := le_bellmanOffset hE hF B hM
  rw [hm] at hlA
  rw [hn] at hlB
  have htrace (P : Sym n) (hP : P ∈ E) : |tracePair A P-tracePair B P| ≤
      Real.sqrt (Fintype.card (RIdx n))*‖A-B‖*D := by
    rw [tracePair_sub_left]
    exact (abs_trace_mul_le ((A-B : Sym n) : Mat n) (P : Mat n)).trans
      (mul_le_mul_of_nonneg_left (hb P hP) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)))
  have hMtr := abs_le.mp (htrace M hM)
  have hNtr := abs_le.mp (htrace N hN)
  rw [hm,hn]
  exact abs_le.mpr ⟨by linarith only [hlA,hNtr.2],by linarith only [hlB,hMtr.1]⟩

theorem bellmanOffset_continuous {n : ℕ} {E : Set (Sym n)}
    (hE : IsCompact E) (hne : E.Nonempty) {F : Sym n → Point n → ℝ}
    {p : Point n} (hF : ContinuousOn (fun M => F M p) E) :
    Continuous (fun A : Sym n => bellmanOffset E F A p) := by
  obtain ⟨D,hD⟩ := hE.exists_bound_of_continuousOn continuous_id.continuousOn
  obtain ⟨M,hM⟩ := hne
  have hDp : 0 ≤ D := (norm_nonneg M).trans (hD M hM)
  have hl : LipschitzWith ⟨Real.sqrt (Fintype.card (RIdx n))*D,
      mul_nonneg (Real.sqrt_nonneg _) hDp⟩ (fun A : Sym n => bellmanOffset E F A p) := by
    apply LipschitzWith.of_dist_le_mul
    intro A B
    have hh := bellmanOffset_slope_sub_le hE ⟨M,hM⟩ hF hD A B
    change |bellmanOffset E F A p-bellmanOffset E F B p| ≤
      (Real.sqrt (Fintype.card (RIdx n))*D)*‖A-B‖
    calc
      _ ≤ Real.sqrt (Fintype.card (RIdx n))*‖A-B‖*D := hh
      _ = _ := by ring
  exact hl.continuous

end Yau.LeafProofs.L05Aux
