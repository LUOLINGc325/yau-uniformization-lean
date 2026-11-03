import Yau.LeafProofs.L05BellmanOffset

noncomputable section

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic Yau.ParabolicCandidates

theorem tracePair_add_right {n : ℕ} (A H K : Sym n) : tracePair A (H+K)=tracePair A H+tracePair A K := by
  simp only [tracePair,AddSubgroup.coe_add,Matrix.mul_add,Matrix.trace_add]

theorem tracePair_smul_right {n : ℕ} (A H : Sym n) (c : ℝ) : tracePair A (c • H)=c*tracePair A H := by
  simp only [tracePair,selfAdjoint.val_smul,Matrix.mul_smul,Matrix.trace_smul,smul_eq_mul]

def bellmanExtension {n : ℕ} (E : Set (Sym n)) (F : Sym n → Point n → ℝ)
    (ell L : ℝ) (N : Sym n) (p : Point n) : ℝ :=
  sInf ((fun A => tracePair A N+bellmanOffset E F A p) '' slopeSet n ell L)

theorem bellmanExtension_attained {n : ℕ} {E : Set (Sym n)}
    (hE : IsCompact E) (hne : E.Nonempty) {F : Sym n → Point n → ℝ}
    {ell L : ℝ} (hell : 0 ≤ ell) (hL : ell ≤ L) {p : Point n}
    (hF : ContinuousOn (fun M => F M p) E) (N : Sym n) :
    ∃ A ∈ slopeSet n ell L, bellmanExtension E F ell L N p=tracePair A N+bellmanOffset E F A p := by
  have hc := (tracePair_continuous_left N).add (bellmanOffset_continuous hE hne hF)
  obtain ⟨A,hA,hmin⟩ := (slopeSet_isCompact n hell).exists_isMinOn (slopeSet_nonempty n hL) hc.continuousOn
  refine ⟨A,hA,le_antisymm ?_ ?_⟩
  · exact csInf_le ((slopeSet_isCompact n hell).bddBelow_image hc.continuousOn) (Set.mem_image_of_mem _ hA)
  · apply le_csInf ((slopeSet_nonempty n hL).image _)
    rintro r ⟨B,hB,rfl⟩
    exact hmin hB

theorem bellmanExtension_le_candidate {n : ℕ} {E : Set (Sym n)}
    (hE : IsCompact E) (hne : E.Nonempty) {F : Sym n → Point n → ℝ}
    {ell L : ℝ} (hell : 0 ≤ ell) {p : Point n}
    (hF : ContinuousOn (fun M => F M p) E) (N : Sym n) {A : Sym n}
    (hA : A ∈ slopeSet n ell L) : bellmanExtension E F ell L N p ≤ tracePair A N+bellmanOffset E F A p := by
  have hc := (tracePair_continuous_left N).add (bellmanOffset_continuous hE hne hF)
  exact csInf_le ((slopeSet_isCompact n hell).bddBelow_image hc.continuousOn) (Set.mem_image_of_mem _ hA)

theorem bellmanExtension_eq_on {n : ℕ} {E U : Set (Sym n)}
    (hEc : IsCompact E) (hEv : Convex ℝ E) (hne : E.Nonempty)
    {F : Sym n → Point n → ℝ} {ell L K beta : ℝ} (hell : 0 ≤ ell) (hL : ell ≤ L)
    (hF : ChuH1 E U F ell L K beta) {N : Sym n} (hN : N ∈ E)
    {p : Point n} (hp : p ∈ backward 1) : bellmanExtension E F ell L N p=F N p := by
  apply le_antisymm
  · have hh := bellmanExtension_le_candidate hEc hne hell (chu_matrix_continuousOn hF hp) N
      (chuSlope_mem_slopeSet hF hN hp)
    rw [bellmanOffset_chuSlope hne hEv hF hN hp] at hh
    linarith only [hh]
  · obtain ⟨A,hA,he⟩ := bellmanExtension_attained hEc hne hell hL (chu_matrix_continuousOn hF hp) N
    have hh := le_bellmanOffset hEc (chu_matrix_continuousOn hF hp) A hN
    rw [he]
    linarith only [hh]

theorem bellmanExtension_globalElliptic {n : ℕ} {E : Set (Sym n)}
    (hE : IsCompact E) (hne : E.Nonempty) {F : Sym n → Point n → ℝ}
    {ell L : ℝ} (hell : 0 ≤ ell) (hL : ell ≤ L) {p : Point n}
    (hF : ContinuousOn (fun M => F M p) E) : globalElliptic (fun N => bellmanExtension E F ell L N p) ell L := by
  intro N P hP
  obtain ⟨A,hA,heA⟩ := bellmanExtension_attained hE hne hell hL hF N
  obtain ⟨B,hB,heB⟩ := bellmanExtension_attained hE hne hell hL hF (N+P)
  have hlow := bellmanExtension_le_candidate hE hne hell hF N hB
  have hupp := bellmanExtension_le_candidate hE hne hell hF (N+P) hA
  have hAtr := (slopeSet_tracePair_bounds hA hP).2
  have hBtr := (slopeSet_tracePair_bounds hB hP).1
  rw [tracePair_add_right] at heB hupp
  constructor <;> linarith only [heA,heB,hlow,hupp,hAtr,hBtr]

theorem bellmanExtension_concave {n : ℕ} {E : Set (Sym n)}
    (hE : IsCompact E) (hne : E.Nonempty) {F : Sym n → Point n → ℝ}
    {ell L : ℝ} (hell : 0 ≤ ell) (hL : ell ≤ L) {p : Point n}
    (hF : ContinuousOn (fun M => F M p) E) : ConcaveOn ℝ Set.univ (fun N => bellmanExtension E F ell L N p) := by
  refine ⟨convex_univ,?_⟩
  intro N hN M hM a b ha hb hab
  obtain ⟨A,hA,he⟩ := bellmanExtension_attained hE hne hell hL hF (a • N+b • M)
  have hn := mul_le_mul_of_nonneg_left (bellmanExtension_le_candidate hE hne hell hF N hA) ha
  have hm := mul_le_mul_of_nonneg_left (bellmanExtension_le_candidate hE hne hell hF M hA) hb
  change a*bellmanExtension E F ell L N p+b*bellmanExtension E F ell L M p ≤
    bellmanExtension E F ell L (a • N+b • M) p
  rw [he,tracePair_add_right,tracePair_smul_right,tracePair_smul_right]
  have hc := congrArg (fun r : ℝ => r*bellmanOffset E F A p) hab
  nlinarith only [hn,hm,hc]

theorem bellmanExtension_matrix_sub_le {n : ℕ} {E : Set (Sym n)}
    (hE : IsCompact E) (hne : E.Nonempty) {F : Sym n → Point n → ℝ}
    {ell L : ℝ} (hell : 0 ≤ ell) (hL : ell ≤ L) {p : Point n}
    (hF : ContinuousOn (fun M => F M p) E) (N M : Sym n) :
    |bellmanExtension E F ell L N p-bellmanExtension E F ell L M p| ≤
      Real.sqrt (Fintype.card (RIdx n))*((2*n)*L)*‖N-M‖ := by
  obtain ⟨A,hA,heA⟩ := bellmanExtension_attained hE hne hell hL hF N
  obtain ⟨B,hB,heB⟩ := bellmanExtension_attained hE hne hell hL hF M
  have hn := bellmanExtension_le_candidate hE hne hell hF N hB
  have hm := bellmanExtension_le_candidate hE hne hell hF M hA
  rw [heA] at hn
  rw [heB] at hm
  have hAtr := abs_le.mp (tracePair_sub_abs_le hell hA N M)
  have hBtr := abs_le.mp (tracePair_sub_abs_le hell hB N M)
  rw [heA,heB]
  exact abs_le.mpr ⟨by linarith only [hm,hAtr.1],by linarith only [hn,hBtr.2]⟩

theorem bellmanExtension_time_holder {n : ℕ} {E U : Set (Sym n)}
    (hE : IsCompact E) (hne : E.Nonempty) {F : Sym n → Point n → ℝ}
    {ell L K beta : ℝ} (hell : 0 ≤ ell) (hL : ell ≤ L) (hF : ChuH1 E U F ell L K beta)
    (N : Sym n) {p q : Point n} (hp : p ∈ backward 1) (hq : q ∈ backward 1) :
    |bellmanExtension E F ell L N p-bellmanExtension E F ell L N q| ≤ K*holderWeight beta p q := by
  obtain ⟨A,hA,heA⟩ := bellmanExtension_attained hE hne hell hL (chu_matrix_continuousOn hF hp) N
  obtain ⟨B,hB,heB⟩ := bellmanExtension_attained hE hne hell hL (chu_matrix_continuousOn hF hq) N
  have hpq := bellmanExtension_le_candidate hE hne hell (chu_matrix_continuousOn hF hp) N hB
  have hqp := bellmanExtension_le_candidate hE hne hell (chu_matrix_continuousOn hF hq) N hA
  rw [heA] at hpq
  rw [heB] at hqp
  have hAc := abs_le.mp (bellmanOffset_time_holder hE hne hF A hp hq)
  have hBc := abs_le.mp (bellmanOffset_time_holder hE hne hF B hp hq)
  rw [heA,heB]
  exact abs_le.mpr ⟨by linarith only [hqp,hAc.1],by linarith only [hpq,hBc.2]⟩

end Yau.LeafProofs.L05Aux
