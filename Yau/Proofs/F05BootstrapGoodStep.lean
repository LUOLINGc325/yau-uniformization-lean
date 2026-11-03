import Yau.Proofs.F05BootstrapGoodQuotientEquation
import Yau.Proofs.F05BootstrapSchauderEquationLimit
import Yau.Proofs.F05BootstrapSourceLimit
import Yau.Proofs.F05BootstrapQuotientSequence
import Yau.Proofs.F05BootstrapBufferedLocalEstimate
import Yau.Proofs.F05BootstrapQuotientTrace

/-! A genuine good derivative gains relative Schauder regularity from
actual first coefficient/source derivatives and current Holder jets.
The quotient solutions and their common estimates are constructed here. -/

open Set Filter
open scoped Topology Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2400000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_good_partial_buffered_upgrade {ν d : Option (RIdx n)}
    {r rb R S sb s T α lam upper M0 MD FD U BQ : ℝ}
    (hd : F05GoodLetter ν d) (hr : 0 < r) (hrrb : r < rb) (hrbR : rb < R) (hR2 : R < 2)
    (hS : 0 < S) (hSsb : S < sb) (hsbs : sb < s) (hsT : s < T)
    (hα : 0 < α) (hα1 : α < 1)
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ) (f v : Point n → ℝ)
    (hv : F05RelC2 (region ν R) (Icc S T) v) (hFace : F05ZeroFace ν T v)
    (hPDE : ∀ z ∈ region ν R ×ˢ Icc S T, F05RelOp (region ν R) (Icc S T) a b v z = f z)
    (hEll : Elliptic (region ν rb ×ˢ Icc sb T) a lam upper)
    (ha : HolderBound α (region ν rb ×ˢ Icc sb T) a M0)
    (hb : ∀ j, HolderBound α (region ν rb ×ˢ Icc sb T) (fun z => b z j) M0)
    (hDa : F05GoodDiffOn T d a (F05PosPatch ν T))
    (hDb : ∀ j, F05GoodDiffOn T d (fun z => b z j) (F05PosPatch ν T))
    (hDf : F05GoodDiffOn T d f (F05PosPatch ν T))
    (hDaH : HolderBound α (region ν R ×ˢ Icc S T) (F05GoodPartial T d a) MD)
    (hDbH : ∀ j, HolderBound α (region ν R ×ˢ Icc S T) (F05GoodPartial T d (fun z => b z j)) MD)
    (hDfH : HolderBound α (region ν R ×ˢ Icc S T) (F05GoodPartial T d f) FD)
    (hH : HolderBound α (region ν R ×ˢ Icc S T) (F05RelDD (region ν R) v) U)
    (hG : HolderBound α (region ν R ×ˢ Icc S T) (F05RelD (region ν R) v) U)
    (hDv : F05GoodDiffOn T d v (F05PosPatch ν T))
    (hDvH : HolderBound α (region ν R ×ˢ Icc S T) (F05GoodPartial T d v) BQ) :
    ∃ C : ℝ, 0 < C ∧ F05RelSchauder α (region ν r) (Icc s T) (F05GoodPartial T d v) C ∧
      ∀ z ∈ region ν r ×ˢ Icc s T,
        F05RelOp (region ν r) (Icc s T) a b (F05GoodPartial T d v) z =
          F05FirstGoodSource T d (region ν R) a b f v z := by
  let η := min (R-rb) (sb-S)/2
  have hη : 0 < η := by dsimp only [η]; exact div_pos (lt_min (sub_pos.mpr hrbR) (sub_pos.mpr hSsb)) (by norm_num)
  let h := F05QuotientScale η
  have hh : ∀ k, 0 < h k := F05_quotient_scale_pos hη
  have hZero : Tendsto h atTop (𝓝 0) := F05_quotient_scale_tendsto η
  have hSpace (k : ℕ) : h k ≤ R-rb := by
    have hLe := F05_quotient_scale_le hη.le k
    have hMin := min_le_left (R-rb) (sb-S)
    dsimp only [η] at hLe
    linarith
  have hTime (k : ℕ) : h k ≤ sb-S := by
    have hLe := F05_quotient_scale_le hη.le k
    have hMin := min_le_right (R-rb) (sb-S)
    dsimp only [η] at hLe
    linarith
  let Q := region ν rb ×ˢ Icc sb T
  let K := region ν R ×ˢ Icc S T
  have hQ : Q ⊆ K := fun z hz => ⟨F05_region_mono hrbR.le hz.1,hSsb.le.trans hz.2.1,hz.2.2⟩
  have hSegment : ∀ k p, p ∈ Q → ∀ θ ∈ Icc (0 : ℝ) 1, F05GoodSegment d (h k) p θ ∈ F05PosPatch ν T := by
    intro k p hp θ hθ
    exact (F05_good_segment_buffered hd (hh k).le (hSpace k) (hTime k) hS hR2 hp hθ).2
  have hIn : ∀ k p, p ∈ Q → ∀ θ ∈ Icc (0 : ℝ) 1, F05GoodSegment d (h k) p θ ∈ K := by
    intro k p hp θ hθ
    exact (F05_good_segment_buffered hd (hh k).le (hSpace k) (hTime k) hS hR2 hp hθ).1
  have hSource := F05_good_quotient_source_common_limit hα hh hZero hQ hSegment hIn
    (region ν R) hDa hDb hDf hDaH hDbH hDfH hH hG
  have hValue := F05_good_quotients_uniform_limit hα hh hZero hDv hSegment hIn hDvH
  let χ : ContDiffBump (0 : Space n) :=
    ⟨(2*r+rb)/3,(r+2*rb)/3,by linarith,by linarith⟩
  have hχ : χ.rOut ≤ rb := by dsimp only [χ]; linarith
  have hrχ : r < χ.rIn := by dsimp only [χ]; linarith
  obtain ⟨CE,hCE,hEstimate⟩ := F05_buffered_physical_local_schauder
    (M := M0) (lam := lam) (upper := upper) ν χ hχ hα hα1 ha.1 hr hrχ hsbs
  let LF := linearizedSourceBudget n FD MD U
  have hLF : 0 ≤ LF := (hSource.1 0).1
  have hBQ : 0 ≤ BQ := hDvH.1
  let C := 1+CE*(BQ+LF)
  have hC : 0 < C := by dsimp only [C]; positivity
  have hCScale : CE*(BQ+LF) ≤ C := by dsimp only [C]; linarith
  have hq (k : ℕ) := F05_relative_good_quotient_equation hd (hr.trans hrrb) hrbR hR2
    hS hSsb (hsbs.trans hsT) (hh k) (hSpace k) (hTime k) hv a b hPDE
  have hqEstimate (k : ℕ) : F05RelSchauder α (region ν r) (Icc s T) (F05GoodQuotient d (h k) v) (CE*(BQ+LF)) := by
    apply hEstimate T a b (F05GoodQuotientSource d (h k) (region ν R) a b f v)
      (F05GoodQuotient d (h k) v) LF BQ hsT hEll ha hb (hSource.1 k) (hq k).1
    · intro z hz
      simpa only [Real.norm_eq_abs] using (hValue.1 k).2.1 z hz
    · exact F05_good_quotient_zero_receiving_face hd (hh k).le (hSpace k) (hTime k) hS hR2 hFace
    · exact (hq k).2
  have hqSch (k : ℕ) : F05RelSchauder α (region ν r) (Icc s T) (F05GoodQuotient d (h k) v) C :=
    ⟨(hqEstimate k).1,holderBound_mono_const (hqEstimate k).2.1 hCScale,
      holderBound_mono_const (hqEstimate k).2.2.1 hCScale,holderBound_mono_const (hqEstimate k).2.2.2 hCScale⟩
  have hSpaceSub : region ν r ⊆ region ν rb := F05_region_mono hrrb.le
  have hTimeSub : Icc s T ⊆ Icc sb T := fun t ht => ⟨hsbs.le.trans ht.1,ht.2⟩
  have hSub : region ν r ×ˢ Icc s T ⊆ Q := prod_mono hSpaceSub hTimeSub
  have hEqRecv : ∀ k z, z ∈ region ν r ×ˢ Icc s T →
      F05RelOp (region ν r) (Icc s T) a b (F05GoodQuotient d (h k) v) z =
        F05GoodQuotientSource d (h k) (region ν R) a b f v z := by
    intro k z hz
    have hJets := F05_relative_restriction_jets (F05_region_uniqueDiffOn ν (hr.trans hrrb))
      (F05_region_uniqueDiffOn ν hr) (uniqueDiffOn_Icc hsT) hSpaceSub hTimeSub (hq k).1 hz
    simpa only [F05RelOp,hJets.1,hJets.2.1,hJets.2.2] using (hq k).2 z (hSub hz)
  have hClosed := F05_relSchauder_equation_limit ν hr hsT hα a b hqSch (hValue.2.mono hSub)
    (fun z hz => hSource.2 z (hSub hz)) hEqRecv
  exact ⟨C,hC,hClosed.1,hClosed.2⟩

end Yau.Proofs.F05Aux
