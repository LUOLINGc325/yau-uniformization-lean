import Yau.Proofs.F05BootstrapGoodStep
import Yau.Proofs.F05BootstrapLocalBounds
import Yau.Proofs.F05BootstrapZeroTrace

/-! A first actual good derivative of a local relative Schauder solution
is itself locally Schauder and satisfies the full differentiated equation.
All quantitative data used by the quotient construction are derived from
the displayed local Holder fields; no smooth coefficient assumption enters. -/

open Set
open scoped Topology Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2400000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_good_partial_local_schauder {ν d : Option (RIdx n)} {T α lam upper : ℝ}
    (hT : 0 < T) (hα : 0 < α) (hα1 : α < 1) (hd : F05GoodLetter ν d)
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ) (f v : Point n → ℝ)
    (hv : F05LocalSchauder α ν T v) (hFace : F05ZeroFace ν T v)
    (hEll : Elliptic (F05PosPatch ν T) a lam upper)
    (ha : F05LocalHolder α ν T a) (hb : ∀ j, F05LocalHolder α ν T (fun z => b z j))
    (hf : F05LocalHolder α ν T f)
    (hDa : F05GoodDiffOn T d a (F05PosPatch ν T))
    (hDb : ∀ j, F05GoodDiffOn T d (fun z => b z j) (F05PosPatch ν T))
    (hDf : F05GoodDiffOn T d f (F05PosPatch ν T))
    (hDaH : F05LocalHolder α ν T (F05GoodPartial T d a))
    (hDbH : ∀ j, F05LocalHolder α ν T (F05GoodPartial T d (fun z => b z j)))
    (hDfH : F05LocalHolder α ν T (F05GoodPartial T d f))
    (hPDE : ∀ z ∈ F05PosPatch ν T,
      F05RelOp (F05PosSpace ν) (Ioc 0 T) a b v z = f z) :
    F05LocalSchauder α ν T (F05GoodPartial T d v) ∧
      F05ZeroFace ν T (F05GoodPartial T d v) ∧
      ∀ z ∈ F05PosPatch ν T,
        F05RelOp (F05PosSpace ν) (Ioc 0 T) a b (F05GoodPartial T d v) z =
          F05FirstGoodSource T d (F05PosSpace ν) a b f v z := by
  have hvGlobal := F05_local_schauder_to_relative hv
  have hDv := F05_local_schauder_good_diff hd hv
  have hDvHolder := F05_local_schauder_good_holder hd hv
  have hLocal (r : ℝ) (hr : 0 < r) (hr2 : r < 2) (s : ℝ) (hs : 0 < s) (hsT : s < T) :
      ∃ C : ℝ, 0 < C ∧ F05RelSchauder α (region ν r) (Icc s T) (F05GoodPartial T d v) C ∧
        ∀ z ∈ region ν r ×ˢ Icc s T,
          F05RelOp (region ν r) (Icc s T) a b (F05GoodPartial T d v) z =
            F05FirstGoodSource T d (F05PosSpace ν) a b f v z := by
    let R := (r+2)/2
    let rb := (r+R)/2
    let S := s/4
    let sb := s/2
    have hR : 0 < R := by dsimp only [R]; linarith
    have hR2 : R < 2 := by dsimp only [R]; linarith
    have hrR : r < R := by dsimp only [R]; linarith
    have hrb : 0 < rb := by dsimp only [rb]; positivity
    have hrrb : r < rb := by dsimp only [rb]; linarith
    have hrbR : rb < R := by dsimp only [rb]; linarith
    have hrb2 : rb < 2 := hrbR.trans hR2
    have hS : 0 < S := by dsimp only [S]; positivity
    have hST : S < T := by dsimp only [S]; linarith
    have hsb : 0 < sb := by dsimp only [sb]; positivity
    have hsbT : sb < T := by dsimp only [sb]; linarith
    have hSsb : S < sb := by dsimp only [S,sb]; linarith
    have hsbs : sb < s := by dsimp only [sb]; linarith
    obtain ⟨CV,hCV,hVSch⟩ := hv R hR hR2 S hS hST
    obtain ⟨CA,hCA,hA⟩ := ha rb hrb hrb2 sb hsb hsbT
    obtain ⟨CB,hCB,hB⟩ := F05_holder_finite_common (fun j => hb j rb hrb hrb2 sb hsb hsbT)
    obtain ⟨CDA,hCDA,hDA⟩ := hDaH R hR hR2 S hS hST
    obtain ⟨CDB,hCDB,hDB⟩ := F05_holder_finite_common (fun j => hDbH j R hR hR2 S hS hST)
    obtain ⟨CDF,hCDF,hDF⟩ := hDfH R hR hR2 S hS hST
    obtain ⟨BQ,hBQ,hVd⟩ := hDvHolder R hR hR2 S hS hST
    let M0 := max CA CB
    let MD := max CDA CDB
    have hEllLocal : Elliptic (region ν rb ×ˢ Icc sb T) a lam upper :=
      ⟨hEll.1,hEll.2.1,fun z hz => hEll.2.2 z (F05_receiving_subset_posPatch ν hrb2 hsb hz)⟩
    have hSpace : region ν R ⊆ F05PosSpace ν := F05_region_subset_posSpace ν hR2
    have hI : Icc S T ⊆ Ioc 0 T := fun t ht => ⟨hS.trans_le ht.1,ht.2⟩
    have hOrigJets (z : Point n) (hz : z ∈ region ν R ×ˢ Icc S T) :=
      F05_relative_restriction_jets (F05_posSpace_uniqueDiffOn ν) (F05_region_uniqueDiffOn ν hR)
        (uniqueDiffOn_Icc hST) hSpace hI hvGlobal hz
    have hEqLocal : ∀ z ∈ region ν R ×ˢ Icc S T,
        F05RelOp (region ν R) (Icc S T) a b v z = f z := by
      intro z hz
      have hJets := hOrigJets z hz
      simpa only [F05RelOp,hJets.1,hJets.2.1,hJets.2.2] using hPDE z ⟨hSpace hz.1,hI hz.2⟩
    obtain ⟨C,hC,hSch,hEquation⟩ := F05_good_partial_buffered_upgrade (M0 := M0) (MD := MD) hd hr hrrb hrbR hR2
      hS hSsb hsbs hsT hα hα1 a b f v hVSch.1 hFace hEqLocal hEllLocal
      (holderBound_mono_const hA (le_max_left _ _))
      (fun j => holderBound_mono_const (hB j) (le_max_right _ _)) hDa hDb hDf
      (holderBound_mono_const hDA (le_max_left _ _))
      (fun j => holderBound_mono_const (hDB j) (le_max_right _ _)) hDF hVSch.2.2.1
      (holderBound_snd hVSch.2.1) hDv hVd
    refine ⟨C,hC,hSch,?_⟩
    intro z hz
    have hzOrig : z ∈ region ν R ×ˢ Icc S T :=
      ⟨F05_region_mono hrR.le hz.1,by dsimp only [S]; linarith [hz.2.1],hz.2.2⟩
    have hJets := hOrigJets z hzOrig
    simpa only [F05FirstGoodSource,hJets.1,hJets.2.1] using hEquation z hz
  have hw : F05LocalSchauder α ν T (F05GoodPartial T d v) := by
    intro r hr hr2 s hs hsT
    obtain ⟨C,hC,hSch,hEquation⟩ := hLocal r hr hr2 s hs hsT
    exact ⟨C,hC,hSch⟩
  refine ⟨hw,F05_good_partial_zero_face hd hFace,?_⟩
  have hwGlobal := F05_local_schauder_to_relative hw
  intro z hz
  have hn : ‖z.1‖ < 2 := by simpa only [Metric.mem_ball,dist_zero_right] using hz.1.2
  let r := (‖z.1‖+2)/2
  let s := z.2/2
  have hr : 0 < r := by dsimp only [r]; linarith [norm_nonneg z.1]
  have hr2 : r < 2 := by dsimp only [r]; linarith
  have hs : 0 < s := by dsimp only [s]; linarith [hz.2.1]
  have hsT : s < T := by dsimp only [s]; linarith [hz.2.1,hz.2.2]
  have hzLocal : z ∈ region ν r ×ˢ Icc s T :=
    ⟨F05_posSpace_mem_region hz.1 (by dsimp only [r]; linarith),by dsimp only [s]; linarith [hz.2.1],hz.2.2⟩
  obtain ⟨C,hC,hSch,hEquation⟩ := hLocal r hr hr2 s hs hsT
  have hLocalTime : Icc s T ⊆ Ioc 0 T := fun t ht => ⟨hs.trans_le ht.1,ht.2⟩
  have hJets := F05_relative_restriction_jets (F05_posSpace_uniqueDiffOn ν) (F05_region_uniqueDiffOn ν hr)
    (uniqueDiffOn_Icc hsT) (F05_region_subset_posSpace ν hr2) hLocalTime hwGlobal hzLocal
  simpa only [F05RelOp,hJets.1,hJets.2.1,hJets.2.2] using hEquation z hzLocal

end Yau.Proofs.F05Aux
