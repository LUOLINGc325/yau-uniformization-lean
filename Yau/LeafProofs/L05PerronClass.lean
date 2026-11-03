import Yau.LeafProofs.L05PerronStability
import Yau.LeafProofs.L05PerronSemicontComparison
import Yau.LeafProofs.L05PerronBarriers

noncomputable section

open Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

def perronClass {n : ℕ} (F : Sym n → ℝ) (G : Point n → ℝ) (B : ℝ) : Set (Point n → ℝ) :=
  {w | UpperSemicontinuousOn w (perronSlab n) ∧
    (∀ p ∈ perronSlab n, -B ≤ w p ∧ w p ≤ B) ∧
    (∀ p ∈ perronBoundary n, w p ≤ G p) ∧
    viscositySub (perronOpen n) (fun H _ => F H) (fun _ => 0) w}

def perronUpperSolution {n : ℕ} (F : Sym n → ℝ) (G : Point n → ℝ) (B : ℝ) : Point n → ℝ :=
  perronUpper (perronSlab n) (perronFamilySup (perronClass F G B))

theorem perron_slab_subset_closed {n : ℕ} : perronSlab n ⊆ abpClosed n 1 (-1) 1 :=
  fun _ hp => ⟨hp.1,hp.2.1,hp.2.2.le⟩

theorem perron_class_nonempty {n : ℕ} {ell L : ℝ} {F : Sym n → ℝ}
    (hell : 0 < ell) (hE : globalElliptic F ell L) (h0 : F 0=0)
    {G : Point n → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hbG : ∀ p ∈ perronSlab n, |G p| ≤ B) : (perronClass F G B).Nonempty := by
  refine ⟨(fun _ => -B),continuous_const.continuousOn.upperSemicontinuousOn,?_,?_,?_⟩
  · intro p hp
    exact ⟨le_rfl,by linarith⟩
  · intro p hp
    exact (abs_le.mp (hbG p (perronBoundary_subset_slab hp))).1
  · exact (perron_constant_solution hell hE h0 (perronOpen n) (-B)).1

theorem perron_class_abs {n : ℕ} {F : Sym n → ℝ} {G : Point n → ℝ} {B : ℝ} :
    ∀ w ∈ perronClass F G B, ∀ p ∈ perronSlab n, |w p| ≤ B := by
  intro w hw p hp
  exact abs_le.mpr (hw.2.1 p hp)

theorem perron_upperSolution_bounds {n : ℕ} {F : Sym n → ℝ} {G : Point n → ℝ} {B : ℝ}
    (hne : (perronClass F G B).Nonempty) :
    ∀ p ∈ perronSlab n, |perronUpperSolution F G B p| ≤ B := by
  intro p hp
  have hb : ∀ q ∈ perronSlab n, |perronFamilySup (perronClass F G B) q| ≤ B :=
    fun q hq => perron_familySup_bounds hne perron_class_abs hq
  exact (perron_upper_bounds hb hp).2

theorem perron_upperSolution_sub {n : ℕ} {F : Sym n → ℝ} {G : Point n → ℝ} {B : ℝ}
    (hF : Continuous F) (hB : 0 ≤ B) (hne : (perronClass F G B).Nonempty) :
    viscositySub (perronOpen n) (fun H _ => F H) (fun _ => 0) (perronUpperSolution F G B) :=
  perron_upperSup_sub (perronOpen_isOpen n) perronOpen_subset_slab hF hne hB perron_class_abs
    (fun _ hw => hw.1) (fun _ hw => hw.2.2.2)

theorem perron_upperSolution_usc {n : ℕ} {F : Sym n → ℝ} {G : Point n → ℝ} {B : ℝ}
    (hne : (perronClass F G B).Nonempty) :
    UpperSemicontinuousOn (perronUpperSolution F G B) (perronSlab n) :=
  perron_upper_usc (fun q hq => perron_familySup_bounds hne perron_class_abs hq)

theorem perron_class_le_upperSolution {n : ℕ} {F : Sym n → ℝ} {G : Point n → ℝ} {B : ℝ}
    (hne : (perronClass F G B).Nonempty) {w : Point n → ℝ} (hw : w ∈ perronClass F G B) :
    ∀ p ∈ perronSlab n, w p ≤ perronUpperSolution F G B p := by
  intro p hp
  have hb : ∀ q ∈ perronSlab n, |perronFamilySup (perronClass F G B) q| ≤ B :=
    fun q hq => perron_familySup_bounds hne perron_class_abs hq
  exact (perron_member_le_familySup perron_class_abs hw hp).trans (perron_upper_bounds hb hp).1

set_option maxHeartbeats 1400000 in
theorem perron_upperSolution_boundary {n : ℕ} (hn : 0 < n) {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) {F : Sym n → ℝ}
    (hF : Continuous F) (hE : globalElliptic F ell L) (h0 : F 0=0)
    {G : Point n → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hG : ContinuousOn G (abpClosed n 1 (-1) 1))
    (hbG : ∀ q ∈ abpClosed n 1 (-1) 1, |G q| ≤ B)
    (hne : (perronClass F G B).Nonempty) :
    ∀ p ∈ perronBoundary n, perronUpperSolution F G B p ≤ G p := by
  have hbU : ∀ q ∈ perronSlab n, |perronFamilySup (perronClass F G B) q| ≤ B :=
    fun q hq => perron_familySup_bounds hne perron_class_abs hq
  intro p hp
  apply le_of_forall_pos_le_add
  intro eps heps
  obtain ⟨l,h,hl,hh,hlp,hhp,hdom,hlSub,hhSuper⟩ :=
    perron_boundary_barriers hn hell hL hE h0 hB hG hbG hp heps
  have hD : IsCompact (abpClosed n 1 (-1) 1) :=
    (isCompact_closedBall (0 : Space n) 1).prod isCompact_Icc
  obtain ⟨C,hC⟩ := hD.bddAbove_image hh.continuous.norm.continuousOn
  have hboundH (q : Point n) (hq : q ∈ perronSlab n) : |h q| ≤ C := by
    simpa only [Real.norm_eq_abs] using hC (Set.mem_image_of_mem (fun q => ‖h q‖) (perron_slab_subset_closed hq))
  have hcompare (w : Point n → ℝ) (hw : w ∈ perronClass F G B) :
      ∀ q ∈ perronSlab n, w q ≤ h q := by
    apply perron_semicont_compare hn hell hL hF hE hw.1 hh.continuous.continuousOn.lowerSemicontinuousOn
    · refine ⟨B+|C|+1,by positivity,?_⟩
      intro q hq
      have hbw := perron_class_abs w hw q hq
      have hbh := hboundH q hq
      constructor <;> linarith [le_abs_self C,abs_nonneg C]
    · exact hw.2.2.2
    · exact hhSuper
    · intro q hq
      exact (hw.2.2.1 q hq).trans (hdom q (perron_slab_subset_closed (perronBoundary_subset_slab hq))).2
  have hUsup : ∀ q ∈ perronSlab n, perronFamilySup (perronClass F G B) q ≤ h q := by
    intro q hq
    obtain ⟨w,hw⟩ := hne
    apply csSup_le (show ({r | ∃ w ∈ perronClass F G B, r=w q} : Set ℝ).Nonempty from ⟨w q,w,hw,rfl⟩)
    rintro r ⟨v,hv,rfl⟩
    exact hcompare v hv q hq
  have hUpper := perron_upper_le_continuous hbU hh.continuous.continuousOn hUsup (perronBoundary_subset_slab hp)
  rw [hhp] at hUpper
  exact hUpper

theorem perron_upperSolution_member {n : ℕ} (hn : 0 < n) {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) {F : Sym n → ℝ}
    (hF : Continuous F) (hE : globalElliptic F ell L) (h0 : F 0=0)
    {G : Point n → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hG : ContinuousOn G (abpClosed n 1 (-1) 1))
    (hbG : ∀ q ∈ abpClosed n 1 (-1) 1, |G q| ≤ B)
    (hne : (perronClass F G B).Nonempty) :
    perronUpperSolution F G B ∈ perronClass F G B := by
  refine ⟨perron_upperSolution_usc hne,?_,
    perron_upperSolution_boundary hn hell hL hF hE h0 hB hG hbG hne,
    perron_upperSolution_sub hF hB hne⟩
  intro p hp
  exact abs_le.mp (perron_upperSolution_bounds hne p hp)

end Yau.LeafProofs.L05Aux
