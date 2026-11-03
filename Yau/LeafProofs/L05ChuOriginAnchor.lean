import Yau.LeafProofs.L05ChuAnchorGeometry
import Yau.LeafProofs.L05ChuGlobalContinuity
import Yau.LeafProofs.L05JetCombinationMatrix

noncomputable section

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

def chuOriginAnchorBound (n : ℕ) (L M fB uB : ℝ) : ℝ :=
  chuAnchorScale uB/2+fB+2*chuAnchorScale uB*(2*n)*L+2*M

theorem chuOriginAnchorBound_pos (n : ℕ) {L M fB uB : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hfB : 0 ≤ fB) (huB : 0 ≤ uB) :
    0 < chuOriginAnchorBound n L M fB uB := by unfold chuOriginAnchorBound chuAnchorScale; positivity

set_option maxHeartbeats 1800000 in
theorem chu_operator_origin_bound {n : ℕ} {ell L M beta fB uB : ℝ}
    (hell : 0 ≤ ell) (hM : 0 ≤ M) (hb : 0 ≤ beta) (huB : 0 ≤ uB)
    {Phi : Sym n → Point n → ℝ}
    (hE : ∀ p ∈ backward 1, globalElliptic (fun H => Phi H p) ell L)
    (hVar : ∀ p ∈ backward 1, |Phi 0 p-Phi 0 (0,0)| ≤ M*holderWeight beta p (0,0))
    {u f : Point n → ℝ} (hu : C2 (backward 1) u)
    (hub : ∀ p ∈ backward 1, |u p| ≤ uB) (hfb : ∀ p ∈ backward 1, |f p| ≤ fB)
    (hPDE : ∀ p ∈ backward 1, timeD (backward 1) u p-Phi (hessian u p) p=f p) :
    |Phi 0 (0,0)| ≤ chuOriginAnchorBound n L M fB uB := by
  let a := chuAnchorScale uB
  have ha : 0 < a := by dsimp only [a,chuAnchorScale]; positivity
  have hD := @chuAnchorDomain_subset_backward n
  obtain ⟨p,hp,hminP⟩ := chuAnchor_minimum huB (hu.1.mono hD) (fun p hp => hub p (hD hp))
  obtain ⟨q,hq,hminQ⟩ := chuAnchor_minimum huB (hu.1.neg.mono hD)
    (fun q hq => by simpa only [Pi.neg_apply,abs_neg] using hub q (hD hq))
  have hpU := chuAnchorOpen_subset_unitOpen hp
  have hqU := chuAnchorOpen_subset_unitOpen hq
  have hpB := chu_unitOpen_subset_backward hpU
  have hqB := chu_unitOpen_subset_backward hqU
  have hUopen : IsOpen (unitOpen n) := Metric.isOpen_ball.prod isOpen_Ioo
  have huU := c2_open_restrict hUopen chu_unitOpen_subset_backward hu
  have hPj := parabolic_touchBelow_jets hUopen huU hpU
    ((chuAnchorLowerTest_smooth a u p).contDiffAt.of_le (by simp)) (chuAnchorLowerTest_touch hminP)
  have hQj := parabolic_touchAbove_jets hUopen huU hqU
    ((chuAnchorUpperTest_smooth a u q).contDiffAt.of_le (by simp)) (chuAnchorUpperTest_touch hminQ)
  have hPt : timeD (backward 1) u p= -2*a*(p.2+(1/2:ℝ)) := by
    calc
      _=timeD (unitOpen n) u p := (timeD_open_restrict hUopen chu_unitOpen_subset_backward u hpU).symm
      _=timeD Set.univ (chuAnchorLowerTest a u p) p := hPj.1
      _=_ := chuAnchorLowerTest_timeD a u p
  have hQt : timeD (backward 1) u q=2*a*(q.2+(1/2:ℝ)) := by
    calc
      _=timeD (unitOpen n) u q := (timeD_open_restrict hUopen chu_unitOpen_subset_backward u hqU).symm
      _=timeD Set.univ (chuAnchorUpperTest a u q) q := hQj.1
      _=_ := chuAnchorUpperTest_timeD a u q
  have hPH := hPj.2
  have hQH := hQj.2
  rw [chuAnchorLowerTest_hessian] at hPH
  rw [chuAnchorUpperTest_hessian] at hQH
  have hmatP : ((hessian u p : Mat n)+(2*a) • (1 : Mat n)-(0 : Mat n)).PosSemidef := by
    simpa only [sub_neg_eq_add,sub_zero] using hPH
  have hmatQ : ((0 : Mat n)+(2*a) • (1 : Mat n)-(hessian u q : Mat n)).PosSemidef := by
    simpa only [zero_add] using hQH
  have hPG := jet_elliptic_le_of_matrix_le (X := (0 : Sym n)) (H := hessian u p) hell
    (hE p hpB) (by positivity : 0 ≤ 2*a) hmatP
  have hQG := jet_elliptic_le_of_matrix_le (X := hessian u q) (H := (0 : Sym n)) hell
    (hE q hqB) (by positivity : 0 ≤ 2*a) hmatQ
  have hplo : -(1/4:ℝ) ≤ p.2+(1/2:ℝ) := by linarith only [hp.2.1]
  have hqlo : -(1/4:ℝ) ≤ q.2+(1/2:ℝ) := by linarith only [hq.2.1]
  have hpm := mul_le_mul_of_nonneg_left hplo (show 0 ≤ 2*a by positivity)
  have hqm := mul_le_mul_of_nonneg_left hqlo (show 0 ≤ 2*a by positivity)
  have hptop : timeD (backward 1) u p ≤ a/2 := by rw [hPt]; nlinarith only [hpm]
  have hqbottom : -a/2 ≤ timeD (backward 1) u q := by rw [hQt]; nlinarith only [hqm]
  have hVp := abs_le.mp ((hVar p hpB).trans
    (mul_le_mul_of_nonneg_left (holderWeight_backward_origin_le_two hb hpB) hM))
  have hVq := abs_le.mp ((hVar q hqB).trans
    (mul_le_mul_of_nonneg_left (holderWeight_backward_origin_le_two hb hqB) hM))
  have hfp := abs_le.mp (hfb p hpB)
  have hfq := abs_le.mp (hfb q hqB)
  have hP := hPDE p hpB
  have hQ := hPDE q hqB
  change |Phi 0 (0,0)| ≤ a/2+fB+2*a*(2*n)*L+2*M
  exact abs_le.mpr ⟨by linarith only [hQG,hQ,hqbottom,hfq.2,hVq.2],
    by linarith only [hPG,hP,hptop,hfp.1,hVp.1]⟩

end Yau.LeafProofs.L05Aux
