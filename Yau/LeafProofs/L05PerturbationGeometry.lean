import Yau.Blueprint.ParabolicSpaces

open Set Metric Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 800000
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

def perturbClosed {n : ℕ} (c : Space n) (R T : ℝ) : Set (Point n) :=
  closedBall c R ×ˢ Icc (T-R^2) T
def perturbOpen {n : ℕ} (c : Space n) (R T : ℝ) : Set (Point n) :=
  ball c R ×ˢ Ioo (T-R^2) T
def perturbBack {n : ℕ} (c : Space n) (R T : ℝ) : Set (Point n) :=
  ball c R ×ˢ Ioc (T-R^2) T
def perturbBoundary {n : ℕ} (c : Space n) (R T : ℝ) : Set (Point n) :=
  (closedBall c R ×ˢ ({T-R^2} : Set ℝ)) ∪ (sphere c R ×ˢ Icc (T-R^2) T)
def perturbScale {n : ℕ} (r : ℝ) (p : Point n) : Point n := (r • p.1,r^2*p.2)
def perturbCenter {n : ℕ} (z : Point n) (r : ℝ) (p : Point n) : Point n :=
  (z.1+r • p.1,z.2+r^2*p.2)
def perturbCore {n : ℕ} (tau : ℝ) : Set (Point n) :=
  closedBall 0 (1/2-tau) ×ˢ Icc (-(1/2 : ℝ)^2+tau^2) 0
def perturbCoreOpen {n : ℕ} (tau : ℝ) : Set (Point n) :=
  ball 0 (1/2-tau) ×ˢ Ioo (-(1/2 : ℝ)^2+tau^2) 0
def perturbCoreBoundary {n : ℕ} (tau : ℝ) : Set (Point n) :=
  (closedBall 0 (1/2-tau) ×ˢ ({-(1/2 : ℝ)^2+tau^2} : Set ℝ)) ∪
  (sphere 0 (1/2-tau) ×ˢ Icc (-(1/2 : ℝ)^2+tau^2) 0)
def perturbCollar {n : ℕ} (tau : ℝ) : Set (Point n) :=
  {p | p ∈ perturbClosed (0 : Space n) (1/2) 0 ∧
    ((1/2-tau ≤ ‖p.1‖) ∨ p.2 ≤ -(1/2 : ℝ)^2+tau^2)}

theorem perturbClosed_compact {n : ℕ} (c : Space n) (R T : ℝ) :
    IsCompact (perturbClosed c R T) := (isCompact_closedBall c R).prod isCompact_Icc

theorem perturbOpen_isOpen {n : ℕ} (c : Space n) (R T : ℝ) :
    IsOpen (perturbOpen c R T) := isOpen_ball.prod isOpen_Ioo

theorem perturbBack_zero {n : ℕ} (R : ℝ) :
    perturbBack (0 : Space n) R 0 = backward R := by simp [perturbBack,backward]

theorem perturbOpen_subset_back {n : ℕ} (c : Space n) (R T : ℝ) :
    perturbOpen c R T ⊆ perturbBack c R T := fun _ h => ⟨h.1,h.2.1,h.2.2.le⟩

theorem perturbBack_subset_closed {n : ℕ} (c : Space n) (R T : ℝ) :
    perturbBack c R T ⊆ perturbClosed c R T :=
  fun _ h => ⟨ball_subset_closedBall h.1,h.2.1.le,h.2.2⟩

theorem perturbBoundary_subset_closed {n : ℕ} (c : Space n) (R T : ℝ) :
    perturbBoundary c R T ⊆ perturbClosed c R T := by
  intro p hp
  rcases hp with hp | hp
  · have he : p.2=T-R^2 := mem_singleton_iff.mp hp.2
    refine ⟨hp.1,by rw [he],?_⟩
    rw [he]
    linarith [sq_nonneg R]
  · exact ⟨sphere_subset_closedBall hp.1,hp.2⟩

theorem perturbScale_continuous {n : ℕ} (r : ℝ) : Continuous (perturbScale (n := n) r) := by
  unfold perturbScale
  fun_prop

theorem perturbCenter_continuous {n : ℕ} (z : Point n) (r : ℝ) :
    Continuous (perturbCenter z r) := by unfold perturbCenter; fun_prop

theorem perturbCenter_zero {n : ℕ} (z : Point n) (r : ℝ) : perturbCenter z r (0,0)=z := by
  simp [perturbCenter]

theorem perturbScale_zero {n : ℕ} (r : ℝ) : perturbScale (n := n) r (0,0)=(0,0) := by
  simp [perturbScale]

theorem perturbScale_one {n : ℕ} (p : Point n) : perturbScale 1 p=p := by simp [perturbScale]

theorem perturbScale_comp {n : ℕ} (r s : ℝ) (p : Point n) :
    perturbScale r (perturbScale s p)=perturbScale (r*s) p := by
  simp only [perturbScale,smul_smul,mul_pow,mul_assoc]

theorem perturb_center_closed_subset {n : ℕ} {z : Point n}
    (hz : z ∈ backward (3/4)) {r : ℝ} (hr : 0<r) (hrb : r≤1/16) :
    perturbClosed z.1 r z.2 ⊆ backward 1 := by
  intro p hp
  have hzN : ‖z.1‖ < (3/4 : ℝ) := by simpa using hz.1
  have hpN : ‖p.1-z.1‖ ≤ r := by simpa only [mem_closedBall,dist_eq_norm] using hp.1
  have htri : ‖p.1‖ ≤ ‖p.1-z.1‖+‖z.1‖ := by
    simpa only [sub_add_cancel] using norm_add_le (p.1-z.1) z.1
  refine ⟨by simpa using (show ‖p.1‖ < (1 : ℝ) by linarith),?_,hp.2.2.trans hz.2.2⟩
  have ht := hp.2.1
  have hzt := hz.2.1
  change -(1 : ℝ)^2 < p.2
  norm_num at hzt ⊢
  nlinarith

theorem perturbCore_compact {n : ℕ} (tau : ℝ) : IsCompact (perturbCore (n := n) tau) :=
  (isCompact_closedBall _ _).prod isCompact_Icc

theorem perturbCoreOpen_isOpen {n : ℕ} (tau : ℝ) : IsOpen (perturbCoreOpen (n := n) tau) :=
  isOpen_ball.prod isOpen_Ioo

theorem perturbCore_subset_closed {n : ℕ} {tau : ℝ} (ht : 0≤tau) :
    perturbCore (n := n) tau ⊆ perturbClosed (0 : Space n) (1/2) 0 := by
  intro p hp
  refine ⟨?_,?_,hp.2.2⟩
  · exact closedBall_subset_closedBall (show (1/2 : ℝ)-tau≤1/2 by linarith) hp.1
  · have hh := hp.2.1
    change 0-(1/2 : ℝ)^2 ≤ p.2
    nlinarith [sq_nonneg tau]

theorem perturb_closed_core_or_collar {n : ℕ} (tau : ℝ) {p : Point n}
    (hp : p ∈ perturbClosed (0 : Space n) (1/2) 0) :
    p ∈ perturbCore tau ∨ p ∈ perturbCollar tau := by
  by_cases hx : ‖p.1‖ ≤ 1/2-tau
  · by_cases ht : -(1/2 : ℝ)^2+tau^2 ≤ p.2
    · exact Or.inl ⟨by simpa using hx,ht,hp.2.2⟩
    · exact Or.inr ⟨hp,Or.inr (le_of_not_ge ht)⟩
  · exact Or.inr ⟨hp,Or.inl (le_of_not_ge hx)⟩

theorem perturb_core_aspect {tau : ℝ} (ht : 0<tau) (hb : tau≤1/8) :
    0 < (1/2 : ℝ)-tau ∧ 0 < (1/2 : ℝ)^2-tau^2 ∧
      1 ≤ ((1/2 : ℝ)^2-tau^2)/((1/2 : ℝ)-tau)^2 ∧
      ((1/2 : ℝ)^2-tau^2)/((1/2 : ℝ)-tau)^2 ≤ 2 := by
  have hp : 0 < (1/2 : ℝ)-tau := by linarith
  have hs : 0 < ((1/2 : ℝ)-tau)^2 := sq_pos_of_pos hp
  refine ⟨hp,by nlinarith,?_,?_⟩
  · apply (le_div_iff₀ hs).mpr
    nlinarith
  · apply (div_le_iff₀ hs).mpr
    nlinarith

end Yau.LeafProofs.L05Aux
