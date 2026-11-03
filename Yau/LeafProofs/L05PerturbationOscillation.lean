import Yau.LeafProofs.L05PerturbationScaledOscillation
import Yau.LeafProofs.L05PerturbationOscillationSequence

open Filter MeasureTheory Set Metric
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

def perturbOscillation {n : ℕ} (c : Space n) (R T : ℝ) (w : Point n → ℝ) : ℝ :=
  sSup (w '' perturbClosed c R T)-sInf (w '' perturbClosed c R T)

theorem perturb_closed_nonempty {n : ℕ} (c : Space n) {R : ℝ} (hR : 0 ≤ R) (T : ℝ) :
    (perturbClosed c R T).Nonempty :=
  ⟨(c,T),mem_closedBall_self hR,sub_le_self T (sq_nonneg R),le_rfl⟩

theorem perturb_closed_subset_radius {n : ℕ} (c : Space n) {S R : ℝ}
    (hS : 0 ≤ S) (hSR : S ≤ R) (T : ℝ) :
    perturbClosed c S T ⊆ perturbClosed c R T := by
  intro p hp
  refine ⟨closedBall_subset_closedBall hSR hp.1,?_,hp.2.2⟩
  have ht : T-S^2 ≤ p.2 := hp.2.1
  nlinarith

theorem perturb_open_subset_radius {n : ℕ} (c : Space n) {S R : ℝ}
    (hS : 0 ≤ S) (hSR : S ≤ R) (T : ℝ) :
    perturbOpen c S T ⊆ perturbOpen c R T := by
  intro p hp
  refine ⟨ball_subset_ball hSR hp.1,?_,hp.2.2⟩
  have ht : T-S^2 < p.2 := hp.2.1
  nlinarith

theorem perturb_oscillation_range {n : ℕ} (c : Space n) {R T : ℝ} (hR : 0 ≤ R)
    {w : Point n → ℝ} (hw : ContinuousOn w (perturbClosed c R T)) :
    ∀ p∈perturbClosed c R T,
      sInf (w '' perturbClosed c R T) ≤ w p ∧ w p ≤ sSup (w '' perturbClosed c R T) := by
  have hImage := (perturbClosed_compact c R T).image_of_continuousOn hw
  intro p hp
  exact ⟨csInf_le hImage.bddBelow ⟨p,hp,rfl⟩,le_csSup hImage.bddAbove ⟨p,hp,rfl⟩⟩

theorem perturb_oscillation_nonneg {n : ℕ} (c : Space n) {R T : ℝ} (hR : 0 ≤ R)
    {w : Point n → ℝ} (hw : ContinuousOn w (perturbClosed c R T)) :
    0 ≤ perturbOscillation c R T w := by
  obtain ⟨p,hp⟩ := perturb_closed_nonempty c hR T
  have hh := perturb_oscillation_range c hR hw p hp
  exact sub_nonneg.mpr (hh.1.trans hh.2)

theorem perturb_oscillation_le_range {n : ℕ} (c : Space n) {R T : ℝ} (hR : 0 ≤ R)
    {w : Point n → ℝ} {m M : ℝ}
    (hRange : ∀ p∈perturbClosed c R T, m ≤ w p ∧ w p ≤ M) :
    perturbOscillation c R T w ≤ M-m := by
  have hNe := (perturb_closed_nonempty c hR T).image w
  have hSup : sSup (w '' perturbClosed c R T) ≤ M := csSup_le hNe (by
    rintro y ⟨p,hp,rfl⟩
    exact (hRange p hp).2)
  have hInf : m ≤ sInf (w '' perturbClosed c R T) := le_csInf hNe (by
    rintro y ⟨p,hp,rfl⟩
    exact (hRange p hp).1)
  exact sub_le_sub hSup hInf

theorem perturb_oscillation_mono {n : ℕ} (c : Space n) {S R T : ℝ}
    (hS : 0 ≤ S) (hSR : S ≤ R) {w : Point n → ℝ}
    (hw : ContinuousOn w (perturbClosed c R T)) :
    perturbOscillation c S T w ≤ perturbOscillation c R T w := by
  have hImage := (perturbClosed_compact c R T).image_of_continuousOn hw
  have hNe := (perturb_closed_nonempty c hS T).image w
  have hSub : w '' perturbClosed c S T ⊆ w '' perturbClosed c R T :=
    image_mono (perturb_closed_subset_radius c hS hSR T)
  have hSup : sSup (w '' perturbClosed c S T) ≤ sSup (w '' perturbClosed c R T) :=
    csSup_le hNe (fun y hy => le_csSup hImage.bddAbove (hSub hy))
  have hInf : sInf (w '' perturbClosed c R T) ≤ sInf (w '' perturbClosed c S T) :=
    le_csInf hNe (fun y hy => csInf_le hImage.bddBelow (hSub hy))
  exact sub_le_sub hSup hInf

theorem perturb_oscillation_abs_sub {n : ℕ} (c : Space n) {R T : ℝ} (hR : 0 ≤ R)
    {w : Point n → ℝ} (hw : ContinuousOn w (perturbClosed c R T))
    {p q : Point n} (hp : p∈perturbClosed c R T) (hq : q∈perturbClosed c R T) :
    |w p-w q| ≤ perturbOscillation c R T w := by
  have hpB := perturb_oscillation_range c hR hw p hp
  have hqB := perturb_oscillation_range c hR hw q hq
  apply abs_le.mpr
  constructor <;> change _ ≤ _ <;> dsimp only [perturbOscillation] <;> linarith

theorem perturb_oscillation_quarter {n : ℕ} (hn : 0 < n) {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) :
    ∃ theta : ℝ, 1/2 ≤ theta ∧ theta < 1 ∧
      ∀ c : Space n, ∀ R T K : ℝ, 0 < R → 0 ≤ K →
      ∀ w : Point n → ℝ, ContinuousOn w (perturbClosed c R T) →
      viscositySub (perturbOpen c R T) (fun H _ => pucciPlus ell L H) (fun _ => K) w →
      viscositySuper (perturbOpen c R T) (fun H _ => harnackPucciMinus ell L H) (fun _ => -K) w →
      perturbOscillation c (R/4) T w ≤ theta*perturbOscillation c R T w+K*R^2 := by
  obtain ⟨theta,ht0,ht1,hContract⟩ := perturb_scaled_range_contraction hn hell hL
  refine ⟨theta,ht0,ht1,?_⟩
  intro c R T K hR hK w hw hSub hSuper
  obtain ⟨m',M',_,_,hRange,hWidth⟩ := hContract c R T K hR hK w hw
    (sInf (w '' perturbClosed c R T)) (sSup (w '' perturbClosed c R T))
    (perturb_oscillation_range c hR.le hw) hSub hSuper
  exact (perturb_oscillation_le_range c (by positivity) hRange).trans hWidth

end Yau.LeafProofs.L05Aux
