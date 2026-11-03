import Yau.LeafProofs.L05PucciHarnack

open Filter MeasureTheory Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

def perturbEarlyMean {n : ℕ} (p : ℝ) (v : Point n → ℝ) : ℝ :=
  ((∫ y in harnackQminus n, (v y)^p)/harnackMu (harnackQminus n))^(1/p)

theorem perturb_harnack_identity {n : ℕ} (z : Point n) :
    harnackAffine (0 : Space n) 1 (-1) 1 z=z := by
  simp [harnackAffine,harnack_affineLinear_one]

theorem perturb_super_div {n : ℕ} {ell L K h : ℝ}
    (hell : 0 ≤ ell) (hL : ell ≤ L) (hh : 0 < h) (hKh : K ≤ h)
    {v : Point n → ℝ}
    (hv : viscositySuper (unitOpen n) (fun H _ => harnackPucciMinus ell L H)
      (fun _ => -K) v) :
    viscositySuper (unitOpen n) (fun H _ => harnackPucciMinus ell L H)
      (fun _ => -1) (fun z => v z/h) := by
  have hPull := harnack_super_affine_pullback hell hL hv (0 : Space n)
    (R := 1) (a := -1) (T := 1) (h := h) (by norm_num) (by norm_num) hh
    (D := unitOpen n) (by intro z hz; simpa only [perturb_harnack_identity] using hz)
  simp only [one_pow,div_one,one_mul,perturb_harnack_identity] at hPull
  intro z hz psi hpsi ht
  have hRes := hPull z hz psi hpsi ht
  have hForce : (-1 : ℝ) ≤ (1/h)*(-K) := by
    have hDiv : K/h ≤ 1 := (div_le_one hh).mpr hKh
    calc
      -1 ≤ -(K/h) := by linarith
      _ = (1/h)*(-K) := by ring
  exact hForce.trans hRes

theorem perturb_forced_weak_harnack {n : ℕ} (hn : 0 < n) {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) :
    ∃ p C : ℝ, 0 < p ∧ p < 1 ∧ 0 < C ∧ ∀ K : ℝ, 0 ≤ K →
      ∀ v : Point n → ℝ, ContinuousOn v (unitClosed n) →
      (∀ z∈unitClosed n, 0 ≤ v z) →
      viscositySuper (unitOpen n) (fun H _ => harnackPucciMinus ell L H)
        (fun _ => -K) v →
      ∀ z∈harnackQplus n, perturbEarlyMean p v ≤ C*(v z+K) := by
  obtain ⟨p,C,hp,hp1,hC,hWH⟩ := pucci_weak_harnack hn hell hL
  refine ⟨p,C,hp,hp1,hC,?_⟩
  intro K hK v hv hv0 hSuper z hz
  apply le_of_forall_pos_le_add
  intro e he
  let h := K+e/C
  have hh : 0 < h := add_pos_of_nonneg_of_pos hK (div_pos he hC)
  have hKh : K ≤ h := le_add_of_nonneg_right (div_nonneg he.le hC.le)
  have hvh : ContinuousOn (fun y => v y/h) (unitClosed n) := hv.div_const h
  have hvh0 : ∀ y∈unitClosed n, 0 ≤ v y/h :=
    fun y hy => div_nonneg (hv0 y hy) hh.le
  have hScaled := perturb_super_div hell.le hL hh hKh hSuper
  have hBound := hWH (fun y => v y/h) hvh hvh0 hScaled z hz
  have hMoment := harnack_moment_norm_scale hvh hv hvh0 hv0
    (harnack_qminus_isOpen n).measurableSet harnack_qminus_subset_unitClosed
    (harnack_qminus_mu_pos n) hh hp (fun y _ => by
      rw [mul_div_cancel₀ _ hh.ne'])
  change perturbEarlyMean p v ≤ h*perturbEarlyMean p (fun y => v y/h) at hMoment
  change perturbEarlyMean p (fun y => v y/h) ≤ C*(v z/h+1) at hBound
  calc
    perturbEarlyMean p v ≤ h*perturbEarlyMean p (fun y => v y/h) := hMoment
    _ ≤ h*(C*(v z/h+1)) := mul_le_mul_of_nonneg_left hBound hh.le
    _ = C*(v z+h) := by field_simp [hh.ne'] <;> ring
    _ = C*(v z+K)+e := by dsimp only [h]; field_simp [hC.ne'] <;> ring

theorem perturb_qplus_closure (n : ℕ) :
    closure (harnackQplus n)=Metric.closedBall (0 : Space n) (1/4) ×ˢ Icc (-1/4 : ℝ) 0 := by
  rw [harnackQplus,closure_prod_eq,closure_ball _ (by norm_num : (1/4 : ℝ)≠0),
    closure_Ioo (by norm_num : (-1/4 : ℝ)≠0)]

theorem perturb_qplus_closure_subset {n : ℕ} : closure (harnackQplus n) ⊆ unitClosed n := by
  rw [perturb_qplus_closure]
  intro z hz
  exact ⟨Metric.closedBall_subset_closedBall (by norm_num) hz.1,
    ⟨by linarith [hz.2.1],hz.2.2⟩⟩

theorem perturb_forced_weak_harnack_closed {n : ℕ} (hn : 0 < n) {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) :
    ∃ p C : ℝ, 0 < p ∧ p < 1 ∧ 0 < C ∧ ∀ K : ℝ, 0 ≤ K →
      ∀ v : Point n → ℝ, ContinuousOn v (unitClosed n) →
      (∀ z∈unitClosed n, 0 ≤ v z) →
      viscositySuper (unitOpen n) (fun H _ => harnackPucciMinus ell L H)
        (fun _ => -K) v →
      ∀ z∈Metric.closedBall (0 : Space n) (1/4) ×ˢ Icc (-1/4 : ℝ) 0,
        perturbEarlyMean p v ≤ C*(v z+K) := by
  obtain ⟨p,C,hp,hp1,hC,hWH⟩ := perturb_forced_weak_harnack hn hell hL
  refine ⟨p,C,hp,hp1,hC,?_⟩
  intro K hK v hv hv0 hSuper z hz
  have hPoint := hWH K hK v hv hv0 hSuper
  have hCont : ContinuousOn (fun y => C*(v y+K)) (closure (harnackQplus n)) :=
    (continuousOn_const.mul (hv.add continuousOn_const)).mono perturb_qplus_closure_subset
  exact le_on_closure hPoint continuousOn_const hCont (by rwa [perturb_qplus_closure])

end Yau.LeafProofs.L05Aux
