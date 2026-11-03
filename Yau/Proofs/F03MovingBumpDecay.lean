import Yau.Proofs.F03MovingBumpSubsolution
import Yau.Proofs.F03MovingBumpWeight

/-! The explicit weighted cubic satisfies the actual scalar subcaloric inequality. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau Parabolic
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

theorem decayingMovingBump_spatialDD {n : ℕ} (ε C s₀ R : ℝ)
    (c : ℝ → Space n) (p : Point n) :
    spatialDD (decayingMovingBump ε C s₀ R c) p =
      (ε*Real.exp (-C*(p.2-s₀))) • spatialDD (movingBallBump R c) p := by
  let k := ε*Real.exp (-C*(p.2-s₀))
  change fderiv ℝ (fun x => fderiv ℝ (k • (fun y => movingBallBump R c (y,p.2))) x) p.1 = _
  rw [fderiv_const_smul_field]
  change fderiv ℝ (k • fderiv ℝ (fun y => movingBallBump R c (y,p.2))) p.1 = _
  simpa only [Pi.smul_apply,spatialDD,k] using congrFun
    (fderiv_const_smul_field (𝕜 := ℝ) (f := fderiv ℝ (fun y : Space n => movingBallBump R c (y,p.2))) k) p.1

theorem decayingMovingBump_principal {n : ℕ} (A : Mat n) (ε C s₀ R : ℝ)
    (c : ℝ → Space n) (p : Point n) :
    (∑ i, ∑ j, A i j*spatialDD (decayingMovingBump ε C s₀ R c) p (realVec i) (realVec j)) =
      ε*Real.exp (-C*(p.2-s₀))*
        (∑ i, ∑ j, A i j*spatialDD (movingBallBump R c) p (realVec i) (realVec j)) := by
  rw [decayingMovingBump_spatialDD]
  simp only [smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem decayingMovingBump_subcaloric {n : ℕ} {Q : Set (Point n)}
    {a : Point n → Mat n} {lam upper R V ε : ℝ}
    (hEll : Elliptic Q a lam upper) (hR : 0 < R) (hε : 0 ≤ ε)
    (s₀ : ℝ) {c : ℝ → Space n} {c' : Space n} (p : Point n) (hp : p ∈ Q)
    (hc : HasDerivAt c c' p.2) (hV : ‖c'‖ ≤ V) :
    let C := movingCubicRate R lam (2*R*V+2*(Fintype.card (RIdx n) : ℝ)*upper)
    deriv (fun s => decayingMovingBump ε C s₀ R c (p.1,s)) p.2 -
      (∑ i, ∑ j, a p i j*spatialDD (decayingMovingBump ε C s₀ R c) p (realVec i) (realVec j)) ≤ 0 := by
  dsimp only
  have hres := movingBallBump_residual_le hEll hR p hp hc hV
  rw [(movingBallBump_time_hasDerivAt R p.1 hc).deriv] at hres
  have hw := mul_le_mul_of_nonneg_left hres
    (mul_nonneg hε (Real.exp_pos (-(movingCubicRate R lam
      (2*R*V+2*(Fintype.card (RIdx n) : ℝ)*upper))*(p.2-s₀))).le)
  rw [(decayingMovingBump_time_hasDerivAt ε _ s₀ R p.1 hc).deriv,decayingMovingBump_principal]
  nlinarith only [hw]

end Yau.Proofs.F03Aux
