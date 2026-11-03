import Yau.LeafProofs.L05PerturbationHolderGeometry

open Filter Set Metric
open scoped Topology
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_holder_of_near_pairs {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    {Q : Set (Point n)} {eta rstar J Cnear : ℝ} (heta : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hrstar : 0 < rstar) (hJ : 0 ≤ J) (hNearC : 0 ≤ Cnear) (v : Point n → V)
    (hSup : ∀ p∈Q, ‖v p‖ ≤ J)
    (hNear : ∀ p∈Q, ∀ q∈Q, 0 < parabolicDistance p q → parabolicDistance p q ≤ rstar/4 →
      ‖v p-v q‖ ≤ Cnear*(parabolicDistance p q)^eta) :
    HolderBound eta Q v (1+J+Cnear+2*J*(4/rstar)^eta) := by
  let Cfar := 2*J*(4/rstar)^eta
  let C := 1+J+Cnear+Cfar
  have hFarC : 0 ≤ Cfar := by dsimp only [Cfar]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hCJ : J ≤ C := by dsimp only [C]; linarith
  have hCN : Cnear ≤ C := by dsimp only [C]; linarith
  have hCF : Cfar ≤ C := by dsimp only [C]; linarith
  refine ⟨hC,fun p hp => (hSup p hp).trans hCJ,?_⟩
  intro p hp q hq
  let d := parabolicDistance p q
  have hd : 0 ≤ d := perturb_distance_nonneg p q
  have hPower : d^eta ≤ holderWeight eta p q := perturb_distance_rpow_le_weight heta heta1 p q
  have hW : 0 ≤ holderWeight eta p q :=
    add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (abs_nonneg _) _)
  by_cases hd0 : d=0
  · have hpq : p=q := perturb_distance_zero hd0
    rw [hpq,sub_self,norm_zero]
    simpa only [hpq] using mul_nonneg hC hW
  have hdPos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
  by_cases hNearDist : d ≤ rstar/4
  · exact (hNear p hp q hq hdPos hNearDist).trans
      ((mul_le_mul_of_nonneg_left hPower hNearC).trans (mul_le_mul_of_nonneg_right hCN hW))
  have hFarDist : rstar/4 ≤ d := le_of_lt (lt_of_not_ge hNearDist)
  have hSmallPos : 0 < rstar/4 := by positivity
  have hScalePos : 0 ≤ (4/rstar)^eta := Real.rpow_nonneg (by positivity) _
  have hInverse : (4/rstar)^eta*(rstar/4)^eta=1 := by
    rw [← Real.mul_rpow (by positivity : 0 ≤ 4/rstar) hSmallPos.le]
    rw [show (4/rstar)*(rstar/4)=1 from by field_simp,Real.one_rpow]
  have hOne : 1 ≤ (4/rstar)^eta*d^eta := by
    rw [← hInverse]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hSmallPos.le hFarDist heta) hScalePos
  have hDiff : ‖v p-v q‖ ≤ 2*J :=
    (norm_sub_le (v p) (v q)).trans (by linarith only [hSup p hp,hSup q hq])
  have hFar : 2*J ≤ Cfar*d^eta := by
    have hh := mul_le_mul_of_nonneg_left hOne (show 0 ≤ 2*J by positivity)
    dsimp only [Cfar]
    nlinarith only [hh]
  exact hDiff.trans (hFar.trans
    ((mul_le_mul_of_nonneg_left hPower hFarC).trans (mul_le_mul_of_nonneg_right hCF hW)))

end Yau.LeafProofs.L05Aux
