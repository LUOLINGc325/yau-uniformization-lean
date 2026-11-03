import Yau.Proofs.C01NegativeLogDetClock
import Yau.Proofs.C01FlowLogDetPotential
import Yau.Proofs.C01FlowScalarTimeJets
import Yau.Proofs.C01LogTimeJets

/-! Both pure time blocks of the actual negative log determinant clock.
The derivative Φ_t=R is produced by the original localized-flow potential. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint
open Yau.Blueprint.Alignment.Y03Proof

theorem product_time_wirtinger_and_mixed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : E × ℂ → ℂ} (z : E) (w : ℂ) (hF : ContDiffAt ℝ 2 F (z, w)) :
    wirtBar F (z, w) (0, 1) = wirtBar (fun p => F (z, p)) w 1 ∧
    wirt (fun p => wirtBar F p (0, 1)) (z, w) (0, 1) =
      wirt (fun p => wirtBar (fun q => F (z, q)) p 1) w 1 := by
  let γ : ℂ → E × ℂ := fun p => (z, p)
  have hγ : ContDiffAt ℂ 2 γ w := contDiffAt_const.prodMk contDiffAt_id
  have hγd : HasDerivAt γ (0, 1) w := by
    simpa only [id_eq] using! (hasDerivAt_const w z).prodMk (hasDerivAt_id w)
  have hfirst := wirtBar_comp_holomorphic (f := F) (γ := γ) (v := (1 : ℂ))
    (hF.differentiableAt (by norm_num)) hγd.differentiableAt
  have hsecond := levi_direction_comp_holomorphic hF hγ (1 : ℂ)
  rw [hγd.hasFDerivAt.fderiv] at hfirst hsecond
  simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] at hfirst hsecond
  constructor
  · simpa only [γ, Function.comp_def] using hfirst.symm
  · simpa only [γ, Function.comp_def] using hsecond.symm

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem negativeLogDetClock_wirtBar_time
    (hflow : LocalizedFlow X o h U P ρ) (x : Pt X)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (w : ℂ) :
    let t := Real.exp (2 * w.re)
    wirtBar (fun p : ComplexVector n × ℂ => (negativeLogDetClock h x p : ℂ))
      (z, w) (0, 1) = (t : ℂ) * (scalarCurvature (h t) (chartInv x z) : ℂ) := by
  dsimp only
  have hF : ContDiffAt ℝ 2
      (fun p : ComplexVector n × ℂ => (negativeLogDetClock h x p : ℂ)) (z, w) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp _
      ((negativeLogDetClock_contDiffAt hflow x (z, w) hz).of_le (by simp))
  rw [(product_time_wirtinger_and_mixed z w hF).1]
  have hd : HasDerivAt (fun s => ((-logDet (h s) x z : ℝ) : ℂ))
      (scalarCurvature (h (Real.exp (2 * w.re))) (chartInv x z) : ℂ)
      (Real.exp (2 * ((0 : ℂ) + w).re)) := by
    simpa only [zero_add] using!
      (localizedFlow_chart_negativeLogDet_hasDerivAt hflow x z hz (Real.exp_pos _)).ofReal_comp
  have hp := (logarithmic_time_wirtinger
    (fun s => ((-logDet (h s) x z : ℝ) : ℂ)) 0 w _ hd).2
  simpa only [negativeLogDetClock, zero_add] using hp

theorem negativeLogDetClock_mixed_time
    (hflow : LocalizedFlow X o h U P ρ) (x : Pt X)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (w : ℂ) :
    let t := Real.exp (2 * w.re)
    wirt (fun p => wirtBar (fun q : ComplexVector n × ℂ =>
      (negativeLogDetClock h x q : ℂ)) p (0, 1)) (z, w) (0, 1) =
        (t : ℂ) * (scalarCurvature (h t) (chartInv x z) : ℂ) +
        (t : ℂ) ^ 2 * ((deriv (fun s => scalarCurvature (h s) (chartInv x z)) t : ℝ) : ℂ) := by
  dsimp only
  have hF : ContDiffAt ℝ 2
      (fun p : ComplexVector n × ℂ => (negativeLogDetClock h x p : ℂ)) (z, w) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp _
      ((negativeLogDetClock_contDiffAt hflow x (z, w) hz).of_le (by simp))
  rw [(product_time_wirtinger_and_mixed z w hF).2]
  have hd : HasDerivAt (fun s => (scalarCurvature (h s) (chartInv x z) : ℂ))
      ((deriv (fun s => scalarCurvature (h s) (chartInv x z))
        (Real.exp (2 * w.re)) : ℝ) : ℂ) (Real.exp (2 * ((0 : ℂ) + w).re)) := by
    simpa only [zero_add] using!
      (localizedFlow_scalar_hasDerivAt hflow (chartInv x z) (Real.exp_pos _)).ofReal_comp
  have hp := logarithmic_time_mixed
    (fun s => ((-logDet (h s) x z : ℝ) : ℂ))
    (fun s => (scalarCurvature (h s) (chartInv x z) : ℂ)) 0 w _
    (fun s hs => (localizedFlow_chart_negativeLogDet_hasDerivAt hflow x z hz hs).ofReal_comp) hd
  simpa only [negativeLogDetClock, zero_add] using hp

end Yau.NodeProofs.C01Aux
