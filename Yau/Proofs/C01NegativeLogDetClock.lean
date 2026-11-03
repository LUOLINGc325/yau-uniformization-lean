import Yau.Proofs.C01SpacetimeLogDetLevi
import Yau.Proofs.C01LeviTwoDirections

/-! The same negative log determinant as a genuine smooth function of
space and logarithmic time; its Levi form is tested in every base direction. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint
open Yau.Blueprint.Alignment.Y03Proof

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

def negativeLogDetClock (h : Flow X) (x : Pt X)
    (q : ComplexVector n × ℂ) : ℝ :=
  -logDet (h (Real.exp (2 * q.2.re))) x q.1

theorem negativeLogDetClock_contDiffAt
    (hflow : LocalizedFlow X o h U P ρ) (x : Pt X)
    (q : ComplexVector n × ℂ) (hq : q.1 ∈ chartTarget x) :
    ContDiffAt ℝ ∞ (negativeLogDetClock h x) q := by
  let S : Set (ComplexVector n × ℂ) := chartTarget x ×ˢ Set.univ
  let H : (ComplexVector n × ℂ) → Herm n :=
    fun p => hMat (h (Real.exp (2 * p.2.re))) x p.1
  have hS : IsOpen S := (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ
  have hSq : q ∈ S := ⟨hq, Set.mem_univ _⟩
  have hre : ContDiff ℝ ∞ (fun p : ComplexVector n × ℂ => p.2.re) :=
    Complex.reCLM.contDiff.comp contDiff_snd
  have hmap : ContDiffOn ℝ ∞
      (fun p : ComplexVector n × ℂ => (p.1, Real.exp (2 * p.2.re))) S :=
    (contDiff_fst.prodMk ((contDiff_const.mul hre).exp)).contDiffOn
  have hH (i j : Fin n) : ContDiffOn ℝ ∞ (fun p => H p i j) S :=
    (metricFamily_hMat_contDiffOn hflow.1.2.1 x i j).comp hmap
      (fun p hp => ⟨hp.1, (Real.exp_pos _).le⟩)
  have hdet := Yau.LeafProofs.SharedCalculus.contDiffOn_matrix_det hH
  have hnonzero (p : ComplexVector n × ℂ) (hp : p ∈ S) : (H p).det.re ≠ 0 :=
    (Complex.pos_iff.mp (hMat_posDef _ x p.1 hp.1).det_pos).1.ne'
  have hlog : ContDiffOn ℝ ∞ (fun p => Real.log (H p).det.re) S :=
    (Complex.reCLM.contDiff.comp_contDiffOn hdet).log hnonzero
  exact hlog.neg.contDiffAt (hS.mem_nhds hSq)

theorem localizedFlow_negativeLogDetClock_levi_nonneg
    (hflow : LocalizedFlow X o h U P ρ) (hjoint : JointPositivity X h)
    (x : Pt X) (z d : ComplexVector n) (hz : z ∈ chartTarget x) (w τ : ℂ) :
    0 ≤ (wirt (fun p => wirtBar (fun q : ComplexVector n × ℂ =>
      (negativeLogDetClock h x q : ℂ)) p (d, τ)) (z, w) (d, τ)).re := by
  let γ : ℂ → ComplexVector n × ℂ := fun ζ => (z + ζ • d, w + ζ * τ)
  have hγ : ContDiffAt ℂ 2 γ 0 := by
    exact (show ContDiffAt ℂ 2 (fun ζ : ℂ => z + ζ • d) 0 from by fun_prop).prodMk
      (show ContDiffAt ℂ 2 (fun ζ : ℂ => w + ζ * τ) 0 from by fun_prop)
  have hγd : HasDerivAt γ (d, τ) 0 := by
    have hd := ((hasDerivAt_id (0 : ℂ)).smul_const d).const_add z
    have hτ := ((hasDerivAt_id (0 : ℂ)).mul_const τ).const_add w
    simpa only [one_smul, one_mul, id_eq] using! hd.prodMk hτ
  have hchart : (γ 0).1 ∈ chartTarget x := by
    simpa only [γ, zero_smul, add_zero] using hz
  have hfc : ContDiffAt ℝ 2
      (fun q : ComplexVector n × ℂ => (negativeLogDetClock h x q : ℂ)) (γ 0) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp _
      ((negativeLogDetClock_contDiffAt hflow x (γ 0) hchart).of_le (by simp))
  have hcurve := levi_direction_comp_holomorphic hfc hγ (1 : ℂ)
  rw [hγd.hasFDerivAt.fderiv] at hcurve
  simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] at hcurve
  have hline := localizedFlow_spacetime_negativeLogDet_levi_nonneg hflow hjoint x z d hz w τ
  change 0 ≤ (wirt (fun p => wirtBar
    ((fun q : ComplexVector n × ℂ => (negativeLogDetClock h x q : ℂ)) ∘ γ) p 1) 0 1).re at hline
  rw [hcurve] at hline
  simpa only [γ, zero_smul, zero_mul, add_zero] using hline

end Yau.NodeProofs.C01Aux
