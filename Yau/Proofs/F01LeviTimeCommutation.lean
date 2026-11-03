import Yau.Proofs.F01SpaceTimeWirtingerSmooth

/-! The time derivative of the actual complex Hessian is the complex
Hessian of the actual time derivative, on the open solution slab. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ}

theorem leviC_time_derivative_commute (U : ComplexVector n × ℝ → ℝ)
    {S : Set (ComplexVector n)} {I : Set ℝ} (hS : IsOpen S) (hI : IsOpen I)
    (hU : ContDiffOn ℝ ∞ U (S ×ˢ I)) {x : ComplexVector n} {t : ℝ}
    (hx : x ∈ S) (ht : t ∈ I) (i j : Fin n) :
    deriv (fun s => leviC (fun y => U (y, s)) x i j) t =
      leviC (fun y => deriv (fun s => U (y, s)) t) x i j := by
  let F : ComplexVector n × ℝ → ℂ := fun p => (U p : ℂ)
  have hF : ContDiffOn ℝ ∞ F (S ×ˢ I) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hU
  have hderiv (y : ComplexVector n) (hy : y ∈ S) :
      deriv (fun s => F (y, s)) t = ((deriv (fun s => U (y, s)) t : ℝ) : ℂ) := by
    have hd : DifferentiableAt ℝ (fun s => U (y, s)) t :=
      ((hU.contDiffAt ((hS.prod hI).mem_nhds ⟨hy, ht⟩)).differentiableAt (by simp)).comp t
        ((differentiableAt_const y).prodMk differentiableAt_id)
    exact hd.hasDerivAt.ofReal_comp.deriv
  have heq : (fun y => wirtBar (fun z => ((deriv (fun s => U (z, s)) t : ℝ) : ℂ)) y (stdVec i))
      =ᶠ[𝓝 x] (fun y => wirtBar (fun z => deriv (fun s => F (z, s)) t) y (stdVec i)) := by
    filter_upwards [hS.mem_nhds hx] with y hy
    apply wirtBar_eq_of_eventuallyEq
    filter_upwards [hS.mem_nhds hy] with z hz
    exact (hderiv z hz).symm
  have hh := mixed_wirtinger_time_derivative_commute F hS hI hF hx ht (stdVec j) (stdVec i)
  change deriv (fun s => wirt (fun y => wirtBar (fun z => (U (z, s) : ℂ)) y
    (stdVec i)) x (stdVec j)) t =
      wirt (fun y => wirtBar (fun z => ((deriv (fun s => U (z, s)) t : ℝ) : ℂ)) y
        (stdVec i)) x (stdVec j)
  rw [wirt_eq_of_eventuallyEq heq]
  exact hh.symm

theorem leviC_spaceTime_contDiffOn (U : ComplexVector n × ℝ → ℝ)
    {S : Set (ComplexVector n)} {I : Set ℝ} (hS : IsOpen S) (hI : IsOpen I)
    (hU : ContDiffOn ℝ ∞ U (S ×ˢ I)) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ =>
      leviC (fun y => U (y, p.2)) p.1 i j) (S ×ˢ I) := by
  let F : ComplexVector n × ℝ → ℂ := fun p => (U p : ℂ)
  have hF : ContDiffOn ℝ ∞ F (S ×ˢ I) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hU
  have hB : ContDiffOn ℝ ∞ (spaceTimeWirtBar F (stdVec i)) (S ×ˢ I) :=
    spaceTimeWirtBar_contDiffOn F (stdVec i) (hS.prod hI) hF
  change ContDiffOn ℝ ∞ (spaceTimeWirt (spaceTimeWirtBar F (stdVec i)) (stdVec j)) (S ×ˢ I)
  exact spaceTimeWirt_contDiffOn (spaceTimeWirtBar F (stdVec i)) (stdVec j) (hS.prod hI) hB

theorem leviC_time_hasDerivAt (U : ComplexVector n × ℝ → ℝ)
    {S : Set (ComplexVector n)} {I : Set ℝ} (hS : IsOpen S) (hI : IsOpen I)
    (hU : ContDiffOn ℝ ∞ U (S ×ˢ I)) {x : ComplexVector n} {t : ℝ}
    (hx : x ∈ S) (ht : t ∈ I) (i j : Fin n) :
    HasDerivAt (fun s => leviC (fun y => U (y, s)) x i j)
      (leviC (fun y => deriv (fun s => U (y, s)) t) x i j) t := by
  let Ψ : ComplexVector n × ℝ → ℂ := fun p => leviC (fun y => U (y, p.2)) p.1 i j
  have hL : ContDiffOn ℝ ∞ Ψ (S ×ˢ I) := leviC_spaceTime_contDiffOn U hS hI hU i j
  have hd : DifferentiableAt ℝ Ψ (x, t) :=
    (hL.contDiffAt ((hS.prod hI).mem_nhds ⟨hx, ht⟩)).differentiableAt (by simp)
  have hcurve : HasDerivAt (fun s : ℝ => (x, s)) (0, 1) t :=
    (hasDerivAt_const t x).prodMk (hasDerivAt_id t)
  have hh : HasDerivAt (fun s => Ψ (x, s)) (fderiv ℝ Ψ (x, t) (0, 1)) t :=
    hd.hasFDerivAt.comp_hasDerivAt t hcurve
  have he : fderiv ℝ Ψ (x, t) (0, 1) =
      leviC (fun y => deriv (fun s => U (y, s)) t) x i j :=
    (deriv_time_eq_product_fderiv Ψ x t hd).symm.trans
      (leviC_time_derivative_commute U hS hI hU hx ht i j)
  exact hh.congr_deriv he

end Yau.NodeProofs.F01Aux
