import Yau.Proofs.F01LeviTimeCommutation
import Yau.Proofs.F01LeviChartNaturality

/-! The actual scalar complex Monge--Ampere equation differentiates to
the actual local metric evolution.  Every derivative is computed from the potential. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ}

theorem local_potential_matrix_hasDerivAt
    (A : ComplexVector n → Matrix (Fin n) (Fin n) ℂ)
    (K : ComplexVector n × ℝ → Matrix (Fin n) (Fin n) ℂ)
    (Φ : ComplexVector n × ℝ → ℝ)
    {S : Set (ComplexVector n)} {I : Set ℝ} (hS : IsOpen S) (hI : IsOpen I)
    (hΦ : ContDiffOn ℝ ∞ Φ (S ×ˢ I))
    (hmetric : ∀ y ∈ S, ∀ s ∈ I, K (y, s) = A y + leviC (fun z => Φ (z, s)) y)
    (hpde : ∀ y ∈ S, ∀ s ∈ I, HasDerivAt (fun r => Φ (y, r))
      (Real.log (K (y, s)).det.re) s)
    {x : ComplexVector n} {t : ℝ} (hx : x ∈ S) (ht : t ∈ I) (i j : Fin n) :
    HasDerivAt (fun s => K (x, s) i j)
      (leviC (fun y => Real.log (K (y, t)).det.re) x i j) t := by
  have hspace : (fun y => deriv (fun s => Φ (y, s)) t) =ᶠ[𝓝 x]
      (fun y => Real.log (K (y, t)).det.re) := by
    filter_upwards [hS.mem_nhds hx] with y hy
    exact (hpde y hy t ht).deriv
  have hlevi : leviC (fun y => deriv (fun s => Φ (y, s)) t) x =
      leviC (fun y => Real.log (K (y, t)).det.re) x :=
    Yau.LeafProofs.L22Aux.leviC_congr_of_eventuallyEq hspace
  have hh := (leviC_time_hasDerivAt Φ hS hI hΦ hx ht i j).const_add (A x i j)
  rw [hlevi] at hh
  apply hh.congr_of_eventuallyEq
  filter_upwards [hI.mem_nhds ht] with s hs
  rw [hmetric x hx s hs, Matrix.add_apply]

end Yau.NodeProofs.F01Aux
