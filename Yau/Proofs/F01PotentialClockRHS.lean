import Yau.Proofs.F01PotentialFiniteClockJet
import Yau.Proofs.F01SpatialJetPasteContinuity
import Yau.Proofs.F01OrdinaryPullback

/-! Native right-hand side of the potential equation, its actual spatial
smoothness and its exact behavior under a time-face paste. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

def localPotentialClockRHS (S : Point n → Matrix (Fin n) (Fin n) ℂ)
    (b f : Point n → ℝ) (p : Point n) : ℝ :=
  Real.log (S p + leviC (fun z => f (z, p.2)) p.1).det.re + b p

theorem localPotentialClockRHS_smooth_slice
    (S : Point n → Matrix (Fin n) (Fin n) ℂ) (b f : Point n → ℝ)
    {O : Set (Space n)} (hO : IsOpen O) (t : ℝ)
    (hS : ContDiffOn ℝ ∞ (fun z => S (z, t)) O)
    (hb : ContDiffOn ℝ ∞ (fun z => b (z, t)) O)
    (hf : ContDiffOn ℝ ∞ (fun z => f (z, t)) O)
    (hPos : ∀ z ∈ O, 0 < (S (z, t) + leviC (fun y => f (y, t)) z).det.re) :
    ContDiffOn ℝ ∞ (fun z => localPotentialClockRHS S b f (z, t)) O := by
  have hH := hS.add (native_levi_frobenius_contDiffOn hO hf)
  have hLog : ContDiffOn ℝ ∞
      ((complexMatrixLogDet (n := n)) ∘ fun z => S (z, t) + leviC (fun y => f (y, t)) z) O :=
    complexMatrixLogDet_contDiffOn.comp hH (fun z hz => hPos z hz)
  exact hLog.add hb

theorem localPotentialClockRHS_face_match
    (S : Point n → Matrix (Fin n) (Fin n) ℂ) (b f g : Point n → ℝ)
    {O : Set (Space n)} (hO : IsOpen O) (T : ℝ)
    (hMatch : ∀ z ∈ O, f (z, T) = g (z, T)) {x : Space n} (hx : x ∈ O) :
    localPotentialClockRHS S b f (x, T) = localPotentialClockRHS S b g (x, T) := by
  have he : (fun z => f (z, T)) =ᶠ[𝓝 x] (fun z => g (z, T)) := by
    filter_upwards [hO.mem_nhds hx] with z hz using hMatch z hz
  unfold localPotentialClockRHS
  rw [Yau.LeafProofs.L22Aux.leviC_congr_of_eventuallyEq he]

theorem spatial_clock_rhs_timeFacePaste
    (S : Point n → Matrix (Fin n) (Fin n) ℂ) (b f g : Point n → ℝ)
    (T : ℝ) (k : ℕ) (p : Point n) :
    iteratedFDeriv ℝ k
      (fun z => localPotentialClockRHS S b (timeFacePaste f g T) (z, p.2)) p.1 =
      timeFacePaste
        (fun q => iteratedFDeriv ℝ k (fun z => localPotentialClockRHS S b f (z, q.2)) q.1)
        (fun q => iteratedFDeriv ℝ k (fun z => localPotentialClockRHS S b g (z, q.2)) q.1) T p := by
  by_cases ht : p.2 ≤ T
  · simp only [localPotentialClockRHS, timeFacePaste, if_pos ht]
  · simp only [localPotentialClockRHS, timeFacePaste, if_neg ht]

end Yau.NodeProofs.F01Aux
