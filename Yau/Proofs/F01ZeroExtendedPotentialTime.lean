import Yau.Proofs.F01ZeroExtensionTimeJet
import Yau.Proofs.F01ClampedTimeContinuity
import Yau.Proofs.F01LogDetRatioSmooth
import Yau.Geometry.ParabolicCalculus

/-! The actual within-time derivative of the zero-extended potential is
the same actual log-determinant ratio at clamped time, including zero. -/
noncomputable section
open Set
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ} {M : ComplexManifold n}

theorem zero_extended_potential_timeD
    (α : HermitianField M) (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ)
    {T : ℝ} (hT : 0 < T) (hh0 : h 0 = α) (hU0 : ∀ x, U x 0 = 0)
    (hpde : ∀ x s, s ∈ Icc 0 T → HasDerivWithinAt (U x)
      (flowLogDetRatio α h x s) (Icc 0 T) s)
    (e : Space n → M.Carrier) {S : Set (Space n)} {p : Point n}
    (hp : p ∈ S ×ˢ Icc (-1) T) :
    timeD (S ×ˢ Icc (-1) T)
      (forwardZeroSpaceTime (fun q : Point n => U (e q.1) q.2)) p =
        flowLogDetRatio α h (e p.1) (max p.2 0) := by
  have hP0 : ∀ x, flowLogDetRatio α h x 0 = 0 := flowLogDetRatio_initial α h hh0
  have hjet := forwardZeroExtension_time_jet hT (hU0 (e p.1)) (hP0 (e p.1))
    (hpde (e p.1)) hp.2
  have hset : {s : ℝ | (p.1, s) ∈ S ×ˢ Icc (-1) T} = Icc (-1) T := by
    ext s
    exact and_iff_right hp.1
  unfold timeD
  rw [hset]
  change derivWithin (forwardZeroExtension (U (e p.1))) (Icc (-1) T) p.2 = _
  rw [hjet.derivWithin ((uniqueDiffOn_Icc (by linarith : (-1 : ℝ) < T)) p.2 hp.2)]
  exact forwardZeroSpaceTime_eq_clamped
    (F := fun q : Point n => flowLogDetRatio α h (e q.1) q.2)
    (fun z (_ : z ∈ S) => hP0 (e z)) hp.1 p.2

end Yau.NodeProofs.F01Aux
