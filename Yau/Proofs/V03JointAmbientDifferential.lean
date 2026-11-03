import Yau.Proofs.V03JointCotangentDifferential
import Yau.Proofs.V03AmbientSmooth

/-! The genuine ambient derivative of a joint cotangent family equals
the actual chart immersion derivative composed with the original within derivative. -/

open scoped Manifold Topology ContDiff
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem cotangentHolomorphicOn_ambient_fderivWithin {n q : ℕ} {M : ComplexManifold n}
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentHolomorphic G)
    {f : P → CotangentPoint M} {S : Set P} (hf : CotangentHolomorphicOn f S)
    {p : P} (hp : p ∈ S) (hS : UniqueDiffWithinAt ℂ S p)
    (x : M.Carrier) (hx : f p ∈ cotangentSource x) :
    fderivWithin ℂ (fun r => G (f r)) S p =
      (fderiv ℂ (fun z => G (cotangentChartInv x z)) (cotangentChart x (f p))).comp
        (fderivWithin ℂ (fun r => cotangentChart x (f r)) S p) := by
  have hc := cotangentHolomorphicOn_coords_contDiffWithinAt hf hp x hx
  have ht := cotangentChart_mapsTo x hx
  have hopen : IsOpen (cotangentTarget x) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ
  have hg : DifferentiableAt ℂ (fun z => G (cotangentChartInv x z)) (cotangentChart x (f p)) :=
    (hG x _ ht).differentiableAt (hopen.mem_nhds ht)
  have hs : ∀ᶠ r in 𝓝[S] p, f r ∈ cotangentSource x :=
    (hf.1 p hp).continuousWithinAt.preimage_mem_nhdsWithin
      ((isOpen_extChartAt_source (I := ComplexModel n) x).mem_nhds hx)
  have he : (fun r => G (f r)) =ᶠ[𝓝[S] p]
      (fun r => G (cotangentChartInv x (cotangentChart x (f r)))) := by
    filter_upwards [hs] with r hr
    rw [cotangentChart_left_inv x hr]
  rw [he.fderivWithin_eq_of_mem hp]
  exact fderiv_comp_fderivWithin p hg (hc.differentiableWithinAt (by simp)) hS

end Yau.Blueprint.V03Proof
