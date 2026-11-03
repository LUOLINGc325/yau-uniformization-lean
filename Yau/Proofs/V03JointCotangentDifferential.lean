import Yau.Proofs.V03DiscDifferential

/-! Genuine joint cotangent coordinate derivatives transport in every
valid fixed chart, including closed-disc boundary directions. -/

open scoped Manifold Topology ContDiff
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]

theorem cotangentHolomorphicOn_centeredCoords_contDiffWithinAt {f : P → CotangentPoint M} {S : Set P}
    (hf : CotangentHolomorphicOn f S) {p : P} (hp : p ∈ S) :
    ContDiffWithinAt ℂ ∞ (fun q => cotangentChart (f p).1 (f q)) S p := by
  obtain ⟨V, hV, hpV, _, hcoord⟩ := hf.2 p hp
  exact (contDiffWithinAt_inter (hV.mem_nhds hpV)).mp (hcoord p ⟨hp, hpV⟩)

theorem cotangentHolomorphicOn_coords_contDiffWithinAt {f : P → CotangentPoint M} {S : Set P}
    (hf : CotangentHolomorphicOn f S) {p : P} (hp : p ∈ S)
    (x : M.Carrier) (hx : f p ∈ cotangentSource x) :
    ContDiffWithinAt ℂ ∞ (fun q => cotangentChart x (f q)) S p := by
  have hself : f p ∈ cotangentSource (f p).1 := mem_extChartAt_source _
  have htarget := cotangentChart_mapsTo (f p).1 hself
  have hbase : chartInv (f p).1 (cotangentChart (f p).1 (f p)).1 = (f p).1 :=
    (extChartAt (ComplexModel n) (f p).1).left_inv hself
  have htransition := cotangentChartTransition_contDiffAt (f p).1 x htarget
    (by rw [hbase]; exact hx)
  have hcomp := htransition.comp_contDiffWithinAt p
    (cotangentHolomorphicOn_centeredCoords_contDiffWithinAt hf hp)
  apply hcomp.congr_of_eventuallyEq_of_mem ?_ hp
  have hsource : ∀ᶠ q in 𝓝[S] p, f q ∈ cotangentSource (f p).1 :=
    (hf.1 p hp).continuousWithinAt.preimage_mem_nhdsWithin
      ((isOpen_extChartAt_source (I := ComplexModel n) (f p).1).mem_nhds hself)
  filter_upwards [hsource] with q hq
  simp only [Function.comp_def, cotangentChart_left_inv (f p).1 hq]

theorem cotangentHolomorphicOn_fderivWithin_coords_change {f : P → CotangentPoint M} {S : Set P}
    (hf : CotangentHolomorphicOn f S) {p : P} (hp : p ∈ S) (hS : UniqueDiffWithinAt ℂ S p)
    (x x' : M.Carrier) (hx : f p ∈ cotangentSource x) (hx' : f p ∈ cotangentSource x') :
    fderivWithin ℂ (fun q => cotangentChart x' (f q)) S p =
      (fderiv ℂ (fun z => cotangentChart x' (cotangentChartInv x z)) (cotangentChart x (f p))).comp
        (fderivWithin ℂ (fun q => cotangentChart x (f q)) S p) := by
  let c : P → CotangentCoord n := fun q => cotangentChart x (f q)
  let T : CotangentCoord n → CotangentCoord n := fun z => cotangentChart x' (cotangentChartInv x z)
  have hbase : chartInv x (c p).1 = (f p).1 := (extChartAt (ComplexModel n) x).left_inv hx
  have hT : DifferentiableAt ℂ T (c p) :=
    (cotangentChartTransition_contDiffAt x x' (cotangentChart_mapsTo x hx)
      (by rw [hbase]; exact hx')).differentiableAt (by simp)
  have hc : DifferentiableWithinAt ℂ c S p :=
    (cotangentHolomorphicOn_coords_contDiffWithinAt hf hp x hx).differentiableWithinAt (by simp)
  have hsource : ∀ᶠ q in 𝓝[S] p, f q ∈ cotangentSource x :=
    (hf.1 p hp).continuousWithinAt.preimage_mem_nhdsWithin
      ((isOpen_extChartAt_source (I := ComplexModel n) x).mem_nhds hx)
  have heq : (fun q => cotangentChart x' (f q)) =ᶠ[𝓝[S] p] T ∘ c := by
    filter_upwards [hsource] with q hq
    simp only [Function.comp_def, T, c, cotangentChart_left_inv x hq]
  rw [heq.fderivWithin_eq_of_mem hp]
  exact fderiv_comp_fderivWithin p hT hc hS

end Yau.Blueprint.V03Proof
