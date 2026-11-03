import Yau.Proofs.V03DifferentialTransport
import Yau.Proofs.V03DiscSmooth

/-! The actual ambient frame is holomorphic smooth even though its centered
coordinate matrices are checked in varying induced charts. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {M : ComplexManifold n}

theorem cotangentDG_entry_contDiffWithinAt {P : Type*}
    [NormedAddCommGroup P] [NormedSpace ℂ P] {S : Set P} {ζ : P}
    {f : P → CotangentPoint M} {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentHolomorphic G) (x : M.Carrier)
    (hx : f ζ ∈ cotangentSource x)
    (hf : ContDiffWithinAt ℂ ∞ (fun η => cotangentChart x (f η)) S ζ)
    (a : Fin q) (b : CotangentIndex n) :
    ContDiffWithinAt ℂ ∞ (fun η => cotangentDG G x (f η) a b) S ζ := by
  have ht := cotangentChart_mapsTo x hx
  have hchart : ContDiffAt ℂ ∞ (fun z => G (cotangentChartInv x z))
      (cotangentChart x (f ζ)) :=
    (cotangentHolomorphic_chart_contDiffOn hG x).contDiffAt
      (((isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ).mem_nhds ht)
  have hD := (hchart.fderiv_right (m := ∞) (by simp)).comp_contDiffWithinAt ζ hf
  exact (contDiffAt_piLp_apply (p := 2) (i := a)).comp_contDiffWithinAt ζ
    (hD.clm_apply contDiffWithinAt_const)

theorem ambientFrame_entry_contDiffOn {f : ℂ → CotangentPoint M}
    {E : ℂ → CotangentMatrix n} (hE : IsDiscFrame f E)
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentHolomorphic G)
    (a : Fin q) (b : CotangentIndex n) :
    ContDiffOn ℂ ∞ (fun ζ => ambientFrame G f E ζ a b) (Metric.closedBall 0 1) := by
  intro ζ hζ
  obtain ⟨V, hV, hζV, hsource, hframe⟩ := hE.2.2 ζ hζ
  have hself : f ζ ∈ cotangentSource (f ζ).1 := mem_extChartAt_source _
  have hcoord := cotangentDisc_coords_contDiffWithinAt hE.2.1 hζ (f ζ).1 hself
  have hDG : ∀ k, ContDiffWithinAt ℂ ∞
      (fun η => cotangentDG G (f ζ).1 (f η) a k)
      (Metric.closedBall 0 1 ∩ V) ζ := by
    intro k
    exact (cotangentDG_entry_contDiffWithinAt hG (f ζ).1 hself hcoord a k).mono
      Set.inter_subset_left
  have hmodel : ContDiffWithinAt ℂ ∞
      (fun η => (cotangentDG G (f ζ).1 (f η) * frameInChart (f ζ).1 f E η) a b)
      (Metric.closedBall 0 1 ∩ V) ζ := by
    simp only [Matrix.mul_apply]
    apply ContDiffWithinAt.sum
    intro k _
    exact (hDG k).mul (hframe k b ζ ⟨hζ, hζV⟩)
  apply (contDiffWithinAt_inter (hV.mem_nhds hζV)).mp
  apply hmodel.congr_of_eventuallyEq_of_mem ?_ ⟨hζ, hζV⟩
  filter_upwards [self_mem_nhdsWithin] with η hη
  exact congrFun (congrFun (ambientFrame_in_fixed_chart hG f E (f ζ).1 η
    (hsource η hη)) a) b

theorem ambientFrame_contDiffOn {f : ℂ → CotangentPoint M}
    {E : ℂ → CotangentMatrix n} (hE : IsDiscFrame f E)
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentHolomorphic G) :
    ContDiffOn ℂ ∞ (fun ζ (a : Fin q) (b : CotangentIndex n) =>
      ambientFrame G f E ζ a b) (Metric.closedBall 0 1) :=
  contDiffOn_pi.mpr fun a => contDiffOn_pi.mpr fun b =>
    ambientFrame_entry_contDiffOn hE hG a b

end Yau.Blueprint.V03Proof
