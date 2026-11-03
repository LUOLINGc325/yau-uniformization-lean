import Yau.Proofs.F01NormalMixedProduct
import Yau.Proofs.F01RestrictedMixedExchange
import Yau.Proofs.F01ConformalRayleighContact
import Yau.Proofs.F01ScalarChartSmooth

/-! In the constructed real-normal chart, the background Kähler second
derivatives cancel from the actual conformal diagonal derivative exchange. -/
noncomputable section
open Set TopologicalSpace
open scoped Manifold ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} (M : ComplexManifold n) (S : Opens M.Carrier)
  (hS : IsConnected (S : Set M.Carrier))

theorem conformal_normal_diagonal_mixed_exchange (g : SmoothMetric M)
    (f : (openConnectedManifold M S hS).Carrier → ℝ) (hf : SmoothFn f)
    (e : OpenPartialHomeomorph (ComplexVector n) (openConnectedManifold M S hS).Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hs0 : (0 : ComplexVector n) ∈ e.source)
    (hvalue : pullbackMatrix (openRestrictedField M S hS g.form) e 0 = 1)
    (hjet : ∀ i j, fderiv ℝ (fun w =>
      pullbackMatrix (openRestrictedField M S hS g.form) e w i j) 0 = 0) (i a : Fin n) :
    let α := conformalField (openRestrictedField M S hS g.form) f
    wirt (fun w => wirtBar (fun y => pullbackMatrix α e y i i) w (stdVec a)) 0 (stdVec a) -
        wirt (fun w => wirtBar (fun y => pullbackMatrix α e y a a) w (stdVec i)) 0 (stdVec i) =
      leviC (fun w => Real.exp (f (e w))) 0 a a - leviC (fun w => Real.exp (f (e w))) 0 i i := by
  let g0 := openRestrictedField M S hS g.form
  let E := fun w => ((Real.exp (f (e w)) : ℝ) : ℂ)
  have hE : ContDiffOn ℝ ∞ E e.source :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (smoothFn_comp_holomorphic_chart f hf e he).exp
  have hG (p q : Fin n) : ContDiffOn ℝ ∞ (fun w => pullbackMatrix g0 e w p q) e.source :=
    pullbackMatrix_entry_contDiffOn g0
      (openRestrictedField_metricSmooth M S hS (Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric g)) e he p q
  have hunit (p : Fin n) : pullbackMatrix g0 e 0 p p = 1 := by
    exact (congrFun (congrFun hvalue p) p).trans (by simp)
  have hcompute (p q : Fin n) :
      wirt (fun w => wirtBar (fun y => pullbackMatrix (conformalField g0 f) e y p p) w (stdVec q)) 0 (stdVec q) =
        leviC (fun w => Real.exp (f (e w))) 0 q q +
        E 0 * wirt (fun w => wirtBar (fun y => pullbackMatrix g0 e y p p) w (stdVec q)) 0 (stdVec q) := by
    exact mixed_wirt_mul_of_unit_zero_jet E (fun w => pullbackMatrix g0 e w p p)
      e.open_source hE (hG p p) hs0 (hunit p) (hjet p p) (stdVec q) (stdVec q)
  dsimp only
  rw [hcompute i a, hcompute a i,
    restricted_metric_diagonal_mixed_exchange M S hS g e he hs0 i a]
  ring

end Yau.NodeProofs.F01Aux
