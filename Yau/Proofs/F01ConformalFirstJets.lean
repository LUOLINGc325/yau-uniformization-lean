import Yau.Proofs.F01ConformalRayleighContact
import Yau.Proofs.F01ScalarChartSmooth
import Yau.Proofs.F01ConformalGradient
import Yau.Proofs.F01WirtingerCoordinateChain

/-! The actual conformal metric has exactly its scalar first derivative
in a chart whose genuine background real first jet vanishes. -/
noncomputable section
open Set
open scoped Manifold ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem conformal_normal_first_jet (g : HermitianField M) (hg : MetricSmooth g)
    (f : M.Carrier → ℝ) (hf : SmoothFn f)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hs0 : (0 : ComplexVector n) ∈ e.source) (hvalue : pullbackMatrix g e 0 = 1)
    (hjet : ∀ i j, fderiv ℝ (fun w => pullbackMatrix g e w i j) 0 = 0)
    (i j : Fin n) (v : ComplexVector n) :
    wirt (fun w => pullbackMatrix (conformalField g f) e w i j) 0 v =
      (Real.exp (f (e 0)) : ℂ) * wirt (fun w => (f (e w) : ℂ)) 0 v *
        (1 : Matrix (Fin n) (Fin n) ℂ) i j := by
  let E := fun w => ((Real.exp (f (e w)) : ℝ) : ℂ)
  have hfd : DifferentiableAt ℝ (fun w => f (e w)) 0 :=
    ((smoothFn_comp_holomorphic_chart f hf e he).contDiffAt
      (e.open_source.mem_nhds hs0)).differentiableAt (by simp)
  have hEd : DifferentiableAt ℝ E 0 :=
    Complex.ofRealCLM.differentiableAt.comp 0 ((Real.hasDerivAt_exp _).differentiableAt.comp 0 hfd)
  have hGd := (pullbackMatrix_entry_contDiffAt g hg e he hs0 i j).differentiableAt (by simp)
  have hGw : wirt (fun w => pullbackMatrix g e w i j) 0 v = 0 := by
    unfold wirt
    rw [hjet i j]
    simp
  have hEw : wirt E 0 v = (Real.exp (f (e 0)) : ℂ) * wirt (fun w => (f (e w) : ℂ)) 0 v :=
    wirt_ofReal_scalar_comp hfd (Real.hasDerivAt_exp _) v
  change wirt (fun w => E w * pullbackMatrix g e w i j) 0 v = _
  rw [Yau.LeafProofs.L14Aux.wirt_mul_rule E (fun w => pullbackMatrix g e w i j) 0 v hEd hGd,
    hEw, hGw, hvalue]
  ring

end Yau.NodeProofs.F01Aux
