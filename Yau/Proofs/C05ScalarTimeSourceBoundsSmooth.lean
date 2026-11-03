import Yau.Proofs.C05ScalarTimeSourceBoundsDefinitions
import Yau.Proofs.C05NormalizedScalarTimeEvolutionDefinitions
import Yau.Proofs.C05RicciCubicJetsAlgebra
import Yau.Proofs.C05RicciSquareJets
import Yau.Proofs.C05ScalarTraceWord
import Yau.Proofs.C05RicciHessianPair

/-! The computed scalar fields needed by the source budgets are genuinely smooth. -/
noncomputable section
open scoped Topology Manifold ContDiff Matrix
namespace Yau.Proofs.C05ScalarTimeSourceBoundsAux
open Yau Yau.Proofs.C05Aux Yau.Proofs.C05NormalizedScalarTimeEvolutionAux
open Yau.Proofs.C05RicciCubicJetsAux Yau.Proofs.C05RicciSquareJetsAux
open Yau.Proofs.C05HessianPropagationAux Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem smoothFn_add {f g : M.Carrier → ℝ} (hf : SmoothFn f) (hg : SmoothFn g) :
    SmoothFn (fun x => f x + g x) := fun c => (hf c).add (hg c)

theorem smoothFn_const_mul (a : ℝ) {f : M.Carrier → ℝ} (hf : SmoothFn f) :
    SmoothFn (fun x => a * f x) := fun c => contDiffOn_const.mul (hf c)

theorem scalarCurvature_smoothFn (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) : SmoothFn (scalarCurvature k) := by
  intro c
  have hF := (scalarTraceWord 0).eval_contDiffOn k hk c
    (rmJet k c 0) (fun _ _ => (1:ℝ)) (rmJet_contDiffOn k hk c 0)
    (fun _ => contDiffOn_const) Fin.elim0
  exact ((contDiffOn_const (c := (1/2:ℝ))).mul hF).congr
    (fun z hz => scalarJet_eq_curvature_trace_word k hk hK c 0 hz Fin.elim0)

theorem laplacian_smoothFn (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (f : M.Carrier → ℝ) (hf : SmoothFn f) :
    SmoothFn (laplacian k f) := by
  intro c
  have hF := singleTraceEval_contDiffOn (scalarLapTraceWord 0) k hk c
    (scalarJet k f c 2) (scalarJet_contDiffOn k hk f hf c 2) Fin.elim0
  exact ((contDiffOn_const (c := (1/2:ℝ))).mul hF).congr
    (fun z hz => scalarJet_laplacian_trace k hk hK f hf c 0 hz Fin.elim0)

theorem ricciNormSq_smoothFn (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) : SmoothFn (ricciNormSq k) := by
  intro c
  have hF := evalTerms_contDiffOn (ricciSquareTerms 0) k hk c Fin.elim0
  exact ((contDiffOn_const (c := (1/2:ℝ))).mul hF).congr
    (fun z hz => scalarJet_ricciNormSq_terms k hk hK c 0 hz Fin.elim0)

theorem ricciCube_smoothFn (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) : SmoothFn (ricciCube k) := by
  intro c
  have hF := cubicField_contDiffOn k hk c Fin.elim0
  exact ((contDiffOn_const (c := (1/2:ℝ))).mul hF).congr
    (fun z hz => congrFun (scalarJet_ricciCube_eq k hk hK c 0 hz) Fin.elim0)

theorem source1_function (k : HermitianField M) : scalarTimeSource1 k =
    (fun x => laplacian k (scalarCurvature k) x + ricciNormSq k x) := by
  funext x
  simp [scalarTimeSource1, scalarHarnackSource]

theorem source1_smoothFn (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) : SmoothFn (scalarTimeSource1 k) := by
  rw [source1_function]
  exact smoothFn_add (laplacian_smoothFn k hk hK _ (scalarCurvature_smoothFn k hk hK))
    (ricciNormSq_smoothFn k hk hK)

theorem source2_smoothFn (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) : SmoothFn (scalarTimeSource2 k) :=
  smoothFn_add (smoothFn_add (laplacian_smoothFn k hk hK _ (source1_smoothFn k hk hK))
    (smoothFn_const_mul 3 (ricciLeviPairing_smoothFn k hk hK _ (scalarCurvature_smoothFn k hk hK))))
    (smoothFn_const_mul 2 (ricciCube_smoothFn k hk hK))

end Yau.Proofs.C05ScalarTimeSourceBoundsAux
