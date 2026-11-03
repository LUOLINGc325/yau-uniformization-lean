import Yau.Proofs.P06TraceHilbertScalarSpace
import Yau.LeafProofs.L19HeatFamilyDerivative
import Yau.Proofs.P06StrongUniqueness

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux.TraceHilbert
open Yau Yau.LeafProofs Yau.LeafProofs.L03 G04Aux L19Aux L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

def scalarCoefficient (A : RealForm M 0) : M.Carrier → ℝ := fun x => A x Fin.elim0

theorem scalarCoefficient_form (A : RealForm M 0) : scalarForm (scalarCoefficient A) = A := by
  funext x
  ext V
  change A x Fin.elim0 = A x V
  congr 1
  funext r
  exact Fin.elim0 r

theorem scalarCoefficient_smooth (A : RealForm M 0) (hA : SmoothRealForm A) :
    SmoothFn (scalarCoefficient A) := by
  intro x
  have he : inChart x (scalarCoefficient A) = fun z => formComponents A x z Fin.elim0 := by
    funext z
    change A _ Fin.elim0 = A _ (fun r => chartVec x (chartInv x z) (realVec (Fin.elim0 r)))
    congr 1
    funext r
    exact Fin.elim0 r
  rw [he]
  exact hA x Fin.elim0

theorem scalarCoefficient_compact (A : RealForm M 0) (hcA : CompactlySupportedRealForm A) :
    HasCompactSupport (scalarCoefficient A) := by
  apply hcA.of_isClosed_subset isClosed_closure
  apply closure_mono
  intro x hx hzero
  apply hx
  simp only [scalarCoefficient, hzero]
  rfl

theorem scalar_hodge (g : SmoothMetric M) (hk : IsKahler g)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) :
    hodgeRealForm g.form 0 (scalarForm f) = scalarForm (fun x => -2 * laplacian g.form f x) := by
  apply realForm_eq_of_center_components
  intro x I
  have hI : I = Fin.elim0 := by funext r; exact Fin.elim0 r
  rw [hI]
  have hx : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  have hs := L12Aux.metricSmooth_of_smoothMetric g
  have he := hodge_represents g.form hs (scalarForm f) (scalarForm_smooth f hf)
    x (chartPt x x) hx Fin.elim0
  have hn := scalarHodgeNormalization g.form hs hk f hf x (chartPt x x) hx
  have hxinv : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  rw [scalarForm_components, show inChart x (fun x => -2 * laplacian g.form f x)
    (chartPt x x) = -2 * laplacian g.form f x by simp only [inChart, hxinv], he]
  change -(hodgeComponents g.form x 0 (formComponents (scalarForm f) x) (chartPt x x) Fin.elim0) / 2 =
    laplacian g.form f (chartInv x (chartPt x x)) at hn
  rw [hxinv] at hn
  linarith

def laplaceTest (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ScalarEnergyDomain g μ hμ) : ScalarEnergyDomain g μ hμ :=
  ⟨laplacian g.form k, smoothFn_laplacian g k.2.1,
    laplacian_hasCompactSupport g.form k.2.1 k.2.2⟩

theorem scalar_closed_graph_of_tests (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g) (u w : Lp ℝ 2 μ)
    (htest : ∀ k : ScalarEnergyDomain g μ hμ,
      inner ℝ w (scalarEnergyDomainL2 g μ hμ k) =
        -2 * inner ℝ u (scalarEnergyDomainL2 g μ hμ (laplaceTest g μ hμ k))) :
    (scalarLift g μ u, scalarLift g μ w) ∈ (hodgeCoreOperator g μ hμ 0).closure.graph := by
  let T := hodgeCoreOperator g μ hμ 0
  have hpair : ∀ a : T.domain, inner ℝ (scalarLift g μ w) (a : L2FormHilbert g μ 0) =
      inner ℝ (scalarLift g μ u) (T a) := by
    intro a
    have ha := T.mem_graph a
    rw [hodgeCoreOperator_graph] at ha
    obtain ⟨A, W, hAW, he⟩ := ha
    let k : ScalarEnergyDomain g μ hμ :=
      ⟨scalarCoefficient A, scalarCoefficient_smooth A hAW.1,
        scalarCoefficient_compact A hAW.2.1⟩
    have hA : scalarLift g μ (scalarEnergyDomainL2 g μ hμ k) =
        realizeActualForm g μ A hAW.2.2.2.1 := by
      have hr := scalarLift_realize g μ (scalarEnergyDomainL2 g μ hμ k) _
        (show L2RealForm g.form μ (scalarForm k) from by
          change L2RealForm g.form μ (scalarForm (scalarCoefficient A))
          rw [scalarCoefficient_form]; exact hAW.2.2.2.1)
        (scalarEnergyDomainL2_coe g μ hμ k)
      simpa only [k, scalarCoefficient_form] using hr
    have hW : W = scalarForm (fun x => -2 * laplacian g.form k x) := by
      rw [((hodgeCorePair_iff_computed g μ hμ A W).mp hAW).2.2,
        ← scalarCoefficient_form A, scalar_hodge g hk _ (scalarCoefficient_smooth A hAW.1)]
    have hWL : realizeActualForm g μ W hAW.2.2.2.2.1 =
        (-2 : ℝ) • scalarLift g μ (scalarEnergyDomainL2 g μ hμ (laplaceTest g μ hμ k)) := by
      rw [← map_smul]
      apply (realizeL2Form_eq_iff_ae g μ _ _).mpr
      filter_upwards [Lp.coeFn_smul (-2 : ℝ) (scalarEnergyDomainL2 g μ hμ (laplaceTest g μ hμ k)),
        scalarEnergyDomainL2_coe g μ hμ (laplaceTest g μ hμ k)] with x hs hl
      ext V
      change W x V = _
      rw [hW]
      change -2 * laplacian g.form k x = (-2 • scalarEnergyDomainL2 g μ hμ (laplaceTest g μ hμ k) : Lp ℝ 2 μ) x
      rw [hs]
      change -2 * laplacian g.form k x = -2 * scalarEnergyDomainL2 g μ hμ (laplaceTest g μ hμ k) x
      rw [hl]
      rfl
    have ha1 := congrArg Prod.fst he
    have ha2 := congrArg Prod.snd he
    change (a : L2FormHilbert g μ 0) = realizeActualForm g μ A hAW.2.2.2.1 at ha1
    change T a = realizeActualForm g μ W hAW.2.2.2.2.1 at ha2
    rw [ha1, ha2, ← hA, hWL, scalarLift_inner, inner_smul_right, scalarLift_inner]
    exact htest k
  have hd : scalarLift g μ u ∈ T.adjoint.domain :=
    LinearPMap.mem_adjoint_domain_of_exists _ ⟨scalarLift g μ w, hpair⟩
  have he := LinearPMap.adjoint_apply_eq (hodgeCoreOperator_domain_dense g μ hμ 0)
    ⟨scalarLift g μ u, hd⟩ hpair
  have hg : (scalarLift g μ u, scalarLift g μ w) ∈ T.adjoint.graph := by
    rw [← he]
    exact T.adjoint.mem_graph ⟨scalarLift g μ u, hd⟩
  rwa [← hodgeCoreOperator_closure_eq_adjoint g μ hμ 0] at hg

end Yau.NodeProofs.P06Aux.TraceHilbert
