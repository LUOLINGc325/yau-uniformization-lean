import Yau.Proofs.P06TimeIntegralPotentialIntegral
import Yau.Proofs.P06PDETypeTraceTrace

/-! The actual form heat equation induces the correctly normalized matrix
Levi evolution, with the original compact smooth initial trace. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold Matrix
namespace Yau.NodeProofs.P06Aux.TimePotential
open Yau Yau.Blueprint Yau.LeafProofs
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ} {M : ComplexManifold n}

theorem formHermitianMatrix_components (A : RealForm M 2) (x : M.Carrier) (a b : Fin n) :
    formHermitianMatrix A x a b =
      ((formComponents A x (chartPt x x) ![(a, 0), (b, 1)] : ℂ) +
        Complex.I * (formComponents A x (chartPt x x) ![(a, 0), (b, 0)] : ℂ)) / 2 := by
  have hi : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have he (i j : RIdx n) : formComponents A x (chartPt x x) ![i,j] =
      A x ![chartVec x x (realVec i), chartVec x x (realVec j)] := by
    unfold formComponents
    rw [hi]
    congr 1
    funext r
    fin_cases r <;> rfl
  rw [he, he]
  simp only [realVec, Prod.snd, Prod.fst, Fin.isValue, ↓reduceIte, one_smul,
    L12Aux.chartVec_complex_smul]
  rfl

/-- The zeroth original compact jet gives the actual pointwise initial trace
of every component. -/
theorem formComponents_initial_tendsto {A : RealForm M k} {U : ℝ → RealForm M k}
    (h0 : FormSmoothInitial U A) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (I : Fin k → RIdx n) :
    Tendsto (fun s => formComponents (U s) x z I) (𝓝[>] 0)
      (𝓝 (formComponents A x z I)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨τ, hτ, hh⟩ := h0.2 x {z} isCompact_singleton
    (by intro w hw; simpa only [mem_singleton_iff.mp hw] using hz) 0 I ε hε
  filter_upwards [Ioo_mem_nhdsGT hτ] with s hs
  simpa only [norm_iteratedFDeriv_zero, Real.dist_eq, Real.norm_eq_abs] using
    hh s hs.1 hs.2 z (mem_singleton z)

theorem formHermitianMatrix_initial_tendsto {A : RealForm M 2} {U : ℝ → RealForm M 2}
    (h0 : FormSmoothInitial U A) (x : M.Carrier) (a b : Fin n) :
    Tendsto (fun s => formHermitianMatrix (U s) x a b) (𝓝[>] 0)
      (𝓝 (formHermitianMatrix A x a b)) := by
  have h₁ := formComponents_initial_tendsto h0 x (mem_extChartAt_target x) ![(a, 0), (b, 1)]
  have h₂ := formComponents_initial_tendsto h0 x (mem_extChartAt_target x) ![(a, 0), (b, 0)]
  simpa only [formHermitianMatrix_components, Function.comp_def, chartPt] using
    (((Complex.continuous_ofReal.tendsto _).comp h₁).add
      (((Complex.continuous_ofReal.tendsto _).comp h₂).const_mul Complex.I)).div_const 2

/-- No matrix evolution is assumed: it is obtained from the original
coefficient PDE and an actual representative of the Hodge Laplacian. -/
theorem formHeat_matrix_hasDerivAt {g : HermitianField M} {U : ℝ → RealForm M 2}
    (hpde : FormHeatEquation g U) {t : ℝ} (ht : 0 < t)
    {B : RealForm M 2} (hB : RepresentsHodge g (U t) B)
    (x : M.Carrier) (a b : Fin n) :
    HasDerivAt (fun s => formHermitianMatrix (U s) x a b)
      ((-(1 / 2 : ℂ)) * formHermitianMatrix B x a b) t := by
  have hx : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  have hp (I : Fin 2 → RIdx n) := hpde x (chartPt x x) hx t ht I
  have hd := ((hp ![(a, 0), (b, 1)]).ofReal_comp.add
    ((hp ![(a, 0), (b, 0)]).ofReal_comp.const_mul Complex.I)).div_const 2
  convert hd using 1
  · funext s
    exact formHermitianMatrix_components (U s) x a b
  · rw [formHermitianMatrix_components B x a b]
    simp only [hodgeGeneratorComponents, ← hB x (chartPt x x) hx,
      Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat]
    ring

/-- The fixed G=2 Re h, -□/2 clock gives exactly Levi(trace U), without a
changed norm factor or a rescaled time. -/
theorem closed_formHeat_matrix_hasDerivAt (X : KahlerManifold n)
    {A : RealForm X.manifold 2} {U : ℝ → RealForm X.manifold 2}
    (hA : BoundedOneOneData X.metric.form A) (hU : IsBoundedFormHeat X.metric.form A U)
    {t : ℝ} (ht : 0 < t) (hc : ClosedRealForm (U t))
    (x : X.manifold.Carrier) (a b : Fin n) :
    HasDerivAt (fun s => formHermitianMatrix (U s) x a b)
      (levi (formTrace X.metric.form (U t)) x a b) t := by
  have hs := smoothFormTime_slice hU.1 ht
  have h11 := PDETypeTrace.boundedFormHeat_oneOne X A U hA hU t ht
  obtain ⟨B, _, hB⟩ := (hodgeGeometry X).1.2.2 2 (U t) hs
  have hd := formHeat_matrix_hasDerivAt hU.2.2.2 ht hB x a b
  have hn := congrArg (fun K : Matrix (Fin n) (Fin n) ℂ => K a b)
    ((hodgeGeometry X).2.1.2 (U t) B hs h11 hc hB x)
  change (-(1 / 2 : ℂ)) * formHermitianMatrix B x a b = _ at hn
  rw [← hn]
  exact hd

end Yau.NodeProofs.P06Aux.TimePotential
