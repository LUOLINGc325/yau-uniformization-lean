import Yau.Proofs.P06HodgeRegularityWeak
import Yau.Proofs.P06HodgeRegularityScalarEnergy

/-! Ordinary finite components of the actual Hodge chart expression.
The coefficients are the computed Hodge jet CLMs, never arbitrary replacements. -/
noncomputable section
open MeasureTheory Filter Module
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs.L03

section FixedLinearMap
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem regularityDirection_clm (L : F →L[ℝ] ℝ) (U : E → F) {z : E}
    (hU : DifferentiableAt ℝ U z) (e : E) :
    regularityDirection e (fun y => L (U y)) z = L (fderiv ℝ U z e) := by
  have h := (L.hasFDerivAt.comp z hU.hasFDerivAt).fderiv
  exact DFunLike.congr_fun h e

theorem regularityDirection_second_clm (L : F →L[ℝ] ℝ) (U : E → F)
    {O : Set E} (hO : IsOpen O) (hU : ContDiffOn ℝ ∞ U O) {z : E} (hz : z ∈ O) (e f : E) :
    regularityDirection e (regularityDirection f (fun y => L (U y))) z =
      L (fderiv ℝ (fderiv ℝ U) z e f) := by
  have hEq : regularityDirection f (fun y => L (U y)) =ᶠ[𝓝 z]
      (fun y => L (fderiv ℝ U y f)) := by
    filter_upwards [hO.mem_nhds hz] with y hy
    exact regularityDirection_clm L U ((hU.contDiffAt (hO.mem_nhds hy)).differentiableAt (by simp)) f
  change fderiv ℝ (regularityDirection f (fun y => L (U y))) z e = _
  rw [hEq.fderiv_eq]
  have hDU : DifferentiableAt ℝ (fderiv ℝ U) z :=
    (((hU.fderiv_of_isOpen hO (m := ∞) (by simp)).contDiffAt (hO.mem_nhds hz))).differentiableAt (by simp)
  let Q := ContinuousLinearMap.apply ℝ F f
  have h := (L.hasFDerivAt.comp z (Q.hasFDerivAt.comp z hDU.hasFDerivAt)).fderiv
  simpa only [Function.comp_def, Q, ContinuousLinearMap.apply_apply, ContinuousLinearMap.comp_apply] using
    DFunLike.congr_fun h e

end FixedLinearMap

section Basis
variable {F α : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype α]

/-- A fixed fiber basis expands the actual lower-order operator action. -/
theorem regularity_basis_apply (b : Basis α ℝ F) (L : F →L[ℝ] F) (P : F) (r : α) :
    b.repr (L P) r = ∑ c, b.repr (L (b c)) r * b.repr P c := by
  conv_lhs => rw [← b.sum_repr P]
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro c _
  ring

end Basis

variable {n k : ℕ} {M : ComplexManifold n}

def hodgeRegularityCoord {α : Type*} [Fintype α]
    (b : Basis α ℝ (HodgeJets.Fiber n k)) (A : RealForm M k) (x : M.Carrier)
    (z : ComplexVector n) (c : α) : ℝ := b.repr (chartForm A x z) c

def hodgeRegularityE1 {α : Type*} [Fintype α]
    (g : HermitianField M) (x : M.Carrier) (b : Basis α ℝ (HodgeJets.Fiber n k))
    (r c : α) (i : RIdx n) (z : ComplexVector n) : ℝ :=
  b.repr (HodgeJets.E1 g x k i z (b c)) r

def hodgeRegularityE0 {α : Type*} [Fintype α]
    (g : HermitianField M) (x : M.Carrier) (b : Basis α ℝ (HodgeJets.Fiber n k))
    (r c : α) (z : ComplexVector n) : ℝ := b.repr (HodgeJets.E0 g x k z (b c)) r

theorem hodgeRegularityCoord_contDiffOn {α : Type*} [Fintype α]
    (b : Basis α ℝ (HodgeJets.Fiber n k)) (A : RealForm M k) (hA : SmoothRealForm A)
    (x : M.Carrier) (c : α) :
    ContDiffOn ℝ ∞ (fun z => hodgeRegularityCoord b A x z c) (chartTarget x) :=
  (b.coord c).toContinuousLinearMap.contDiff.comp_contDiffOn (chartForm_contDiffOn A hA x)

theorem hodgeRegularityE1_contDiffOn {α : Type*} [Fintype α]
    (g : SmoothMetric M) (x : M.Carrier) (b : Basis α ℝ (HodgeJets.Fiber n k)) (r c : α) (i : RIdx n) :
    ContDiffOn ℝ ∞ (hodgeRegularityE1 g.form x b r c i) (chartTarget x) :=
  (b.coord r).toContinuousLinearMap.contDiff.comp_contDiffOn
    ((HodgeJets.E1_contDiffOn g x k i).clm_apply contDiffOn_const)

theorem hodgeRegularityE0_contDiffOn {α : Type*} [Fintype α]
    (g : SmoothMetric M) (x : M.Carrier) (b : Basis α ℝ (HodgeJets.Fiber n k)) (r c : α) :
    ContDiffOn ℝ ∞ (hodgeRegularityE0 g.form x b r c) (chartTarget x) :=
  (b.coord r).toContinuousLinearMap.contDiff.comp_contDiffOn
    ((HodgeJets.E0_contDiffOn g x k).clm_apply contDiffOn_const)

/-- Every degree of the computed Hodge operator has the genuine scalar
inverse-metric principal part and its actual finite matrix lower-order terms. -/
theorem hodgeRegularity_chart_system {α : Type*} [Fintype α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A : RealForm M k) (hA : SmoothRealForm A) (x : M.Carrier)
    (b : Basis α ℝ (HodgeJets.Fiber n k)) {z : ComplexVector n} (hz : z ∈ chartTarget x) (r : α) :
    hodgeRegularityCoord b (hodgeRealForm g.form k A) x z r =
      -(∑ i, ∑ j, (realMetricFn g.form x z)⁻¹ i j *
        regularityDirection (realModelBasis n i)
          (regularityDirection (realModelBasis n j) (fun y => hodgeRegularityCoord b A x y r)) z) +
      (∑ c, ∑ i, hodgeRegularityE1 g.form x b r c i z *
        regularityDirection (realModelBasis n i) (fun y => hodgeRegularityCoord b A x y c) z) +
      ∑ c, hodgeRegularityE0 g.form x b r c z * hodgeRegularityCoord b A x z c := by
  classical
  let F := chartForm A x
  have hF : ContDiffOn ℝ ∞ F (chartTarget x) := chartForm_contDiffOn A hA x
  have hFd : DifferentiableAt ℝ F z := (hF.contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have hfirst (i : RIdx n) (c : α) :
      regularityDirection (realModelBasis n i) (fun y => hodgeRegularityCoord b A x y c) z =
      b.repr (fderiv ℝ F z (realModelBasis n i)) c :=
    regularityDirection_clm (b.coord c).toContinuousLinearMap F hFd (realModelBasis n i)
  have hsecond (i j : RIdx n) : regularityDirection (realModelBasis n i)
      (regularityDirection (realModelBasis n j) (fun y => hodgeRegularityCoord b A x y r)) z =
      b.repr (fderiv ℝ (fderiv ℝ F) z (realModelBasis n i) (realModelBasis n j)) r :=
    regularityDirection_second_clm (b.coord r).toContinuousLinearMap F
      (isOpen_extChartAt_target (I := ComplexModel n) x) hF hz (realModelBasis n i) (realModelBasis n j)
  have h := congrArg (fun P : HodgeJets.Fiber n k => b.repr P r)
    (HodgeJets.chart_hodge_expansion g μ hμ A hA x hz)
  simp only [map_add, map_neg, map_sum, map_smul, Finsupp.add_apply, Finsupp.neg_apply,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul] at h
  change b.repr (chartForm (hodgeRealForm g.form k A) x z) r = _
  rw [h]
  have hE1 (i : RIdx n) := regularity_basis_apply b (HodgeJets.E1 g.form x k i z)
    (fderiv ℝ F z (realModelBasis n i)) r
  have hE0 := regularity_basis_apply b (HodgeJets.E0 g.form x k z) (F z) r
  apply congrArg₂ (· + ·)
  · apply congrArg₂ (· + ·)
    · apply congrArg Neg.neg
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply congrArg (fun s : ℝ => _ * s)
      simpa only [F, realModelBasis_apply] using (hsecond i j).symm
    · calc
        _ = ∑ i, ∑ c, b.repr (HodgeJets.E1 g.form x k i z (b c)) r *
            b.repr (fderiv ℝ F z (realModelBasis n i)) c := by
          apply Finset.sum_congr rfl
          intro i _
          simpa only [F, realModelBasis_apply] using hE1 i
        _ = ∑ c, ∑ i, b.repr (HodgeJets.E1 g.form x k i z (b c)) r *
            b.repr (fderiv ℝ F z (realModelBasis n i)) c := Finset.sum_comm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro c _
          apply Finset.sum_congr rfl
          intro i _
          exact congrArg (fun s : ℝ => hodgeRegularityE1 g.form x b r c i z * s) (hfirst i c).symm
  · exact hE0

end Yau.NodeProofs.P06Aux
