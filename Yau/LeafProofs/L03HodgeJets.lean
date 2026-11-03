import Yau.LeafProofs.L03
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

open MeasureTheory Filter Module
open scoped Topology InnerProductSpace ComplexConjugate ContDiff

set_option maxSynthPendingDepth 8

noncomputable section

namespace Yau.LeafProofs.L03

namespace HodgeJets

abbrev Fiber (n k : ℕ) := (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ
abbrev Jet (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] := F × (E →L[ℝ] F)
abbrev SecondJet (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] := F × ((E →L[ℝ] F) × (E →L[ℝ] E →L[ℝ] F))

section Abstract

variable {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Differentiate an actual first-jet calculator, retaining its coefficient derivative. -/
def prolong (L : Jet E F →L[ℝ] G) (L' : E →L[ℝ] Jet E F →L[ℝ] G) :
    (Jet E F × (E →L[ℝ] Jet E F)) →L[ℝ] Jet E G :=
  (L.comp (ContinuousLinearMap.fst ℝ _ _)).prod
    ((L'.flip.comp (ContinuousLinearMap.fst ℝ _ _)) +
      ((ContinuousLinearMap.compL ℝ E (Jet E F) G L).comp
        (ContinuousLinearMap.snd ℝ _ _)))

theorem prolong_apply (L : Jet E F →L[ℝ] G) (L' : E →L[ℝ] Jet E F →L[ℝ] G)
    (p : Jet E F) (q : E →L[ℝ] Jet E F) :
    prolong L L' (p, q) = (L p, L'.flip p + L.comp q) := rfl

/-- A genuine second jet has the first derivative duplicated in the two required slots. -/
def secondJetLift : SecondJet E F →L[ℝ] (Jet E F × (E →L[ℝ] Jet E F)) :=
  let p := ContinuousLinearMap.fst ℝ F ((E →L[ℝ] F) × (E →L[ℝ] E →L[ℝ] F))
  let d := (ContinuousLinearMap.fst ℝ (E →L[ℝ] F) (E →L[ℝ] E →L[ℝ] F)).comp
    (ContinuousLinearMap.snd ℝ F _)
  let h := (ContinuousLinearMap.snd ℝ (E →L[ℝ] F) (E →L[ℝ] E →L[ℝ] F)).comp
    (ContinuousLinearMap.snd ℝ F _)
  (p.prod d).prod
    ((ContinuousLinearMap.compL ℝ E F (Jet E F) (ContinuousLinearMap.inl ℝ F (E →L[ℝ] F))).comp d +
      (ContinuousLinearMap.compL ℝ E (E →L[ℝ] F) (Jet E F) (ContinuousLinearMap.inr ℝ F (E →L[ℝ] F))).comp h)

theorem secondJetLift_apply (P : F) (D : E →L[ℝ] F) (H : E →L[ℝ] E →L[ℝ] F) :
    secondJetLift (P, D, H) = ((P, D), D.prod H) := by
  ext x <;> simp [secondJetLift]

theorem prolong_actual (L : E → Jet E F →L[ℝ] G) (u : E → F) (z : E)
    (hL : DifferentiableAt ℝ L z) (hu : DifferentiableAt ℝ u z)
    (hdu : DifferentiableAt ℝ (fderiv ℝ u) z) :
    prolong (L z) (fderiv ℝ L z)
        (secondJetLift (u z, fderiv ℝ u z, fderiv ℝ (fderiv ℝ u) z)) =
      ((L z (u z, fderiv ℝ u z)),
        fderiv ℝ (fun y => L y (u y, fderiv ℝ u y)) z) := by
  rw [secondJetLift_apply, prolong_apply]
  congr 1
  simpa only [hu.fderiv_prodMk hdu, add_comm] using
    (fderiv_clm_apply hL (hu.prodMk hdu)).symm

/-- Smooth coefficients remain smooth after the true first-jet prolongation. -/
theorem prolong_contDiffOn [FiniteDimensional ℝ E] (L : E → Jet E F →L[ℝ] G) (O : Set E)
    (hL : ContDiffOn ℝ ∞ L O) (hO : IsOpen O)
    (p : Jet E F) (q : E →L[ℝ] Jet E F) :
    ContDiffOn ℝ ∞ (fun z => prolong (L z) (fderiv ℝ L z) (p, q)) O := by
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ L) O := hL.fderiv_of_isOpen hO (by simp)
  apply ContDiffOn.prodMk (hL.clm_apply contDiffOn_const)
  apply contDiffOn_clm_apply.mpr
  intro v
  exact ((hd.clm_apply contDiffOn_const).clm_apply contDiffOn_const).add
    (hL.clm_apply contDiffOn_const)

end Abstract

local instance {n k : ℕ} : NormedAddCommGroup (Fiber n k) := inferInstance
local instance {n k : ℕ} : NormedSpace ℝ (Fiber n k) := inferInstance
local instance {n k : ℕ} : NormedAddCommGroup (ComplexVector n →L[ℝ] Fiber n k) := inferInstance
local instance {n k : ℕ} : NormedSpace ℝ (ComplexVector n →L[ℝ] Fiber n k) := inferInstance
local instance {n k : ℕ} : NormedAddCommGroup (Jet (ComplexVector n) (Fiber n k)) := inferInstance
local instance {n k : ℕ} : NormedSpace ℝ (Jet (ComplexVector n) (Fiber n k)) := inferInstance
local instance {n j k : ℕ} : NormedAddCommGroup (Jet (ComplexVector n) (Fiber n j) →L[ℝ] Fiber n k) := inferInstance
local instance {n j k : ℕ} : NormedSpace ℝ (Jet (ComplexVector n) (Fiber n j) →L[ℝ] Fiber n k) := inferInstance

section Geometry

variable {n k : ℕ} {M : ComplexManifold n}

/-- The coefficient family of the actual codifferential is smooth as a CLM. -/
theorem codifferentialJet_contDiffOn (g : SmoothMetric M) (x : M.Carrier) :
    ContDiffOn ℝ ∞ (modelCodifferentialJetCLM (k := k) g.form x) (chartTarget x) := by
  apply contDiffOn_clm_apply.mpr
  rintro ⟨P, D⟩
  exact modelCodifferentialJetCLM_contDiffOn g x P D

/-- Continuous linear calculator on true second jets of degree-k model forms. -/
def hodgeSecondJetCLM (g : HermitianField M) (x : M.Carrier) (z : ComplexVector n) :
    (k : ℕ) → SecondJet (ComplexVector n) (Fiber n k) →L[ℝ] Fiber n k
  | 0 => (modelCodifferentialJetCLM (k := 0) g x z).comp
      ((prolong (modelExteriorJetCLM n 0) 0).comp secondJetLift)
  | j + 1 => (modelExteriorJetCLM n j).comp
      ((prolong (modelCodifferentialJetCLM (k := j) g x z)
        (fderiv ℝ (modelCodifferentialJetCLM (k := j) g x) z)).comp secondJetLift) +
      (modelCodifferentialJetCLM (k := j + 1) g x z).comp
        ((prolong (modelExteriorJetCLM n (j + 1)) 0).comp secondJetLift)

theorem chart_exterior (A : RealForm M k) (hA : SmoothRealForm A)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    chartForm (exteriorRealForm A) x z =
      modelExteriorJetCLM n k (chartForm A x z, fderiv ℝ (chartForm A x) z) := by
  apply modelFormCoefficientMap_injective n (k + 1)
  funext I
  exact (exteriorRealForm_represents A hA x z hz I).trans
    (chartForm_extDeriv_apply A hA x hz I).symm

theorem chart_codifferential (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M (k + 1))
    (hA : SmoothRealForm A) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) :
    chartForm (codifferentialRealForm g.form A) x z =
      modelCodifferentialJetCLM g.form x z (chartForm A x z, fderiv ℝ (chartForm A x) z) := by
  rw [modelCodifferentialJetCLM_chart]
  apply modelFormCoefficientMap_injective n k
  funext I
  exact (codifferentialRealForm_represents g μ hμ A hA x z hz I).trans
    (codifferentialChartForm_coeff g.form A hA x hz I).symm

/-- Exact reconstruction of the original global Hodge expression, before splitting its symbol. -/
theorem hodgeSecondJetCLM_chart (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M k) (hA : SmoothRealForm A)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    chartForm (hodgeRealForm g.form k A) x z = hodgeSecondJetCLM g.form x z k
      (chartForm A x z, fderiv ℝ (chartForm A x) z, fderiv ℝ (fderiv ℝ (chartForm A x)) z) := by
  have hO := isOpen_extChartAt_target (I := ComplexModel n) x
  have hs := chartForm_contDiffOn A hA x
  have hd := (hs.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
  have hds : ContDiffOn ℝ ∞ (fderiv ℝ (chartForm A x)) (chartTarget x) :=
    hs.fderiv_of_isOpen hO (by simp)
  have hdd := (hds.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
  have he : chartForm (exteriorRealForm A) x =ᶠ[𝓝 z]
      (fun y => modelExteriorJetCLM n k (chartForm A x y, fderiv ℝ (chartForm A x) y)) := by
    filter_upwards [hO.mem_nhds hz] with y hy
    exact chart_exterior A hA x hy
  have hpe := prolong_actual (fun _ : ComplexVector n => modelExteriorJetCLM n k)
    (chartForm A x) z (differentiableAt_const _) hd hdd
  rw [fderiv_const_apply] at hpe
  cases k with
  | zero =>
      rw [hodgeRealForm, chart_codifferential g μ hμ _ (exteriorRealForm_smooth A hA) x hz]
      simp only [hodgeSecondJetCLM, ContinuousLinearMap.comp_apply, hpe]
      rw [← he.eq_of_nhds, ← he.fderiv_eq]
  | succ j =>
      have hδ : chartForm (codifferentialRealForm g.form A) x =ᶠ[𝓝 z]
          (fun y => modelCodifferentialJetCLM g.form x y
            (chartForm A x y, fderiv ℝ (chartForm A x) y)) := by
        filter_upwards [hO.mem_nhds hz] with y hy
        exact chart_codifferential g μ hμ A hA x hy
      have hc := ((codifferentialJet_contDiffOn (k := j) g x).contDiffAt
        (hO.mem_nhds hz)).differentiableAt (by simp)
      have hpδ := prolong_actual (modelCodifferentialJetCLM (k := j) g.form x)
        (chartForm A x) z hc hd hdd
      rw [hodgeRealForm]
      change chartForm (exteriorRealForm (codifferentialRealForm g.form A)) x z +
        chartForm (codifferentialRealForm g.form (exteriorRealForm A)) x z = _
      rw [chart_exterior _ (codifferentialRealForm_smooth g μ hμ A hA) x hz,
        chart_codifferential g μ hμ _ (exteriorRealForm_smooth A hA) x hz]
      simp only [hodgeSecondJetCLM, add_apply,
        ContinuousLinearMap.comp_apply, hpe, hpδ]
      rw [← he.eq_of_nhds, ← he.fderiv_eq, ← hδ.eq_of_nhds, ← hδ.fderiv_eq]

/-- The fixed dual real coordinate covectors. -/
def coord (i : RIdx n) : ComplexVector n →L[ℝ] ℝ :=
  ((realModelBasis n).coord i).toContinuousLinearMap

@[simp] theorem coord_realVec (i j : RIdx n) : coord i (realVec j) = if j = i then 1 else 0 := by
  classical
  by_cases h : j = i
  · subst j; simp [coord, ← realModelBasis_apply]
  · simp [coord, ← realModelBasis_apply, h, Ne.symm h]

/-- Expansion of a genuine derivative CLM in the real coordinate basis. -/
theorem derivative_decomposition {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D : ComplexVector n →L[ℝ] F) :
    D = ∑ i, (coord i).smulRight (D (realVec i)) := by
  apply ContinuousLinearMap.ext
  intro v
  have h := congrArg D ((realModelBasis n).sum_repr v)
  simpa only [map_sum, map_smul, sum_apply,
    ContinuousLinearMap.smulRight_apply, coord, LinearMap.coe_toContinuousLinearMap',
    Basis.coord_apply, realModelBasis_apply] using h.symm

/-- Exterior differentiation of an arbitrary first derivative, with its actual symbols. -/
theorem exterior_decomposition (P : Fiber n k) (D : ComplexVector n →L[ℝ] Fiber n k) :
    modelExteriorJetCLM n k (P, D) =
      ∑ i, modelExteriorSymbol (coord i) (D (realVec i)) := by
  change ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexVector n) ℝ D = _
  conv_lhs => rw [derivative_decomposition D]
  rw [map_sum]
  rfl

/-- The exterior calculator is independent of the value slot. -/
theorem exterior_value (P Q : Fiber n k) (D : ComplexVector n →L[ℝ] Fiber n k) :
    modelExteriorJetCLM n k (P, D) = modelExteriorJetCLM n k (Q, D) := rfl

/-- Its coefficient-constant prolongation depends only on the second derivative. -/
theorem exterior_prolong (P : Fiber n k) (D : ComplexVector n →L[ℝ] Fiber n k)
    (H : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] Fiber n k) :
    prolong (modelExteriorJetCLM n k) 0 (secondJetLift (P, D, H)) =
      (modelExteriorJetCLM n k (P, D),
        (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexVector n) ℝ).comp H) := by
  rw [secondJetLift_apply, prolong_apply]
  congr 1
  ext v
  simp [modelExteriorJetCLM]

/-- The genuine principal first-derivative part of the codifferential. -/
theorem codifferential_principal (g : HermitianField M) (x : M.Carrier) (z : ComplexVector n)
    (D : ComplexVector n →L[ℝ] Fiber n (k + 1)) :
    modelCodifferentialJetCLM g x z (0, D) =
      -∑ a, ∑ b, (realMetricFn g x z)⁻¹ a b • (D (realVec a)).curryLeft (realVec b) := by
  simp [modelCodifferentialJetCLM_apply]

/-- Exterior multiplication, bundled linearly in the form argument. -/
def wedgeCLM (ξ : ComplexVector n →L[ℝ] ℝ) : Fiber n k →L[ℝ] Fiber n (k + 1) :=
  (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexVector n) ℝ).comp
    (ContinuousLinearMap.smulRightL ℝ (ComplexVector n) (Fiber n k) ξ)

@[simp] theorem wedgeCLM_apply (ξ : ComplexVector n →L[ℝ] ℝ) (P : Fiber n k) :
    wedgeCLM ξ P = modelExteriorSymbol ξ P := rfl

/-- The derivative-only codifferential, with an arbitrary frozen inverse metric. -/
def deltaPrincipalCLM (B : Matrix (RIdx n) (RIdx n) ℝ) :
    (ComplexVector n →L[ℝ] Fiber n (k + 1)) →L[ℝ] Fiber n k :=
  -∑ a, ∑ b, B a b • ((modelContractionCLM (realVec b)).comp
    (ContinuousLinearMap.apply ℝ (Fiber n (k + 1)) (realVec a)))

theorem deltaPrincipalCLM_apply (B : Matrix (RIdx n) (RIdx n) ℝ)
    (D : ComplexVector n →L[ℝ] Fiber n (k + 1)) :
    deltaPrincipalCLM B D = -∑ a, ∑ b, B a b • (D (realVec a)).curryLeft (realVec b) := by
  simp [deltaPrincipalCLM, modelContractionCLM_apply]

theorem codifferential_eq_deltaPrincipal (g : HermitianField M) (x : M.Carrier)
    (z : ComplexVector n) (D : ComplexVector n →L[ℝ] Fiber n (k + 1)) :
    modelCodifferentialJetCLM g x z (0, D) = deltaPrincipalCLM (realMetricFn g x z)⁻¹ D := by
  rw [codifferential_principal, deltaPrincipalCLM_apply]

/-- Exact principal part at degree zero, where no Hessian symmetry is needed. -/
theorem principal_zero (B : Matrix (RIdx n) (RIdx n) ℝ)
    (H : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] Fiber n 0) :
    deltaPrincipalCLM B
      ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexVector n) ℝ).comp H) =
      -∑ a, ∑ b, B a b • H (realVec a) (realVec b) := by
  rw [deltaPrincipalCLM_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  change (modelExteriorJetCLM n 0 (0, H (realVec a))).curryLeft (realVec b) = _
  rw [exterior_decomposition]
  change modelContractionCLM (realVec b) (∑ i, modelExteriorSymbol (coord i)
    (H (realVec a) (realVec i))) = _
  rw [map_sum]
  simp [modelContractionCLM_apply, modelExteriorSymbol_curry_zero]

/-- Cartan cancellation for every symmetric actual second-derivative tensor.
The statement does not identify arbitrary nonsymmetric second jets. -/
theorem principal_succ (B : Matrix (RIdx n) (RIdx n) ℝ)
    (H : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] Fiber n (k + 1))
    (hH : ∀ u v, H u v = H v u) :
    modelExteriorJetCLM n k (0, (deltaPrincipalCLM B).comp H) +
      deltaPrincipalCLM B
        ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexVector n) ℝ).comp H) =
      -∑ a, ∑ b, B a b • H (realVec a) (realVec b) := by
  rw [exterior_decomposition, deltaPrincipalCLM_apply]
  have hleft : (∑ i, modelExteriorSymbol (coord i)
      ((deltaPrincipalCLM B) (H (realVec i)))) =
      -∑ a, ∑ b, B a b • ∑ i,
        modelExteriorSymbol (coord i) ((H (realVec a) (realVec i)).curryLeft (realVec b)) := by
    simp only [deltaPrincipalCLM_apply, ← wedgeCLM_apply, map_neg, map_sum, map_smul]
    rw [Finset.sum_neg_distrib]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hH (realVec i) (realVec a)]
  have hright : (∑ a, ∑ b, B a b •
      (((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexVector n) ℝ).comp H)
        (realVec a)).curryLeft (realVec b)) =
      ∑ a, ∑ b, B a b • ∑ i,
        (modelExteriorSymbol (coord i) (H (realVec a) (realVec i))).curryLeft (realVec b) := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    congr 1
    change (modelExteriorJetCLM n (k + 1) (0, H (realVec a))).curryLeft (realVec b) = _
    rw [exterior_decomposition]
    change modelContractionCLM (realVec b) (∑ i, modelExteriorSymbol (coord i)
      (H (realVec a) (realVec i))) = _
    rw [map_sum]
    rfl
  change (∑ i, modelExteriorSymbol (coord i) ((deltaPrincipalCLM B) (H (realVec i)))) +
    -(∑ a, ∑ b, B a b •
      (((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexVector n) ℝ).comp H)
        (realVec a)).curryLeft (realVec b)) = _
  rw [hleft, hright, ← neg_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [← smul_add, ← Finset.sum_add_distrib]
  congr 1
  have hcartan (i : RIdx n) := modelExteriorSymbol_curry_add (coord i)
    (H (realVec a) (realVec i)) (realVec b)
  simp_rw [add_comm (modelExteriorSymbol (coord _) _), hcartan, coord_realVec]
  simp

/-- The second-jet family has genuinely smooth CLM-valued coefficients. -/
theorem hodgeSecondJetCLM_contDiffOn (g : SmoothMetric M) (x : M.Carrier) (k : ℕ) :
    ContDiffOn ℝ ∞ (fun z => hodgeSecondJetCLM g.form x z k) (chartTarget x) := by
  apply contDiffOn_clm_apply.mpr
  intro p
  cases k with
  | zero =>
      exact (codifferentialJet_contDiffOn (k := 0) g x).clm_apply contDiffOn_const
  | succ j =>
      apply ContDiffOn.add
      · exact (modelExteriorJetCLM n j).contDiff.comp_contDiffOn
          (prolong_contDiffOn (modelCodifferentialJetCLM (k := j) g.form x) (chartTarget x)
            (codifferentialJet_contDiffOn g x)
            (isOpen_extChartAt_target (I := ComplexModel n) x)
            (secondJetLift p).1 (secondJetLift p).2)
      · exact (codifferentialJet_contDiffOn (k := j + 1) g x).clm_apply contDiffOn_const

/-- The actual Hodge second-jet calculator has the negative scalar metric principal part. -/
theorem hodgeSecondJetCLM_principal (g : HermitianField M) (x : M.Carrier)
    (z : ComplexVector n) (H : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] Fiber n k)
    (hH : ∀ u v, H u v = H v u) :
    hodgeSecondJetCLM g x z k (0, 0, H) =
      -∑ a, ∑ b, (realMetricFn g x z)⁻¹ a b • H (realVec a) (realVec b) := by
  cases k with
  | zero =>
      simp only [hodgeSecondJetCLM, ContinuousLinearMap.comp_apply, exterior_prolong]
      have he : modelExteriorJetCLM n 0 (0, 0) = 0 := map_zero _
      rw [he, codifferential_eq_deltaPrincipal, principal_zero]
  | succ j =>
      simp only [hodgeSecondJetCLM, add_apply, ContinuousLinearMap.comp_apply,
        secondJetLift_apply, prolong_apply]
      have he : modelExteriorJetCLM n (j + 1) (0, 0) = 0 := map_zero _
      have hd : modelCodifferentialJetCLM (k := j) g x z (0, 0) = 0 := map_zero _
      rw [he, hd]
      have hder : (fderiv ℝ (modelCodifferentialJetCLM (k := j) g x) z).flip
          ((0 : Fiber n (j + 1)), 0) = 0 := map_zero _
      rw [hder, zero_add, codifferential_eq_deltaPrincipal]
      have hcomp : (modelCodifferentialJetCLM (k := j) g x z).comp
          (((0 : ComplexVector n →L[ℝ] Fiber n (j + 1))).prod H) =
          (deltaPrincipalCLM (realMetricFn g x z)⁻¹).comp H := by
        apply ContinuousLinearMap.ext
        intro v
        exact codifferential_eq_deltaPrincipal g x z (H v)
      rw [hcomp]
      have hex : (0 : ComplexVector n →L[ℝ]
          Jet (ComplexVector n) (Fiber n (j + 1)) →L[ℝ] Fiber n (j + 2)).flip
          ((0 : Fiber n (j + 1)), 0) = 0 := map_zero _
      rw [hex, zero_add]
      exact principal_succ _ H hH

section Injections

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Injection of the value into a second jet. -/
def valueIn : F →L[ℝ] SecondJet E F := ContinuousLinearMap.inl ℝ _ _

/-- Injection of a first derivative into a second jet. -/
def derivativeIn : (E →L[ℝ] F) →L[ℝ] SecondJet E F :=
  (ContinuousLinearMap.inr ℝ F _).comp (ContinuousLinearMap.inl ℝ _ _)

end Injections

/-- The smooth zeroth-order coefficient of the actual Hodge operator. -/
def E0 (g : HermitianField M) (x : M.Carrier) (k : ℕ) (z : ComplexVector n) :
    Fiber n k →L[ℝ] Fiber n k :=
  (hodgeSecondJetCLM g x z k).comp valueIn

/-- The smooth first-order coefficients of the actual Hodge operator. -/
def E1 (g : HermitianField M) (x : M.Carrier) (k : ℕ) (i : RIdx n) (z : ComplexVector n) :
    Fiber n k →L[ℝ] Fiber n k :=
  (hodgeSecondJetCLM g x z k).comp (derivativeIn.comp
    (ContinuousLinearMap.smulRightL ℝ (ComplexVector n) (Fiber n k) (coord i)))

theorem E0_contDiffOn (g : SmoothMetric M) (x : M.Carrier) (k : ℕ) :
    ContDiffOn ℝ ∞ (E0 g.form x k) (chartTarget x) :=
  (hodgeSecondJetCLM_contDiffOn g x k).clm_comp contDiffOn_const

theorem E1_contDiffOn (g : SmoothMetric M) (x : M.Carrier) (k : ℕ) (i : RIdx n) :
    ContDiffOn ℝ ∞ (E1 g.form x k i) (chartTarget x) :=
  (hodgeSecondJetCLM_contDiffOn g x k).clm_comp contDiffOn_const

/-- Exact lower-order split, with the principal tensor kept separate until symmetry is supplied. -/
theorem hodgeSecondJetCLM_split (g : HermitianField M) (x : M.Carrier)
    (z : ComplexVector n) (P : Fiber n k) (D : ComplexVector n →L[ℝ] Fiber n k)
    (H : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] Fiber n k) :
    hodgeSecondJetCLM g x z k (P, D, H) =
      hodgeSecondJetCLM g x z k (0, 0, H) +
        (∑ i, E1 g x k i z (D (realVec i))) + E0 g x k z P := by
  have hD : derivativeIn D = ∑ i, derivativeIn ((coord i).smulRight (D (realVec i))) := by
    conv_lhs => rw [derivative_decomposition D]
    rw [map_sum]
  have hp : (P, D, H) = (0, 0, H) + (0, D, 0) + (P, 0, 0) := by
    ext <;> simp
  rw [hp, map_add, map_add]
  change hodgeSecondJetCLM g x z k (0, 0, H) +
    hodgeSecondJetCLM g x z k (derivativeIn D) + hodgeSecondJetCLM g x z k (P, 0, 0) = _
  rw [hD, map_sum]
  rfl

/-- Actual chart expansion on every smooth form, with no compactness restriction. -/
theorem chart_hodge_expansion (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M k) (hA : SmoothRealForm A)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    chartForm (hodgeRealForm g.form k A) x z =
      -(∑ i, ∑ j, (realMetricFn g.form x z)⁻¹ i j •
        fderiv ℝ (fderiv ℝ (chartForm A x)) z (realVec i) (realVec j)) +
      (∑ i, E1 g.form x k i z (fderiv ℝ (chartForm A x) z (realVec i))) +
      E0 g.form x k z (chartForm A x z) := by
  rw [hodgeSecondJetCLM_chart g μ hμ A hA x hz, hodgeSecondJetCLM_split]
  congr 2
  apply hodgeSecondJetCLM_principal
  exact ((chartForm_contDiffOn A hA x).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).isSymmSndFDerivAt (by simp)

/-- A fixed directional derivative of the first derivative is the corresponding true second jet. -/
theorem second_derivative_direction (G : ComplexVector n → Fiber n k)
    (hG : ContDiff ℝ ∞ G) (z u v : ComplexVector n) :
    fderiv ℝ (fderiv ℝ G) z u v =
      fderiv ℝ (fun y => fderiv ℝ G y v) z u := by
  have hd : DifferentiableAt ℝ (fderiv ℝ G) z :=
    ((hG.contDiffAt.fderiv_right (m := ∞) (by simp))).differentiableAt (by simp)
  have h := ((ContinuousLinearMap.apply ℝ (Fiber n k) v).hasFDerivAt.comp z hd.hasFDerivAt).fderiv
  exact (DFunLike.congr_fun h u).symm

/-- The requested second-order chart expansion for every genuine compact smooth model test.
The lower-order coefficients are the smooth CLMs `E1` and `E0`; the principal part has coefficient one. -/
theorem chart_hodge_pushforward_expansion (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    (G : ComplexVector n → Fiber n k) (hG : ContDiff ℝ ∞ G)
    (hcG : HasCompactSupport G) (hGO : tsupport G ⊆ chartTarget x)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    chartForm (hodgeRealForm g.form k (chartFormPushforward x G)) x z =
      -(∑ i, ∑ j, (realMetricFn g.form x z)⁻¹ i j •
        fderiv ℝ (fun y => fderiv ℝ G y ((realModelBasis n) j)) z ((realModelBasis n) i)) +
      (∑ i, E1 g.form x k i z (fderiv ℝ G z ((realModelBasis n) i))) + E0 g.form x k z (G z) := by
  have hA := chartFormPushforward_smooth x G hG hcG hGO
  have hF : chartForm (chartFormPushforward x G) x =ᶠ[𝓝 z] G := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with y hy
    exact chartFormPushforward_to_chart x G hy
  have h := chart_hodge_expansion g μ hμ (chartFormPushforward x G) hA x hz
  rw [hF.eq_of_nhds, hF.fderiv_eq, hF.fderiv.fderiv_eq] at h
  simpa only [realModelBasis_apply, second_derivative_direction G hG] using h

/-- Smooth lower-order coefficient operators exist for the actual original Hodge expression. -/
theorem exists_chart_hodge_second_order_expansion (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier) (k : ℕ) :
    ∃ (E : RIdx n → ComplexVector n → Fiber n k →L[ℝ] Fiber n k)
      (Ezero : ComplexVector n → Fiber n k →L[ℝ] Fiber n k),
      (∀ i, ContDiffOn ℝ ∞ (E i) (chartTarget x)) ∧
      ContDiffOn ℝ ∞ Ezero (chartTarget x) ∧
      ∀ (G : ComplexVector n → Fiber n k), ContDiff ℝ ∞ G →
        HasCompactSupport G → tsupport G ⊆ chartTarget x →
        ∀ z ∈ chartTarget x,
        chartForm (hodgeRealForm g.form k (chartFormPushforward x G)) x z =
          -(∑ i, ∑ j, (realMetricFn g.form x z)⁻¹ i j •
            fderiv ℝ (fun y => fderiv ℝ G y ((realModelBasis n) j)) z ((realModelBasis n) i)) +
          (∑ i, E i z (fderiv ℝ G z ((realModelBasis n) i))) + Ezero z (G z) := by
  refine ⟨E1 g.form x k, E0 g.form x k, E1_contDiffOn g x k, E0_contDiffOn g x k, ?_⟩
  intro G hG hcG hGO z hz
  exact chart_hodge_pushforward_expansion g μ hμ x G hG hcG hGO hz

end Geometry

end HodgeJets

end Yau.LeafProofs.L03
