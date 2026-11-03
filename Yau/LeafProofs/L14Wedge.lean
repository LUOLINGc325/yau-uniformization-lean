import Yau.LeafProofs.L14TwoContraction
import Yau.LeafProofs.L14TwoCoordinates

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Manifold Topology ContDiff ComplexOrder ENNReal Matrix Kronecker
open MeasureTheory Bundle Filter Module
namespace Yau.LeafProofs.L14Aux
open BundleDbar

section WedgeAlgebra
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [Module ℂ V]
  [IsScalarTower ℝ ℂ V] [AddCommGroup W] [Module ℝ W] [Module ℂ W]
  [IsScalarTower ℝ ℂ W]

/-- The exterior product of a conjugate-linear covector with a one-form. -/
def antiOneWedge (d : V →ₗ[ℝ] ℂ) (A : V [⋀^Fin 1]→ₗ[ℝ] W) :
    V [⋀^Fin 2]→ₗ[ℝ] W := by
  let L := (AlternatingMap.ofSubsingleton ℝ V W (0 : Fin 1)).symm A
  exact {
    toFun := fun v => d (v 0) • L (v 1) - d (v 1) • L (v 0)
    map_update_add' := by
      intro _ v k u w
      fin_cases k <;> simp [map_add, add_smul, smul_add] <;> abel
    map_update_smul' := by
      intro _ v k c u
      fin_cases k <;> simp [map_smul, smul_sub, smul_comm c]
      all_goals
        change (c • d u) • _ = _
        rw [smul_assoc, smul_comm c]
    map_eq_zero_of_eq' := by
      intro v k l h hne
      have he : v 0 = v 1 := by
        fin_cases k <;> fin_cases l
        · exact False.elim (hne rfl)
        · exact h
        · exact h.symm
        · exact False.elim (hne rfl)
      simp only [he, sub_self] }

omit [Module ℂ V] [IsScalarTower ℝ ℂ V] in
theorem antiOneWedge_apply (d : V →ₗ[ℝ] ℂ) (A : V [⋀^Fin 1]→ₗ[ℝ] W) (v : Fin 2 → V) :
    antiOneWedge d A v = d (v 0) • A (fun _ => v 1) - d (v 1) • A (fun _ => v 0) := rfl

omit [IsScalarTower ℝ ℂ V] in
theorem antiOneWedge_anti (d : V →ₗ[ℝ] ℂ) (A : V [⋀^Fin 1]→ₗ[ℝ] W)
    (hd : ∀ c v, d (c • v) = star c * d v)
    (hA : ∀ (v : Fin 1 → V) (i : Fin 1) (c : ℂ),
      A (Function.update v i (c • v i)) = star c • A v)
    (v : Fin 2 → V) (k : Fin 2) (c : ℂ) :
    antiOneWedge d A (Function.update v k (c • v k)) = star c • antiOneWedge d A v := by
  have ha (u : V) : A (fun _ => c • u) = star c • A (fun _ => u) := by
    have he : Function.update (fun _ : Fin 1 => u) 0 (c • u) = fun _ => c • u := by
      ext t; fin_cases t; rfl
    simpa only [he] using hA (fun _ => u) 0 c
  fin_cases k <;> simp [antiOneWedge_apply, hd, ha, smul_sub, mul_smul]
  all_goals exact smul_comm _ _ _
end WedgeAlgebra

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- The intrinsic antiholomorphic differential, defined using the canonical chart at the point. -/
def scalarBarDifferential (χ : M.Carrier → ℝ) (x : M.Carrier) : TangentVector M x →ₗ[ℝ] ℂ where
  toFun v := ∑ i, star ((chartFrameBasis x x (mem_extChartAt_source x)).coord i v) *
    wirtBar (fun w => Complex.ofReal (inChart x χ w)) (chartPt x x) (stdVec i)
  map_add' u v := by simp [map_add, star_add, add_mul, Finset.sum_add_distrib]
  map_smul' c v := by
    simp [LinearMap.map_smul_of_tower, Complex.real_smul, star_mul, Finset.mul_sum, mul_assoc, mul_left_comm]

theorem scalarBarDifferential_smul (χ : M.Carrier → ℝ) (x : M.Carrier)
    (c : ℂ) (v : TangentVector M x) :
    scalarBarDifferential χ x (c • v) = star c * scalarBarDifferential χ x v := by
  simp [scalarBarDifferential, map_smul, Finset.mul_sum, mul_assoc]

/-- The actual exterior product `∂̄χ ∧ U`, with no regularity requirement on `U`. -/
def gradientWedge (χ : M.Carrier → ℝ) (U : NQForm E 1) : NQForm E 2 := fun x => by
  letI : IsScalarTower ℝ ℂ ((TangentVector M x) [⋀^Fin n]→ₗ[ℂ] E x) := ⟨by
    intro c d A
    ext v
    exact smul_assoc c d (A v)⟩
  exact ⟨antiOneWedge (scalarBarDifferential χ x) (U x).1,
    antiOneWedge_anti _ _ (scalarBarDifferential_smul χ x) (U x).2⟩

theorem gradientWedge_apply (χ : M.Carrier → ℝ) (U : NQForm E 1)
    (x : M.Carrier) (v : Fin 2 → TangentVector M x) :
    (gradientWedge E χ U x).1 v = scalarBarDifferential χ x (v 0) • (U x).1 (fun _ => v 1) -
      scalarBarDifferential χ x (v 1) • (U x).1 (fun _ => v 0) := rfl

theorem scalarBarDifferential_chartVec (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (a : M.Carrier) (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) (j : Fin n) :
    scalarBarDifferential χ (chartInv a z) (chartVec a (chartInv a z) (stdVec j)) =
      wirtBar (fun w => Complex.ofReal (inChart a χ w)) z (stdVec j) := by
  let x := chartInv a z
  have hxx : x ∈ bundleChartSource (r := r) E x :=
    ⟨mem_extChartAt_source x, FiberBundle.mem_baseSet_trivializationAt' x⟩
  have he := congrArg (fun v : Fin n → ℂ => star (v j))
    (chartScalarWirt_overlap E χ hχ x a z ⟨hz,hxx⟩)
  have hc (i : Fin n) :
      (chartFrameBasis x x (mem_extChartAt_source x)).coord i (chartVec a x (stdVec j)) =
      fderiv ℂ (fun w => chartPt x (chartInv a w)) z (stdVec j) i := by
    have ht := congrFun (congrFun
      (chartFrameBasis_toMatrix_fderiv x a z hz.1 (mem_extChartAt_source x)) i) j
    change (chartFrameBasis x x (mem_extChartAt_source x)).coord i
      (chartFrameBasis a x ((extChartAt (ComplexModel n) a).map_target hz.1) j) = _ at ht
    rw [chartFrameBasis_apply] at ht
    exact ht
  change (∑ i, star ((chartFrameBasis x x _).coord i (chartVec a x (stdVec j))) *
    wirtBar (fun w => Complex.ofReal (inChart x χ w)) (chartPt x x) (stdVec i)) = _
  simp_rw [hc]
  symm
  simpa only [chartScalarWirt, ← star_wirtBar_ofReal, Matrix.vecMul, dotProduct,
    star_sum, star_mul, star_star, Matrix.of_apply, mul_comm] using he

/-- Exact coefficients in every genuine chart, for arbitrary raw one-forms. -/
theorem coefficients_gradientWedge_apply (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (U : NQForm E 1) (a : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ localDomain (r := r) E a) (i j : Fin n) (α : Fin r) :
    coefficients (r := r) E (gradientWedge E χ U) a z ![i,j] α =
      wirtBar (fun w => Complex.ofReal (inChart a χ w)) z (stdVec i) *
        coefficients (r := r) E U a z (fun _ => j) α -
      wirtBar (fun w => Complex.ofReal (inChart a χ w)) z (stdVec j) *
        coefficients (r := r) E U a z (fun _ => i) α := by
  unfold coefficients
  rw [gradientWedge_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    sub_apply, smul_apply, map_sub, map_smul, PiLp.sub_apply,
    PiLp.smul_apply, smul_eq_mul]
  rw [scalarBarDifferential_chartVec E χ hχ a z hz i,
    scalarBarDifferential_chartVec E χ hχ a z hz j]

theorem wedge_normSq_bound {n r : ℕ}
    (G : Matrix (Fin n) (Fin n) ℂ) (H : Matrix (Fin r) (Fin r) ℂ)
    (hG : G.PosDef) (hH : H.PosDef) (a : Fin n → ℂ) (F : Fin r → Fin n → ℂ) :
    twoCoefficientNormSq G H (fun α i j => a i * F α j - a j * F α i) ≤
      (star a ⬝ᵥ G⁻¹ *ᵥ a).re *
        (∑ α, ∑ β, H α β * (star (F α) ⬝ᵥ G⁻¹ *ᵥ F β)).re := by
  have he := wedge_contraction_energy_identity_coefficients G H hG a F
  have hn := (Complex.nonneg_iff.mp (hH.posSemidef.dotProduct_mulVec_nonneg
    (fun α => star a ⬝ᵥ G⁻¹ *ᵥ F α))).1
  linarith

/-- The sharp pointwise chart bound for the actual wedge tensor. -/
theorem chartGradientWedge_normSq_bound (g : HermitianField M) (h : Metric E)
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ) (U : NQForm E 1)
    (a : M.Carrier) (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) :
    chartTwoCoefficientNormSq (r := r) E g h (gradientWedge E χ U) a z ≤
      (star (fun i => wirtBar (fun w => Complex.ofReal (inChart a χ w)) z (stdVec i)) ⬝ᵥ
        (hMat g a z)⁻¹ *ᵥ
          (fun i => wirtBar (fun w => Complex.ofReal (inChart a χ w)) z (stdVec i))).re *
            chartOneCoefficientNormSq (r := r) E g h U a z := by
  rw [chartTwoCoefficientNormSq_eq, chartOneCoefficientNormSq_eq_fiber_sum]
  simp_rw [coefficients_gradientWedge_apply E χ hχ U a z hz]
  exact wedge_normSq_bound _ _ (hMat_posDef g a z hz.1)
    (metricMatrix_posDef E h a z hz) _ _

/-- The actual intrinsic wedge satisfies the sharp metric estimate. -/
theorem gradientWedge_normSq_le (g : HermitianField M) (h : Metric E)
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ) (U : NQForm E 1) (x : M.Carrier) :
    BundleDbar.formNormSq (r := r) E g h (gradientWedge E χ U) x ≤
      gradNormSq g χ x * BundleDbar.formNormSq (r := r) E g h U x := by
  have hxx : chartInv x (chartPt x x) = x :=
    chartInv_chartPt_of_mem x x (mem_chart_source _ _)
  have hz : chartPt x x ∈ localDomain (r := r) E x := by
    refine ⟨mem_extChartAt_target x, ?_⟩
    change chartInv x (chartPt x x) ∈ (localTriv (r := r) E x).baseSet
    rw [hxx]
    exact FiberBundle.mem_baseSet_trivializationAt' x
  have hw := formNormSq_two_chart_factor_matrix E g h (gradientWedge E χ U)
    x (chartPt x x) hz
  have hu := formNormSq_one_chart_factor E g h U x (chartPt x x) hz
  rw [hxx] at hw hu
  rw [hw, hu, gradNormSq_eq_chart_bar_norm]
  have he := mul_le_mul_of_nonneg_left
    (chartGradientWedge_normSq_bound E g h χ hχ U x (chartPt x x) hz)
    (inv_nonneg.mpr (L18Aux.hMat_det_re_pos g x hz.1).le)
  simpa only [mul_assoc, mul_left_comm] using he

/-- Finite-dimensional complex adjunction, including the exterior normalization. -/
theorem wedge_contraction_pairing {n r : ℕ}
    (G : Matrix (Fin n) (Fin n) ℂ) (H : Matrix (Fin r) (Fin r) ℂ)
    (a : Fin n → ℂ) (F : Fin r → Fin n → ℂ)
    (W : Fin r → Fin n → Fin n → ℂ) (hW : ∀ β k l, W β l k = -W β k l) (d : ℂ) :
    (1 / 2 : ℂ) * (∑ i, ∑ k, ∑ j, ∑ l, G i k * G j l *
      ((∑ α, ∑ β, star (a i * F α j - a j * F α i) * H α β * W β k l) / d)) =
      ∑ j, ∑ l, G j l * ((∑ α, ∑ β, star (F α j) * H α β *
        (∑ i, ∑ k, star (a i) * G i k * W β k l)) / d) := by
  classical
  let f := fun i k j l α β => G i k * G j l * star (a i) * star (F α j) * H α β * W β k l / d
  have hswap : (∑ i, ∑ k, ∑ j, ∑ l, ∑ α, ∑ β,
      G i k * G j l * star (a j) * star (F α i) * H α β * W β k l / d) =
      -(∑ i, ∑ k, ∑ j, ∑ l, ∑ α, ∑ β, f i k j l α β) := by
    let e : (Fin n × Fin n × Fin n × Fin n × Fin r × Fin r) ≃
        (Fin n × Fin n × Fin n × Fin n × Fin r × Fin r) :=
      { toFun := fun ⟨i,k,j,l,α,β⟩ => (j,l,i,k,α,β)
        invFun := fun ⟨i,k,j,l,α,β⟩ => (j,l,i,k,α,β)
        left_inv := by rintro ⟨i,k,j,l,α,β⟩; rfl
        right_inv := by rintro ⟨i,k,j,l,α,β⟩; rfl }
    have he := e.sum_comp (fun p => f p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)
    simp only [Fintype.sum_prod_type] at he
    rw [← he]
    simp only [← Finset.sum_neg_distrib]
    repeat' apply Finset.sum_congr rfl; intro _ _
    simp only [f, e, Equiv.coe_fn_mk]
    rw [hW]
    ring
  have hfirst : (∑ j, ∑ l, G j l * ((∑ α, ∑ β, star (F α j) * H α β *
      (∑ i, ∑ k, star (a i) * G i k * W β k l)) / d)) =
      ∑ i, ∑ k, ∑ j, ∑ l, ∑ α, ∑ β, f i k j l α β := by
    let e : (Fin n × Fin n × Fin r × Fin r × Fin n × Fin n) ≃
        (Fin n × Fin n × Fin n × Fin n × Fin r × Fin r) :=
      { toFun := fun ⟨j,l,α,β,i,k⟩ => (i,k,j,l,α,β)
        invFun := fun ⟨i,k,j,l,α,β⟩ => (j,l,α,β,i,k)
        left_inv := by rintro ⟨j,l,α,β,i,k⟩; rfl
        right_inv := by rintro ⟨i,k,j,l,α,β⟩; rfl }
    have he := e.sum_comp (fun p => f p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)
    simp only [Fintype.sum_prod_type] at he
    rw [← he]
    simp only [Finset.mul_sum, Finset.sum_div]
    repeat' apply Finset.sum_congr rfl; intro _ _
    simp only [f, e, Equiv.coe_fn_mk]
    ring
  rw [hfirst]
  have hterm (i k j l : Fin n) : G i k * G j l *
      ((∑ α, ∑ β, star (a i * F α j - a j * F α i) * H α β * W β k l) / d) =
      (∑ α, ∑ β, f i k j l α β) -
      (∑ α, ∑ β, G i k * G j l * star (a j) * star (F α i) * H α β * W β k l / d) := by
    simp only [← Finset.sum_sub_distrib, Finset.sum_div, Finset.mul_sum]
    repeat' apply Finset.sum_congr rfl; intro _ _
    dsimp only [f]
    rw [star_sub, star_mul, star_mul]
    ring
  simp_rw [hterm, Finset.sum_sub_distrib]
  rw [hswap]
  ring

include r in
/-- Exact pointwise complex adjunction with the existing metric contraction. -/
theorem gradientWedge_pairing (g : HermitianField M) (h : Metric E)
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ) (U : NQForm E 1) (W : NQForm E 2)
    (x : M.Carrier) :
    twoFormPairing E g h (gradientWedge E χ U) W x =
      oneFormPairing E g h U (twoGradientContraction E g χ W) x := by
  have hxx : chartInv x (chartPt x x) = x :=
    chartInv_chartPt_of_mem x x (mem_chart_source _ _)
  have hz : chartPt x x ∈ localDomain (r := r) E x := by
    refine ⟨mem_extChartAt_target x, ?_⟩
    change chartInv x (chartPt x x) ∈ (localTriv (r := r) E x).baseSet
    rw [hxx]
    exact FiberBundle.mem_baseSet_trivializationAt' x
  rw [← hxx, twoFormPairing_inChart E g h _ W x _ hz,
    oneFormPairing_inChart E g h U _ x _ hz]
  simp_rw [coefficients_gradientWedge_apply E χ hχ U x _ hz,
    coefficients_twoGradientContraction_apply E g χ hχ W x _ hz]
  exact wedge_contraction_pairing _ _ _ _ _
    (fun β k l => coefficients_two_skew E W x (chartPt x x) k l β) _

/-- Smooth scalar differentiation and multiplication preserve local square integrability. -/
theorem locallyL2_gradientWedge (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (U : NQForm E 1) (hU : LocallyL2 (r := r) E U) :
    LocallyL2 (r := r) E (gradientWedge E χ U) := by
  intro a I α
  let O := localDomain (r := r) E a
  let C := fun i z => wirtBar (fun w => Complex.ofReal (inChart a χ w)) z (stdVec i)
  have hχC : ContDiffOn ℝ ∞ (fun w => Complex.ofReal (inChart a χ w)) O :=
    ((hχ a).continuousLinearMap_comp Complex.ofRealCLM).mono Set.inter_subset_left
  have hC (i : Fin n) : ContinuousOn (C i) O :=
    (wirtBar_contDiffOn (localDomain_isOpen E a) _ hχC (stdVec i)).continuousOn
  have hcoeff (z : ComplexVector n) (hz : z ∈ O) :
      coefficients (r := r) E (gradientWedge E χ U) a z I α =
      C (I 0) z * coefficients (r := r) E U a z (fun _ => I 1) α -
        C (I 1) z * coefficients (r := r) E U a z (fun _ => I 0) α := by
    have hI : I = ![I 0,I 1] := by ext t; fin_cases t <;> rfl
    rw [hI, coefficients_gradientWedge_apply E χ hχ U a z hz]
    rfl
  have hmC (i : Fin n) : AEStronglyMeasurable (C i) ((lebesgueC n).restrict O) :=
    (hC i).aestronglyMeasurable (localDomain_isOpen E a).measurableSet
  refine ⟨?_, ?_⟩
  · apply (((hmC (I 0)).mul (hU a (fun _ => I 1) α).1).sub
      ((hmC (I 1)).mul (hU a (fun _ => I 0) α).1)).congr
    filter_upwards [ae_restrict_mem (localDomain_isOpen E a).measurableSet] with z hz
    exact (hcoeff z hz).symm
  · intro K hK hs
    have ht (i j : Fin n) : MemLp
        (fun z => C i z * coefficients (r := r) E U a z (fun _ => j) α)
        2 ((lebesgueC n).restrict K) := memLp_continuousOn_mul_compact K hK _ _
      ((hC i).mono hs) (locallyL2_coefficients_memLp E U hU a (fun _ => j) α K hK hs)
    have hm := (ht (I 0) (I 1)).sub (ht (I 1) (I 0))
    apply lintegral_norm_sq_lt_top_of_memLp
    exact MemLp.ae_eq ((ae_restrict_mem hK.measurableSet).mono
      fun z hz => (hcoeff z (hs hz)).symm) hm

theorem weightedNormSq_gradientWedge_le (g : HermitianField M) (μ : Measure M.Carrier)
    (h : Metric E) (φ : M.Carrier → ℝ) (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (U : NQForm E 1) (C : ℝ) (hC : 0 ≤ C) (hgrad : ∀ x, gradNormSq g χ x ≤ C) :
    weightedNormSq (r := r) E g h μ φ (gradientWedge E χ U) ≤
      ENNReal.ofReal C * weightedNormSq (r := r) E g h μ φ U := by
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (C * (BundleDbar.formNormSq (r := r) E g h U x * Real.exp (-φ x))) ∂μ := by
      apply lintegral_mono
      intro x
      change ENNReal.ofReal (BundleDbar.formNormSq (r := r) E g h
        (gradientWedge E χ U) x * Real.exp (-φ x)) ≤ _
      apply ENNReal.ofReal_le_ofReal
      have he := (gradientWedge_normSq_le (r := r) E g h χ hχ U x).trans
        (mul_le_mul_of_nonneg_right (hgrad x) (formNormSq_one_nonneg E g h U x))
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
    _ = _ := by
      simp only [ENNReal.ofReal_mul hC]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem weightedL2_gradientWedge (g : HermitianField M) (μ : Measure M.Carrier)
    (h : Metric E) (φ : M.Carrier → ℝ) (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (U : NQForm E 1) (hU : WeightedL2 (r := r) E g h μ φ U)
    (C : ℝ) (hC : 0 ≤ C) (hgrad : ∀ x, gradNormSq g χ x ≤ C) :
    WeightedL2 (r := r) E g h μ φ (gradientWedge E χ U) :=
  ⟨locallyL2_gradientWedge E χ hχ U hU.1,
    (weightedNormSq_gradientWedge_le (r := r) E g μ h φ χ hχ U C hC hgrad).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hU.2)⟩

end Yau.LeafProofs.L14Aux
