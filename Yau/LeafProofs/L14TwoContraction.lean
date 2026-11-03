import Yau.LeafProofs.L14Contraction
import Yau.LeafProofs.L14TwoChartGeometry

/-! The zero-order contraction of an actual, possibly rough `(n,2)` form. -/

noncomputable section
open scoped Manifold Topology ContDiff ComplexOrder ENNReal Matrix Kronecker
open MeasureTheory Bundle Filter Module
namespace Yau.LeafProofs.L14Aux
open BundleDbar
variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- Leave the first antiholomorphic slot free and fix the second slot. -/
def twoFirstSlotSlice (W : NQForm E 2) (V : ∀ x, TangentVector M x) : NQForm E 1 :=
  fun x => ⟨antiCoordinateSlice (W x).1 ![0,V x] 0,
    antiCoordinateSlice_anti (W x).1 (W x).2 _ _⟩

/-- Fix the first antiholomorphic slot and leave the second slot free. -/
def twoSecondSlotSlice (W : NQForm E 2) (V : ∀ x, TangentVector M x) : NQForm E 1 :=
  fun x => ⟨antiCoordinateSlice (W x).1 ![V x,0] 1,
    antiCoordinateSlice_anti (W x).1 (W x).2 _ _⟩

/-- Contract the first antiholomorphic slot against the metric dual of `∂χ`.
The definition uses actual fiber tensors and requires no regularity of `W`. -/
def twoGradientContraction (g : HermitianField M) (χ : M.Carrier → ℝ)
    (W : NQForm E 2) : NQForm E 1 := fun x =>
  (show antiComplexSubmodule E x 1 from ∑ i, ∑ k,
    (chartScalarWirt χ x (chartPt x x) i * (hMat g x (chartPt x x))⁻¹ i k) •
    (show antiComplexSubmodule E x 1 from
      twoSecondSlotSlice E W (fun y => chartVec y y (stdVec k)) x))

set_option backward.isDefEq.respectTransparency false in
theorem scalarGradientContraction_value (g : HermitianField M) (χ : M.Carrier → ℝ)
    (u : NQForm E 1) (x : M.Carrier) :
    (scalarGradientContraction (r := r) E g χ u x).1 Fin.elim0 =
      ∑ i, ∑ k, (chartScalarWirt χ x (chartPt x x) i * (hMat g x (chartPt x x))⁻¹ i k) •
        (u x).1 (fun _ => chartVec x x (stdVec k)) := by
  classical
  apply sub_eq_zero.mp
  apply alternating_eq_zero_of_apply_basis_eq_zero (Module.Free.chooseBasis ℂ (E x))
    (chartFrameBasis x x (mem_extChartAt_source x))
  simp only [sub_apply]
  apply sub_eq_zero.mpr
  let hx : x ∈ bundleChartSource (r := r) E x :=
    ⟨mem_extChartAt_source x, FiberBundle.mem_baseSet_trivializationAt' x⟩
  have hv := topTensorValueEquiv_symm_coordinates (r := r) E x x hx
    (chartScalarContraction (r := r) E g χ u x (chartPt x x))
  change ((scalarGradientContraction (r := r) E g χ u x).1 Fin.elim0)
    (chartFrameBasis x x hx.1) = _
  rw [show ((scalarGradientContraction (r := r) E g χ u x).1 Fin.elim0)
      (chartFrameBasis x x hx.1) =
      (localTriv (r := r) E x).symmL ℂ x
        (chartScalarContraction (r := r) E g χ u x (chartPt x x)) from hv]
  apply ((localTriv (r := r) E x).continuousLinearEquivAt ℂ x hx.2).injective
  have htr := (localTriv (r := r) E x).coe_continuousLinearEquivAt_eq (R := ℂ) hx.2
  simp only [htr, Trivialization.continuousLinearMapAt_symmL _ hx.2, sum_apply,
    smul_apply, map_sum, map_smul]
  ext α
  rw [chartScalarContraction_apply]
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, chartScalarWirt,
    star_wirtBar_ofReal]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  rw [coefficients_at_chartPt E u x x hx.1]
  rw [show (fun t => chartVec x x (stdVec t)) = chartFrameBasis x x hx.1 from
    funext (fun t => (chartFrameBasis_apply x x hx.1 t).symm)]

set_option backward.isDefEq.respectTransparency false in
theorem twoGradientContraction_apply (g : HermitianField M) (χ : M.Carrier → ℝ)
    (W : NQForm E 2) (V : ∀ x, TangentVector M x) (x : M.Carrier) :
    (twoGradientContraction E g χ W x).1 (fun _ => V x) =
      (scalarGradientContraction (r := r) E g χ (twoFirstSlotSlice E W V) x).1 Fin.elim0 := by
  rw [scalarGradientContraction_value]
  simp only [twoGradientContraction, Submodule.coe_sum, sum_apply,
    twoSecondSlotSlice, twoFirstSlotSlice, antiCoordinateSlice_zero_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  change (_ • antiCoordinateSlice (W x).1 ![chartVec x x (stdVec k),0] 1)
    (fun _ => V x) = _
  rw [smul_apply, antiCoordinateSlice_one_apply]

set_option backward.isDefEq.respectTransparency false in
/-- The contraction coefficients in every genuine chart and bundle frame. -/
theorem coefficients_twoGradientContraction_apply (g : HermitianField M)
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ) (W : NQForm E 2)
    (a : M.Carrier) (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a)
    (j : Fin n) (α : Fin r) :
    coefficients (r := r) E (twoGradientContraction E g χ W) a z (fun _ => j) α =
      ∑ i, ∑ k, star (wirtBar (fun w => Complex.ofReal (inChart a χ w)) z (stdVec i)) *
        (hMat g a z)⁻¹ i k * coefficients (r := r) E W a z ![k,j] α := by
  let V := fun y => chartVec a y (stdVec j)
  have he := twoGradientContraction_apply (r := r) E g χ W V (chartInv a z)
  have hc : coefficients (r := r) E (twoGradientContraction E g χ W) a z (fun _ => j) =
      coefficients (r := r) E (scalarGradientContraction (r := r) E g χ (twoFirstSlotSlice E W V)) a z Fin.elim0 := by
    unfold coefficients
    rw [he]
    rfl
  rw [congrArg (fun v : ComplexVector r => v α) hc,
    coefficients_scalarGradientContraction_apply E g χ hχ _ a z hz α]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  unfold coefficients twoFirstSlotSlice V
  rw [antiCoordinateSlice_zero_apply]
  have hh : ![chartVec a (chartInv a z) (stdVec k), chartVec a (chartInv a z) (stdVec j)] =
      (fun t : Fin 2 => chartVec a (chartInv a z) (stdVec (![k,j] t))) := by
    ext t
    fin_cases t <;> rfl
  rw [hh]

theorem scalar_contraction_bound_fintype {n : ℕ} {ι : Type*} [Fintype ι]
    (G : Matrix (Fin n) (Fin n) ℂ) (H : Matrix ι ι ℂ)
    (hG : G.PosDef) (hH : H.PosDef) (a : Fin n → ℂ) (F : ι → Fin n → ℂ) :
    (star (fun α => star a ⬝ᵥ G⁻¹ *ᵥ F α) ⬝ᵥ H *ᵥ
      (fun α => star a ⬝ᵥ G⁻¹ *ᵥ F α)).re ≤
        (star a ⬝ᵥ G⁻¹ *ᵥ a).re *
          (∑ α, ∑ β, H α β * (star (F α) ⬝ᵥ G⁻¹ *ᵥ F β)).re := by
  classical
  let e := (Fintype.equivFin ι).symm
  have he := scalar_contraction_bound G (H.submatrix e e) hG (hH.submatrix e.injective)
    a (fun i => F (e i))
  have hleft : (star (fun α => star a ⬝ᵥ G⁻¹ *ᵥ F (e α)) ⬝ᵥ H.submatrix e e *ᵥ
      (fun α => star a ⬝ᵥ G⁻¹ *ᵥ F (e α))) =
      (star (fun α => star a ⬝ᵥ G⁻¹ *ᵥ F α) ⬝ᵥ H *ᵥ
      (fun α => star a ⬝ᵥ G⁻¹ *ᵥ F α)) := by
    let c := fun α => star a ⬝ᵥ G⁻¹ *ᵥ F α
    change (∑ α, star (c (e α)) * ∑ β, H (e α) (e β) * c (e β)) =
      ∑ α, star (c α) * ∑ β, H α β * c β
    have hs (α : ι) : (∑ β, H α (e β) * c (e β)) = ∑ β, H α β * c β :=
      e.sum_comp (fun β => H α β * c β)
    simp_rw [hs]
    exact e.sum_comp (fun α : ι => star (c α) * ∑ β, H α β * c β)
  have hright : (∑ α, ∑ β, H.submatrix e e α β *
      (star (F (e α)) ⬝ᵥ G⁻¹ *ᵥ F (e β))) =
      ∑ α, ∑ β, H α β * (star (F α) ⬝ᵥ G⁻¹ *ᵥ F β) := by
    have hs (α : ι) : (∑ β, H α (e β) *
        (star (F α) ⬝ᵥ G⁻¹ *ᵥ F (e β))) =
        ∑ β, H α β * (star (F α) ⬝ᵥ G⁻¹ *ᵥ F β) :=
      e.sum_comp (fun β : ι => H α β * (star (F α) ⬝ᵥ G⁻¹ *ᵥ F β))
    simp only [Matrix.submatrix_apply]
    simp_rw [hs]
    exact e.sum_comp (fun α : ι => ∑ β, H α β * (star (F α) ⬝ᵥ G⁻¹ *ᵥ F β))
  rw [hleft, hright] at he
  exact he

theorem fiberPairing_eq_kronecker {n r : ℕ}
    (G : Matrix (Fin n) (Fin n) ℂ) (H : Matrix (Fin r) (Fin r) ℂ)
    (C : Fin r → Fin n → ℂ) :
    (∑ α, ∑ β, H α β * (star (C α) ⬝ᵥ G *ᵥ C β)) =
      star (fun p : Fin r × Fin n => C p.1 p.2) ⬝ᵥ (H ⊗ₖ G) *ᵥ
        (fun p : Fin r × Fin n => C p.1 p.2) := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Matrix.kronecker_apply,
    Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro β _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem twoCoefficientNormSq_eq_fiber_sum {n r : ℕ}
    (G : Matrix (Fin n) (Fin n) ℂ) (H : Matrix (Fin r) (Fin r) ℂ)
    (F : Fin r → Fin n → Fin n → ℂ) :
    (∑ p : Fin r × Fin n, ∑ q : Fin r × Fin n,
      (H ⊗ₖ G⁻¹) p q *
        (star (fun i => F p.1 i p.2) ⬝ᵥ G⁻¹ *ᵥ (fun k => F q.1 k q.2))).re =
      2 * twoCoefficientNormSq G H F := by
  have he : (∑ p : Fin r × Fin n, ∑ q : Fin r × Fin n,
      (H ⊗ₖ G⁻¹) p q *
        (star (fun i => F p.1 i p.2) ⬝ᵥ G⁻¹ *ᵥ (fun k => F q.1 k q.2))) =
      ∑ α, ∑ β, ∑ i, ∑ j, ∑ k, ∑ l,
        H α β * G⁻¹ i k * G⁻¹ j l * star (F α i j) * F β k l := by
    simp only [Fintype.sum_prod_type, Matrix.kronecker_apply, dotProduct, Matrix.mulVec,
      Pi.star_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro α _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro β _
    conv_lhs => arg 2; intro j; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [he]
  unfold twoCoefficientNormSq
  have hhalf (c : ℂ) : ((1 / 2 : ℂ) * c).re = (1 / 2 : ℝ) * c.re := by
    simp only [Complex.mul_re]; norm_num
  rw [hhalf]
  ring

theorem two_contraction_bound {n r : ℕ}
    (G : Matrix (Fin n) (Fin n) ℂ) (H : Matrix (Fin r) (Fin r) ℂ)
    (hG : G.PosDef) (hH : H.PosDef) (a : Fin n → ℂ)
    (F : Fin r → Fin n → Fin n → ℂ) :
    (∑ α, ∑ β, H α β *
      (star (fun j => star a ⬝ᵥ G⁻¹ *ᵥ (fun k => F α k j)) ⬝ᵥ G⁻¹ *ᵥ
        (fun l => star a ⬝ᵥ G⁻¹ *ᵥ (fun k => F β k l)))).re ≤
      2 * (star a ⬝ᵥ G⁻¹ *ᵥ a).re * twoCoefficientNormSq G H F := by
  have he := scalar_contraction_bound_fintype G (H ⊗ₖ G⁻¹) hG (hH.kronecker hG.inv)
    a (fun p i => F p.1 i p.2)
  rw [twoCoefficientNormSq_eq_fiber_sum] at he
  rw [fiberPairing_eq_kronecker]
  convert he using 1
  ring

set_option backward.isDefEq.respectTransparency false in
theorem chartTwoGradientContraction_normSq_bound (g : HermitianField M) (h : Metric E)
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ) (W : NQForm E 2)
    (a : M.Carrier) (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) :
    chartOneCoefficientNormSq (r := r) E g h (twoGradientContraction E g χ W) a z ≤
      2 * (star (fun i => wirtBar (fun w => Complex.ofReal (inChart a χ w)) z (stdVec i)) ⬝ᵥ
        (hMat g a z)⁻¹ *ᵥ
          (fun i => wirtBar (fun w => Complex.ofReal (inChart a χ w)) z (stdVec i))).re *
            chartTwoCoefficientNormSq (r := r) E g h W a z := by
  let v := fun i => wirtBar (fun w => Complex.ofReal (inChart a χ w)) z (stdVec i)
  let F := fun α i j => coefficients (r := r) E W a z ![i,j] α
  have hc (α : Fin r) :
      (fun j => coefficients (r := r) E (twoGradientContraction E g χ W) a z (fun _ => j) α) =
      fun j => star v ⬝ᵥ (hMat g a z)⁻¹ *ᵥ (fun k => F α k j) := by
    funext j
    rw [coefficients_twoGradientContraction_apply E g χ hχ W a z hz j α]
    simp only [v, F, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc]
  rw [chartOneCoefficientNormSq_eq_fiber_sum, chartTwoCoefficientNormSq_eq]
  simp_rw [hc]
  exact two_contraction_bound _ _ (hMat_posDef g a z hz.1)
    (metricMatrix_posDef E h a z hz) v F

/-- The pointwise contraction bound for an arbitrary actual degree-two form. -/
theorem twoGradientContraction_normSq_le (g : HermitianField M) (h : Metric E)
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ) (W : NQForm E 2) (x : M.Carrier) :
    BundleDbar.formNormSq (r := r) E g h (twoGradientContraction E g χ W) x ≤
      2 * gradNormSq g χ x * BundleDbar.formNormSq (r := r) E g h W x := by
  have hxx : chartInv x (chartPt x x) = x :=
    chartInv_chartPt_of_mem x x (mem_chart_source _ _)
  have hz : chartPt x x ∈ localDomain (r := r) E x := by
    refine ⟨mem_extChartAt_target x, ?_⟩
    change chartInv x (chartPt x x) ∈ (localTriv (r := r) E x).baseSet
    rw [hxx]
    exact FiberBundle.mem_baseSet_trivializationAt' x
  have hu := formNormSq_one_chart_factor E g h (twoGradientContraction E g χ W)
    x (chartPt x x) hz
  have hw := formNormSq_two_chart_factor_matrix E g h W x (chartPt x x) hz
  rw [hxx] at hu hw
  rw [hu, hw, gradNormSq_eq_chart_bar_norm]
  have he := mul_le_mul_of_nonneg_left
    (chartTwoGradientContraction_normSq_bound E g h χ hχ W x (chartPt x x) hz)
    (inv_nonneg.mpr (L18Aux.hMat_det_re_pos g x hz.1).le)
  simpa only [mul_assoc, mul_left_comm] using he

end Yau.LeafProofs.L14Aux
