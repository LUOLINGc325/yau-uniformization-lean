import Yau.LeafProofs.L21WeightedDomainsMeaning
import Yau.LeafProofs.L21WeakLinear

open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem weightedDomains_integrable_compact_product {f : X n → ℂ}
    (hf : ContinuousOn f (Metric.ball 0 1)) (ψ : CompactTest (Metric.ball (0 : X n) 1)) :
    Integrable (fun x => ψ x*f x) (Yau.lebesgueC n) :=
  Yau.LeafProofs.L14Aux.integrable_compactTest_mul_complex Metric.isOpen_ball
    ψ.property.1.continuous ψ.property.2.1 ψ.property.2.2 hf

theorem weightedRowTranspose_eq_rowTranspose {α β ι : Type*} [Fintype α] [Fintype ι]
    (v : ι → X n) (a : β → α → ι → X n → ℂ) (b : β → α → X n → ℂ)
    (r : β) (c : α) (ψ : X n → ℂ) (x : X n) :
    weightedRowTranspose v a b r c ψ x = rowTranspose v (a r c) ψ x+b r c x*ψ x := by
  simp only [weightedRowTranspose,rowTranspose,rowApply,rowDivergence,
    Finset.sum_add_distrib,Finset.sum_mul]
  ring

/-- Smooth local inputs satisfy the exact complex compact-test equation
of one original row, including its locally smooth zeroth-order part. -/
theorem weightedDomains_smooth_single_row_pairing {α β ι : Type*} [Fintype α] [Fintype ι]
    (v : ι → X n) (a : β → α → ι → X n → ℂ) (b : β → α → X n → ℂ)
    (ha : ∀ r c i, ContDiffOn ℝ ∞ (a r c i) (Metric.ball 0 1))
    (hb : ∀ r c, ContDiffOn ℝ ∞ (b r c) (Metric.ball 0 1))
    (r : β) (c : α) {u : X n → ℂ} (hu : ContDiffOn ℝ ∞ u (Metric.ball 0 1))
    (ψ : CompactTest (Metric.ball (0 : X n) 1)) :
    (∫ x, ψ x*((∑ i, a r c i x*fderiv ℝ u x (v i))+b r c x*u x) ∂Yau.lebesgueC n) =
      ∫ x, u x*weightedRowTranspose v a b r c ψ x ∂Yau.lebesgueC n := by
  have hDu (i : ι) : ContDiffOn ℝ ∞ (fun x => fderiv ℝ u x (v i)) (Metric.ball 0 1) :=
    (hu.fderiv_of_isOpen Metric.isOpen_ball (by simp)).clm_apply contDiffOn_const
  have huL2 := locallyL2On_of_continuousOn hu.continuousOn
  have hDuL2 (i : ι) := locallyL2On_of_continuousOn (hDu i).continuousOn
  have hPair := weak_gradient_row_transpose_pairing Metric.isOpen_ball v (a r c) (ha r c)
    u (fun x i => fderiv ℝ u x (v i)) huL2 hDuL2
    (fun i => complexWeakDerivativeOn_smooth Metric.isOpen_ball hu (v i)) ψ
  have hMain := weightedDomains_integrable_compact_product
    (ContDiffOn.sum (s := Finset.univ) (fun i _ => (ha r c i).mul (hDu i))).continuousOn ψ
  have hZero := weightedDomains_integrable_compact_product ((hb r c).mul hu).continuousOn ψ
  have hTrans := locallyL2On_test_integrable Metric.isOpen_ball huL2
    (rowTransposeTest Metric.isOpen_ball v (a r c) (ha r c) ψ)
  have hZeroR := locallyL2On_test_integrable Metric.isOpen_ball huL2
    (multiplyLocalTest Metric.isOpen_ball (hb r c) ψ)
  calc
    _ = (∫ x, ψ x*(∑ i, a r c i x*fderiv ℝ u x (v i)) ∂Yau.lebesgueC n)+
        ∫ x, ψ x*(b r c x*u x) ∂Yau.lebesgueC n := by
      simp only [mul_add]
      exact integral_add hMain hZero
    _ = (∫ x, u x*rowTranspose v (a r c) ψ x ∂Yau.lebesgueC n)+
        ∫ x, u x*(b r c x*ψ x) ∂Yau.lebesgueC n := by
      rw [← hPair]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = ∫ x, u x*rowTranspose v (a r c) ψ x+u x*(b r c x*ψ x) ∂Yau.lebesgueC n :=
      (integral_add hTrans hZeroR).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [weightedRowTranspose_eq_rowTranspose]
      ring


/-- The full finite complex system has its literal compact distribution
pairing, for every locally smooth input. -/
theorem weightedDomains_smooth_rows_pairing {α β ι : Type*} [Fintype α] [Fintype ι]
    (v : ι → X n) (a : β → α → ι → X n → ℂ) (b : β → α → X n → ℂ)
    (ha : ∀ r c i, ContDiffOn ℝ ∞ (a r c i) (Metric.ball 0 1))
    (hb : ∀ r c, ContDiffOn ℝ ∞ (b r c) (Metric.ball 0 1))
    (u : X n → α → ℂ) (hu : ∀ c, ContDiffOn ℝ ∞ (fun x => u x c) (Metric.ball 0 1))
    (r : β) (ψ : CompactTest (Metric.ball (0 : X n) 1)) :
    (∫ x, ψ x*Yau.LeafProofs.L14Aux.complexFirstOrderSystemApply v a b u x r ∂Yau.lebesgueC n) =
      ∫ x, ∑ c, u x c*weightedRowTranspose v a b r c ψ x ∂Yau.lebesgueC n := by
  have hDu (c : α) (i : ι) : ContDiffOn ℝ ∞ (fun x => fderiv ℝ (fun y => u y c) x (v i))
      (Metric.ball 0 1) :=
    ((hu c).fderiv_of_isOpen Metric.isOpen_ball (by simp)).clm_apply contDiffOn_const
  have hIntLeft (c : α) : Integrable (fun x => ψ x*((∑ i, a r c i x*fderiv ℝ (fun y => u y c) x (v i))+
      b r c x*u x c)) (Yau.lebesgueC n) :=
    weightedDomains_integrable_compact_product
      (((ContDiffOn.sum (s := Finset.univ) (fun i _ => (ha r c i).mul (hDu c i))).add
        ((hb r c).mul (hu c))).continuousOn) ψ
  have hIntRight (c : α) : Integrable (fun x => u x c*weightedRowTranspose v a b r c ψ x)
      (Yau.lebesgueC n) :=
    locallyL2On_test_integrable Metric.isOpen_ball (locallyL2On_of_continuousOn (hu c).continuousOn)
      (weightedRowTransposeTest v a b ha hb r c ψ)
  calc
    _ = ∫ x, ∑ c, ψ x*((∑ i, a r c i x*fderiv ℝ (fun y => u y c) x (v i))+b r c x*u x c)
        ∂Yau.lebesgueC n := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [Yau.LeafProofs.L14Aux.complexFirstOrderSystemApply,Finset.mul_sum]
    _ = ∑ c, ∫ x, ψ x*((∑ i, a r c i x*fderiv ℝ (fun y => u y c) x (v i))+b r c x*u x c)
        ∂Yau.lebesgueC n := integral_finsetSum _ (fun c _ => hIntLeft c)
    _ = ∑ c, ∫ x, u x c*weightedRowTranspose v a b r c ψ x ∂Yau.lebesgueC n := by
      apply Finset.sum_congr rfl
      intro c hc
      exact weightedDomains_smooth_single_row_pairing v a b ha hb r c (hu c) ψ
    _ = _ := (integral_finsetSum _ (fun c _ => hIntRight c)).symm

/-- Only equality of genuine L² representatives is needed to place a
smooth input and its computed pointwise output in the maximal weak graph. -/
theorem weightedRowsGraph_of_smooth_representatives {α β ι : Type*} [Fintype α] [Fintype ι]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (K : ℝ) (hK : 0 ≤ K) (src : α → E →L[ℂ] WeightedScalar n K)
    (dst : β → F →L[ℂ] WeightedScalar n K)
    (v : ι → X n) (a : β → α → ι → X n → ℂ) (b : β → α → X n → ℂ)
    (ha : ∀ r c i, ContDiffOn ℝ ∞ (a r c i) (Metric.ball 0 1))
    (hb : ∀ r c, ContDiffOn ℝ ∞ (b r c) (Metric.ball 0 1))
    (x : E) (y : F) (u : X n → α → ℂ)
    (hu : ∀ c, ContDiffOn ℝ ∞ (fun z => u z c) (Metric.ball 0 1))
    (hSrc : ∀ c, (fun z => u z c) =ᵐ[weightedBallMeasure n K] (src c x : X n → ℂ))
    (hDst : ∀ r, (fun z => Yau.LeafProofs.L14Aux.complexFirstOrderSystemApply v a b u z r)
      =ᵐ[weightedBallMeasure n K] (dst r y : X n → ℂ)) :
    (x,y) ∈ weightedRowsGraph K hK src dst v a b ha hb := by
  apply (weightedRowsGraph_mem_iff K hK src dst v a b ha hb (x,y)).mpr
  intro r ψ
  have hInt (c : α) : Integrable (fun z => u z c*weightedRowTranspose v a b r c ψ z)
      (Yau.lebesgueC n) :=
    locallyL2On_test_integrable Metric.isOpen_ball (locallyL2On_of_continuousOn (hu c).continuousOn)
      (weightedRowTransposeTest v a b ha hb r c ψ)
  calc
    _ = ∫ z, ψ z*Yau.LeafProofs.L14Aux.complexFirstOrderSystemApply v a b u z r ∂Yau.lebesgueC n :=
      weightedCompactFunctional_apply_representative K hK ψ _ (hDst r)
    _ = ∫ z, ∑ c, u z c*weightedRowTranspose v a b r c ψ z ∂Yau.lebesgueC n :=
      weightedDomains_smooth_rows_pairing v a b ha hb u hu r ψ
    _ = ∑ c, ∫ z, u z c*weightedRowTranspose v a b r c ψ z ∂Yau.lebesgueC n :=
      integral_finsetSum _ (fun c _ => hInt c)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [weightedCompactFunctional_apply_representative K hK _ _ (hSrc c)]
      apply integral_congr_ae
      filter_upwards [] with z
      exact mul_comm _ _

end Yau.LeafProofs.L21Aux
