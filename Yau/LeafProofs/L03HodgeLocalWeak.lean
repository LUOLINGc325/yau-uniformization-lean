import Yau.LeafProofs.L03HodgeLocalizedData

open MeasureTheory Filter Module
open scoped Topology ContDiff

noncomputable section

namespace Yau.LeafProofs.L03.HodgeDivergenceWeak

variable {n k : ℕ} {M : ComplexManifold n}

theorem actual_formal_test_eq_testRow {α : Type*} [Fintype α] [DecidableEq α]
    (g : HermitianField M) (x : M.Carrier) (b : Basis α ℝ (Fiber n k))
    (r c : α) (φ : ComplexVector n → ℝ) (z : ComplexVector n) :
    divergenceFormalTest (realModelBasis n) (a g x b) (B g x b) (C g x b) φ z r c =
      testRow g x b r c φ z := by
  simpa only [one_mul, divergenceFormalTest] using
    (divergence_row_identity g x b r c φ z 1).symm

theorem actual_formal_test_contDiffOn {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (x : M.Carrier) (b : Basis α ℝ (Fiber n k))
    (r c : α) (φ : ComplexVector n → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    ContDiffOn ℝ ∞ (fun z => divergenceFormalTest (realModelBasis n)
      (a g.form x b) (B g.form x b) (C g.form x b) φ z r c) (chartTarget x) := by
  have hd (i : RIdx n) : ContDiff ℝ ∞ (fun z => fderiv ℝ φ z (realModelBasis n i)) :=
    (hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hdd (i j : RIdx n) : ContDiff ℝ ∞
      (fun z => fderiv ℝ (fun y => fderiv ℝ φ y (realModelBasis n i)) z (realModelBasis n j)) :=
    ((hd i).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hda (i j : RIdx n) : ContDiffOn ℝ ∞
      (fun z => fderiv ℝ (a g.form x b r c i j) z (realModelBasis n j)) (chartTarget x) :=
    ((a_contDiffOn g x b r c i j).fderiv_of_isOpen
      (isOpen_extChartAt_target (I := ComplexModel n) x) (by simp)).clm_apply contDiffOn_const
  exact (((ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ =>
    ((a_contDiffOn g x b r c i j).mul (hdd i j).contDiffOn).add ((hda i j).mul (hd i).contDiffOn)))).neg).sub
    (ContDiffOn.sum (fun i _ => (B_contDiffOn g x b r c i).mul (hd i).contDiffOn))).add
    ((C_contDiffOn g x b r c).mul hφ.contDiffOn)

theorem chart_coord_cutoff_product_integrable {α : Type*} [Fintype α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A : RealForm M k) (hA : L2RealForm g.form μ A) (x : M.Carrier)
    (b : Basis α ℝ (Fiber n k)) (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (hχO : tsupport χ ⊆ chartTarget x)
    (f : ComplexVector n → ℝ) (hf : ContDiffOn ℝ ∞ f (chartTarget x)) (c : α) :
    Integrable (fun z => (χ z * f z) * b.repr (chartForm A x z) c) (lebesgueC n) := by
  have hp := scalar_cutoff_contDiff_properties
    (isOpen_extChartAt_target (I := ComplexModel n) x) χ hχ hcχ hχO f hf
  exact chart_cutoff_coord_integrable g μ hμ A hA x b _ hp.1 hp.2.1 (hp.2.2.trans hχO) c

theorem compact_scalar_mul_integrable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    (ν : Measure E) (φ : E → ℝ) (hφ : Continuous φ) (hcφ : HasCompactSupport φ)
    (f : E → ℝ) (hf : Integrable f ν) : Integrable (fun z => φ z * f z) ν := by
  obtain ⟨D, hD⟩ := hcφ.exists_bound_of_continuous hφ
  exact (hf.bdd_smul D hφ.aestronglyMeasurable (Filter.Eventually.of_forall hD)).congr
    (Filter.Eventually.of_forall fun _ => rfl)

/-- Multiplying an original rough Hodge deficiency field by an actual
compact chart cutoff gives a global divergence equation with explicit
compact ordinary L² value/flux data. No raw derivative is used. -/
theorem maximalGraph_localized_divergenceWeak {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A : RealForm M k) (hmax : OperatorCandidates.HodgeMaximalGraph g.form μ A (-A))
    (x : M.Carrier) (b : Basis α ℝ (Fiber n k))
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ chartTarget x) :
    divergenceSystemWeakEquation (lebesgueC n) (realModelBasis n)
      (a g.form x b) (B g.form x b) (C g.form x b)
      (localizedInput x b χ A) (localizedValue g.form x b χ A) (localizedFlux g.form x b χ A) := by
  classical
  letI : IsLocallyFiniteMeasure (lebesgueC n) := by rw [lebesgueC_eq_volume]; infer_instance
  intro r φ hφ hcφ
  let u := fun z c => b.repr (chartForm A x z) c
  let L := fun z => ∑ c, divergenceFormalTest (realModelBasis n) (a g.form x b)
    (B g.form x b) (C g.form x b) φ z r c * localizedInput x b χ A z c
  let O := fun z => ∑ c, divergenceFormalTest (realModelBasis n) (a g.form x b)
    (B g.form x b) (C g.form x b) (fun y => χ y * φ y) z r c * u z c
  let V := fun z => localizedValue g.form x b χ A z r * φ z
  let Q := fun i z => localizedFlux g.form x b χ A z r i * fderiv ℝ φ z (realModelBasis n i)
  have hd (i : RIdx n) : ContDiff ℝ ∞ (fun z => fderiv ℝ φ z (realModelBasis n i)) :=
    (hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hdd (i j : RIdx n) : ContDiff ℝ ∞
      (fun z => fderiv ℝ (fun y => fderiv ℝ φ y (realModelBasis n i)) z (realModelBasis n j)) :=
    ((hd i).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hda (c : α) (i j : RIdx n) : ContDiffOn ℝ ∞
      (fun z => fderiv ℝ (a g.form x b r c i j) z (realModelBasis n j)) (chartTarget x) :=
    ((a_contDiffOn g x b r c i j).fderiv_of_isOpen
      (isOpen_extChartAt_target (I := ComplexModel n) x) (by simp)).clm_apply contDiffOn_const
  have hp (c : α) (i j : RIdx n) : Integrable (fun z =>
      (a g.form x b r c i j z * fderiv ℝ (fun y => fderiv ℝ φ y (realModelBasis n i)) z (realModelBasis n j) +
        fderiv ℝ (a g.form x b r c i j) z (realModelBasis n j) * fderiv ℝ φ z (realModelBasis n i)) *
          localizedInput x b χ A z c) (lebesgueC n) := by
    have hh := chart_coord_cutoff_product_integrable g μ hμ A hmax.1 x b χ hχ hcχ hχO _
      (((a_contDiffOn g x b r c i j).mul (hdd i j).contDiffOn).add ((hda c i j).mul (hd i).contDiffOn)) c
    apply hh.congr
    exact Filter.Eventually.of_forall fun z => by dsimp only [localizedInput]; ring
  have hb (c : α) (i : RIdx n) : Integrable (fun z =>
      (B g.form x b r c i z * fderiv ℝ φ z (realModelBasis n i)) * localizedInput x b χ A z c) (lebesgueC n) := by
    have hh := chart_coord_cutoff_product_integrable g μ hμ A hmax.1 x b χ hχ hcχ hχO _
      ((B_contDiffOn g x b r c i).mul (hd i).contDiffOn) c
    apply hh.congr
    exact Filter.Eventually.of_forall fun z => by dsimp only [localizedInput]; ring
  have hc (c : α) : Integrable (fun z => φ z *
      (C g.form x b r c z * localizedInput x b χ A z c)) (lebesgueC n) := by
    have hh := chart_coord_cutoff_product_integrable g μ hμ A hmax.1 x b χ hχ hcχ hχO _
      (hφ.contDiffOn.mul (C_contDiffOn g x b r c)) c
    apply hh.congr
    exact Filter.Eventually.of_forall fun z => by dsimp only [localizedInput]; ring
  have hLrow (c : α) : Integrable (fun z => divergenceFormalTest (realModelBasis n) (a g.form x b)
      (B g.form x b) (C g.form x b) φ z r c * localizedInput x b χ A z c) (lebesgueC n) := by
    have hh := chart_coord_cutoff_product_integrable g μ hμ A hmax.1 x b χ hχ hcχ hχO _
      (actual_formal_test_contDiffOn g x b r c φ hφ) c
    apply hh.congr
    exact Filter.Eventually.of_forall fun z => by dsimp only [localizedInput]; ring
  have hL : Integrable L (lebesgueC n) := integrable_finsetSum Finset.univ (fun c _ => hLrow c)
  have hm := localized_data_memLp g μ hμ A hmax.1 x b χ hχ hcχ hχO
  have hs := localized_data_support g.form x b χ A
  have hVi : Integrable (fun z => localizedValue g.form x b χ A z r) (lebesgueC n) :=
    memLp_two_compact_integrable (lebesgueC n) _ (hm.2.1 r)
      (hcχ.of_isClosed_subset (isClosed_tsupport _) (hs.2.1 r))
  have hQi (i : RIdx n) : Integrable (fun z => localizedFlux g.form x b χ A z r i) (lebesgueC n) :=
    memLp_two_compact_integrable (lebesgueC n) _ (hm.2.2 r i)
      (hcχ.of_isClosed_subset (isClosed_tsupport _) (hs.2.2 r i))
  have hV : Integrable V (lebesgueC n) := by
    simpa only [V, mul_comm] using compact_scalar_mul_integrable (lebesgueC n) φ hφ.continuous hcφ _ hVi
  have hQ (i : RIdx n) : Integrable (Q i) (lebesgueC n) := by
    simpa only [Q, mul_comm] using compact_scalar_mul_integrable (lebesgueC n) _ (hd i).continuous
      (hcφ.fderiv_apply ℝ (realModelBasis n i)) _ (hQi i)
  have hQsum : Integrable (fun z => ∑ i, Q i z) (lebesgueC n) :=
    integrable_finsetSum Finset.univ (fun i _ => hQ i)
  have hid (z : ComplexVector n) : L z = O z + V z - ∑ i, Q i z :=
    divergenceFormalTest_mul_sum (realModelBasis n) (a g.form x b) (B g.form x b) (C g.form x b)
      u χ φ hχ hφ z r
  have hO : Integrable O (lebesgueC n) := by
    apply ((hL.sub hV).add hQsum).congr
    exact Filter.Eventually.of_forall fun z => by
      change L z - V z + ∑ i, Q i z = O z
      rw [hid]
      ring
  have hzero := maximalGraph_chart_scalar_test g μ hμ A hmax x b r (fun z => χ z * φ z)
    (hχ.mul hφ) hcχ.mul_right (tsupport_mul_subset_left.trans hχO)
  have hOeq : O = (fun z => ∑ c, b.repr (chartForm A x z) c * testRow g.form x b r c (fun y => χ y * φ y) z) := by
    funext z
    apply Finset.sum_congr rfl
    intro c _
    rw [actual_formal_test_eq_testRow]
    exact mul_comm _ _
  rw [← hOeq] at hzero
  have hcombined : (∫ z, L z ∂lebesgueC n) =
      (∫ z, V z ∂lebesgueC n) - ∑ i, ∫ z, Q i z ∂lebesgueC n := by
    have hlin := integral_sub (hO.add hV) hQsum
    have hadd := integral_add hO hV
    simp only [Pi.add_apply, Pi.sub_apply] at hlin hadd
    calc
      _ = ∫ z, O z + V z - ∑ i, Q i z ∂lebesgueC n := integral_congr_ae (Filter.Eventually.of_forall hid)
      _ = _ := by rw [hlin, hadd, hzero, zero_add, integral_finsetSum Finset.univ (fun i _ => hQ i)]
  rw [← integral_divergenceFormalTest (lebesgueC n) (realModelBasis n) (a g.form x b) (B g.form x b)
    (C g.form x b) (localizedInput x b χ A) φ r hp hb hc]
  simpa only [L, V, Q, mul_comm] using hcombined

end Yau.LeafProofs.L03.HodgeDivergenceWeak
