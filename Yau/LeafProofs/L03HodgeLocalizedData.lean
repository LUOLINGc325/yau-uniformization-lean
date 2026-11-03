import Yau.LeafProofs.L03DivergenceLocalize
import Yau.LeafProofs.L03HodgeDivergenceWeak

open MeasureTheory Filter Module
open scoped Topology ContDiff

noncomputable section

namespace Yau.LeafProofs.L03.HodgeDivergenceWeak

variable {n k : ℕ} {M : ComplexManifold n}

theorem chart_cutoff_actual_coord_memLp {α : Type*} [Fintype α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A : RealForm M k) (hA : L2RealForm g.form μ A) (x : M.Carrier)
    (b : Basis α ℝ (Fiber n k)) (φ : ComplexVector n → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hcφ : HasCompactSupport φ) (hφO : tsupport φ ⊆ chartTarget x) (c : α) :
    MemLp (fun z => φ z * b.repr (chartForm A x z) c) 2 (lebesgueC n) := by
  apply (chart_cutoff_coord_memLp g μ hμ A hA x b φ hφ hcφ hφO c).ae_eq
  exact Filter.Eventually.of_forall fun z => by
    by_cases hz : z ∈ chartTarget x
    · simp only [chartFormPullbackZero, ite_eq_left hz]
    · have hφz : φ z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hφO h))
      simp only [hφz, zero_mul]

theorem localized_value_coefficient_contDiff {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (x : M.Carrier) (b : Basis α ℝ (Fiber n k))
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ chartTarget x) (r c : α) :
    ContDiff ℝ ∞ (fun z => localizedDivergenceValueCoefficient (realModelBasis n)
      (a g.form x b) (B g.form x b) χ z r c) := by
  let Dχ := fun i z => fderiv ℝ χ z (realModelBasis n i)
  have hD (i : RIdx n) : ContDiff ℝ ∞ (Dχ i) :=
    (hχ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hcD (i : RIdx n) : HasCompactSupport (Dχ i) := hcχ.fderiv_apply ℝ (realModelBasis n i)
  have hsD (i : RIdx n) : tsupport (Dχ i) ⊆ chartTarget x :=
    (tsupport_fderiv_apply_subset ℝ (realModelBasis n i)).trans hχO
  have hDa (i j : RIdx n) : ContDiffOn ℝ ∞
      (fun z => fderiv ℝ (a g.form x b r c i j) z (realModelBasis n j)) (chartTarget x) :=
    ((a_contDiffOn g x b r c i j).fderiv_of_isOpen
      (isOpen_extChartAt_target (I := ComplexModel n) x) (by simp)).clm_apply contDiffOn_const
  have h1 (i j : RIdx n) : ContDiff ℝ ∞ (fun z =>
      fderiv ℝ (a g.form x b r c i j) z (realModelBasis n j) * Dχ i z) := by
    simpa only [mul_comm] using (scalar_cutoff_contDiff_properties
      (isOpen_extChartAt_target (I := ComplexModel n) x) (Dχ i) (hD i) (hcD i) (hsD i)
      _ (hDa i j)).1
  have h2 (i j : RIdx n) : ContDiff ℝ ∞ (fun z =>
      a g.form x b r c i j z * fderiv ℝ (Dχ i) z (realModelBasis n j)) := by
    simpa only [mul_comm] using (scalar_cutoff_contDiff_properties
      (isOpen_extChartAt_target (I := ComplexModel n) x)
      (fun z => fderiv ℝ (Dχ i) z (realModelBasis n j))
      (((hD i).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)
      ((hcD i).fderiv_apply ℝ (realModelBasis n j))
      ((tsupport_fderiv_apply_subset ℝ (realModelBasis n j)).trans (hsD i))
      _ (a_contDiffOn g x b r c i j)).1
  have h3 (i : RIdx n) : ContDiff ℝ ∞ (fun z => B g.form x b r c i z * Dχ i z) := by
    simpa only [mul_comm] using (scalar_cutoff_contDiff_properties
      (isOpen_extChartAt_target (I := ComplexModel n) x) (Dχ i) (hD i) (hcD i) (hsD i)
      _ (B_contDiffOn g x b r c i)).1
  exact (ContDiff.sum (fun i _ => ContDiff.sum (fun j _ => (h1 i j).add (h2 i j)))).add
    (ContDiff.sum (fun i _ => h3 i))

theorem localized_flux_coefficient_contDiff {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (x : M.Carrier) (b : Basis α ℝ (Fiber n k))
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ chartTarget x) (r c : α) (l : RIdx n) :
    ContDiff ℝ ∞ (fun z => localizedDivergenceFluxCoefficient (realModelBasis n)
      (a g.form x b) χ z r c l) := by
  have hpart (i j m : RIdx n) : ContDiff ℝ ∞ (fun z =>
      a g.form x b r c i j z * fderiv ℝ χ z (realModelBasis n m)) := by
    simpa only [mul_comm] using (scalar_cutoff_contDiff_properties
      (isOpen_extChartAt_target (I := ComplexModel n) x)
      (fun z => fderiv ℝ χ z (realModelBasis n m))
      ((hχ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)
      (hcχ.fderiv_apply ℝ (realModelBasis n m))
      ((tsupport_fderiv_apply_subset ℝ (realModelBasis n m)).trans hχO)
      _ (a_contDiffOn g x b r c i j)).1
  have hleft : ContDiff ℝ ∞ (fun z => -(∑ j, a g.form x b r c l j z * fderiv ℝ χ z (realModelBasis n j))) :=
    (ContDiff.sum (fun j _ => hpart l j j)).neg
  have hright : ContDiff ℝ ∞ (fun z => ∑ i, fderiv ℝ χ z (realModelBasis n i) * a g.form x b r c i l z) := by
    apply ContDiff.sum
    intro i _
    simpa only [mul_comm] using hpart i l i
  exact hleft.sub hright

theorem localized_value_coefficient_zero_off {α : Type*} [Fintype α] [DecidableEq α]
    (g : HermitianField M) (x : M.Carrier) (b : Basis α ℝ (Fiber n k))
    (χ : ComplexVector n → ℝ) (r c : α) (z : ComplexVector n) (hz : z ∉ tsupport χ) :
    localizedDivergenceValueCoefficient (realModelBasis n) (a g x b) (B g x b) χ z r c = 0 := by
  have hdd (i j : RIdx n) : fderiv ℝ (fun y => fderiv ℝ χ y (realModelBasis n i)) z (realModelBasis n j) = 0 := by
    rw [fderiv_of_notMem_tsupport ℝ (fun h => hz ((tsupport_fderiv_apply_subset ℝ (realModelBasis n i)) h))]
    rfl
  simp only [localizedDivergenceValueCoefficient, fderiv_of_notMem_tsupport ℝ hz,
    zero_apply, hdd, mul_zero, add_zero, Finset.sum_const_zero]

theorem localized_flux_coefficient_zero_off {α : Type*} [Fintype α] [DecidableEq α]
    (g : HermitianField M) (x : M.Carrier) (b : Basis α ℝ (Fiber n k))
    (χ : ComplexVector n → ℝ) (r c : α) (l : RIdx n) (z : ComplexVector n) (hz : z ∉ tsupport χ) :
    localizedDivergenceFluxCoefficient (realModelBasis n) (a g x b) χ z r c l = 0 := by
  simp only [localizedDivergenceFluxCoefficient, fderiv_of_notMem_tsupport ℝ hz,
    zero_apply, mul_zero, zero_mul, Finset.sum_const_zero, neg_zero, sub_zero]

theorem tsupport_subset_cutoff_of_zero_off (χ f : ComplexVector n → ℝ)
    (hf : ∀ z, z ∉ tsupport χ → f z = 0) : tsupport f ⊆ tsupport χ := by
  apply closure_minimal _ (isClosed_tsupport χ)
  intro z hz
  by_contra hχ
  exact hz (hf z hχ)

def localizedInput {α : Type*} [Fintype α] (x : M.Carrier) (b : Basis α ℝ (Fiber n k))
    (χ : ComplexVector n → ℝ) (A : RealForm M k) (z : ComplexVector n) (c : α) : ℝ :=
  χ z * b.repr (chartForm A x z) c

def localizedValue {α : Type*} [Fintype α] [DecidableEq α]
    (g : HermitianField M) (x : M.Carrier) (b : Basis α ℝ (Fiber n k))
    (χ : ComplexVector n → ℝ) (A : RealForm M k) (z : ComplexVector n) (r : α) : ℝ :=
  ∑ c, localizedDivergenceValueCoefficient (realModelBasis n) (a g x b) (B g x b) χ z r c *
    b.repr (chartForm A x z) c

def localizedFlux {α : Type*} [Fintype α] [DecidableEq α]
    (g : HermitianField M) (x : M.Carrier) (b : Basis α ℝ (Fiber n k))
    (χ : ComplexVector n → ℝ) (A : RealForm M k) (z : ComplexVector n) (r : α) (l : RIdx n) : ℝ :=
  ∑ c, localizedDivergenceFluxCoefficient (realModelBasis n) (a g x b) χ z r c l *
    b.repr (chartForm A x z) c

theorem localized_data_memLp {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A : RealForm M k) (hA : L2RealForm g.form μ A) (x : M.Carrier)
    (b : Basis α ℝ (Fiber n k)) (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (hχO : tsupport χ ⊆ chartTarget x) :
    (∀ c, MemLp (fun z => localizedInput x b χ A z c) 2 (lebesgueC n)) ∧
    (∀ r, MemLp (fun z => localizedValue g.form x b χ A z r) 2 (lebesgueC n)) ∧
    (∀ r l, MemLp (fun z => localizedFlux g.form x b χ A z r l) 2 (lebesgueC n)) := by
  classical
  refine ⟨fun c => chart_cutoff_actual_coord_memLp g μ hμ A hA x b χ hχ hcχ hχO c, ?_, ?_⟩
  · intro r
    apply memLp_finsetSum
    intro c _
    let f := fun z => localizedDivergenceValueCoefficient (realModelBasis n) (a g.form x b) (B g.form x b) χ z r c
    have hs : tsupport f ⊆ tsupport χ := tsupport_subset_cutoff_of_zero_off χ f
      (localized_value_coefficient_zero_off g.form x b χ r c)
    exact chart_cutoff_actual_coord_memLp g μ hμ A hA x b f
      (localized_value_coefficient_contDiff g x b χ hχ hcχ hχO r c)
      (hcχ.of_isClosed_subset (isClosed_tsupport f) hs) (hs.trans hχO) c
  · intro r l
    apply memLp_finsetSum
    intro c _
    let f := fun z => localizedDivergenceFluxCoefficient (realModelBasis n) (a g.form x b) χ z r c l
    have hs : tsupport f ⊆ tsupport χ := tsupport_subset_cutoff_of_zero_off χ f
      (localized_flux_coefficient_zero_off g.form x b χ r c l)
    exact chart_cutoff_actual_coord_memLp g μ hμ A hA x b f
      (localized_flux_coefficient_contDiff g x b χ hχ hcχ hχO r c l)
      (hcχ.of_isClosed_subset (isClosed_tsupport f) hs) (hs.trans hχO) c

theorem localized_data_support {α : Type*} [Fintype α] [DecidableEq α]
    (g : HermitianField M) (x : M.Carrier) (b : Basis α ℝ (Fiber n k))
    (χ : ComplexVector n → ℝ) (A : RealForm M k) :
    (∀ c, tsupport (fun z => localizedInput x b χ A z c) ⊆ tsupport χ) ∧
    (∀ r, tsupport (fun z => localizedValue g x b χ A z r) ⊆ tsupport χ) ∧
    (∀ r l, tsupport (fun z => localizedFlux g x b χ A z r l) ⊆ tsupport χ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro c
    apply tsupport_subset_cutoff_of_zero_off
    intro z hz
    simp only [localizedInput, image_eq_zero_of_notMem_tsupport hz, zero_mul]
  · intro r
    apply tsupport_subset_cutoff_of_zero_off
    intro z hz
    simp only [localizedValue, localized_value_coefficient_zero_off g x b χ r _ z hz,
      zero_mul, Finset.sum_const_zero]
  · intro r l
    apply tsupport_subset_cutoff_of_zero_off
    intro z hz
    simp only [localizedFlux, localized_flux_coefficient_zero_off g x b χ r _ l z hz,
      zero_mul, Finset.sum_const_zero]

end Yau.LeafProofs.L03.HodgeDivergenceWeak
