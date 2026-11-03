import Yau.LeafProofs.L22RegularizedMaxKernel

noncomputable section

open scoped Topology ContDiff Convolution
open MeasureTheory Set

namespace Yau.LeafProofs.L22Aux

/-- The maximum on a finite coordinate space, with value zero on the empty
coordinate space. -/
def finiteMaximum {κ : Type*} [Fintype κ] (v : κ → ℝ) : ℝ := by
  classical
  exact if h : Nonempty κ then Finset.univ.sup' (Finset.univ_nonempty) v else 0

theorem finiteMaximum_eq {κ : Type*} [Fintype κ] [Nonempty κ] (v : κ → ℝ) :
    finiteMaximum v = Finset.univ.sup' Finset.univ_nonempty v := by
  classical
  simp only [finiteMaximum, dif_pos (inferInstance : Nonempty κ)]

theorem le_finiteMaximum {κ : Type*} [Fintype κ] (v : κ → ℝ) (i : κ) :
    v i ≤ finiteMaximum v := by
  classical
  letI : Nonempty κ := ⟨i⟩
  rw [finiteMaximum_eq]
  exact Finset.le_sup' _ (Finset.mem_univ i)

theorem finiteMaximum_le {κ : Type*} [Fintype κ] [Nonempty κ]
    (v : κ → ℝ) {B : ℝ} (h : ∀ i, v i ≤ B) : finiteMaximum v ≤ B := by
  classical
  rw [finiteMaximum_eq]
  exact Finset.sup'_le _ _ (fun i _ => h i)

theorem finiteMaximum_continuous {κ : Type*} [Fintype κ] :
    Continuous (finiteMaximum : (κ → ℝ) → ℝ) := by
  classical
  change Continuous (fun v : κ → ℝ => finiteMaximum v)
  by_cases h : Nonempty κ
  · letI := h
    simp only [finiteMaximum_eq]
    exact Continuous.finset_sup'_apply _ (fun i _ => continuous_apply i)
  · simp only [finiteMaximum, dif_neg h]
    exact continuous_const

theorem finiteMaximum_monotone {κ : Type*} [Fintype κ] :
    Monotone (finiteMaximum : (κ → ℝ) → ℝ) := by
  classical
  intro u v huv
  by_cases h : Nonempty κ
  · letI := h
    exact finiteMaximum_le _ (fun i => (huv i).trans (le_finiteMaximum v i))
  · simp only [finiteMaximum, dif_neg h, le_refl]

theorem finiteMaximum_add_const {κ : Type*} [Fintype κ] [Nonempty κ]
    (v : κ → ℝ) (c : ℝ) : finiteMaximum (fun i => v i + c) = finiteMaximum v + c := by
  apply le_antisymm
  · exact finiteMaximum_le _ (fun i => add_le_add (le_finiteMaximum v i) le_rfl)
  · have h := finiteMaximum_le v (B := finiteMaximum (fun i => v i + c) - c)
      (fun i => by linarith [le_finiteMaximum (fun i => v i + c) i])
    linarith

theorem finiteMaximum_convex {κ : Type*} [Fintype κ] :
    ConvexOn ℝ univ (finiteMaximum : (κ → ℝ) → ℝ) := by
  classical
  refine ⟨convex_univ, ?_⟩
  intro u _ v _ a b ha hb hab
  by_cases h : Nonempty κ
  · letI := h
    apply finiteMaximum_le
    intro i
    exact add_le_add (mul_le_mul_of_nonneg_left (le_finiteMaximum u i) ha)
      (mul_le_mul_of_nonneg_left (le_finiteMaximum v i) hb)
  · simp only [finiteMaximum, dif_neg h, smul_zero, add_zero, le_refl]

theorem regularizedMaxProductKernel_integrable_mul {κ : Type*} [Fintype κ]
    (δ : κ → ℝ) {f : (κ → ℝ) → ℝ} (hf : Continuous f) :
    Integrable (fun x => f x * regularizedMaxProductKernel δ x) :=
  (hf.mul (regularizedMaxProductKernel_smooth δ).continuous).integrable_of_hasCompactSupport
    (regularizedMaxProductKernel_compact δ).mul_left

theorem regularizedMaxProductKernel_firstMoment {κ : Type*} [Fintype κ]
    (δ : κ → ℝ) (i : κ) : (∫ x, x i * regularizedMaxProductKernel δ x) = 0 := by
  classical
  have heven (x : κ → ℝ) : regularizedMaxProductKernel δ (-x) =
      regularizedMaxProductKernel δ x := regularizedMaxProductKernel_even δ x
  have heq := integral_neg_eq_self
    (fun x : κ → ℝ => x i * regularizedMaxProductKernel δ x) volume
  simp only [Pi.neg_apply, heven, neg_mul, integral_neg] at heq
  linarith

/-- The genuine finite product convolution used for Richberg gluing. -/
def regularizedMaxCoords {κ : Type*} [Fintype κ] (δ z : κ → ℝ) : ℝ :=
  ∫ x, finiteMaximum (z + x) * regularizedMaxProductKernel δ x

theorem regularizedMaxCoords_integrable {κ : Type*} [Fintype κ]
    (δ z : κ → ℝ) :
    Integrable (fun x => finiteMaximum (z + x) * regularizedMaxProductKernel δ x) :=
  regularizedMaxProductKernel_integrable_mul δ
    (finiteMaximum_continuous.comp (continuous_const.add continuous_id))

theorem regularizedMaxCoords_eq_convolution {κ : Type*} [Fintype κ] (δ : κ → ℝ) :
    regularizedMaxCoords δ =
      regularizedMaxProductKernel δ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] finiteMaximum := by
  funext z
  rw [regularizedMaxCoords, ← integral_neg_eq_self
    (fun x : κ → ℝ => finiteMaximum (z + x) * regularizedMaxProductKernel δ x) volume]
  simp only [regularizedMaxProductKernel_even, ← sub_eq_add_neg, convolution_lsmul,
    smul_eq_mul, mul_comm]

theorem regularizedMaxCoords_smooth {κ : Type*} [Fintype κ] (δ : κ → ℝ) :
    ContDiff ℝ ∞ (regularizedMaxCoords δ) := by
  rw [regularizedMaxCoords_eq_convolution]
  exact (regularizedMaxProductKernel_compact δ).contDiff_convolution_left _
    (regularizedMaxProductKernel_smooth δ) finiteMaximum_continuous.locallyIntegrable

theorem regularizedMaxCoords_monotone {κ : Type*} [Fintype κ] (δ : κ → ℝ) :
    Monotone (regularizedMaxCoords δ) := by
  intro u v huv
  apply integral_mono (regularizedMaxCoords_integrable δ u)
    (regularizedMaxCoords_integrable δ v)
  intro x
  exact mul_le_mul_of_nonneg_right
    (finiteMaximum_monotone (fun i => add_le_add (huv i) le_rfl))
    (regularizedMaxProductKernel_nonneg δ x)

theorem regularizedMaxCoords_add_const {κ : Type*} [Fintype κ] [Nonempty κ]
    (δ z : κ → ℝ) (c : ℝ) :
    regularizedMaxCoords δ (fun i => z i + c) = regularizedMaxCoords δ z + c := by
  have h (x : κ → ℝ) : finiteMaximum ((fun i => z i + c) + x) =
      finiteMaximum (z + x) + c := by
    convert finiteMaximum_add_const (z + x) c using 1
    congr 1
    ext i
    simp only [Pi.add_apply]
    ring
  simp only [regularizedMaxCoords, h, add_mul]
  rw [integral_add (regularizedMaxCoords_integrable δ z)
    ((regularizedMaxProductKernel_integrable δ).const_mul c), integral_const_mul,
    regularizedMaxProductKernel_mass, mul_one]

theorem regularizedMaxCoords_ge {κ : Type*} [Fintype κ]
    (δ z : κ → ℝ) (i : κ) : z i ≤ regularizedMaxCoords δ z := by
  have hi : Integrable (fun x : κ → ℝ => (z i + x i) * regularizedMaxProductKernel δ x) :=
    regularizedMaxProductKernel_integrable_mul δ (continuous_const.add (continuous_apply i))
  have hmean : (∫ x : κ → ℝ, (z i + x i) * regularizedMaxProductKernel δ x) = z i := by
    simp only [add_mul]
    rw [integral_add ((regularizedMaxProductKernel_integrable δ).const_mul _)
      (regularizedMaxProductKernel_integrable_mul δ (continuous_apply i)),
      integral_const_mul, regularizedMaxProductKernel_mass,
      regularizedMaxProductKernel_firstMoment, mul_one, add_zero]
  rw [← hmean]
  apply integral_mono hi (regularizedMaxCoords_integrable δ z)
  intro x
  exact mul_le_mul_of_nonneg_right (le_finiteMaximum (z + x) i)
    (regularizedMaxProductKernel_nonneg δ x)

theorem regularizedMaxCoords_convex {κ : Type*} [Fintype κ] (δ : κ → ℝ) :
    ConvexOn ℝ univ (regularizedMaxCoords δ) := by
  refine ⟨convex_univ, ?_⟩
  intro u _ v _ a b ha hb hab
  have hpoint (x : κ → ℝ) : finiteMaximum (a • u + b • v + x) ≤
      a * finiteMaximum (u + x) + b * finiteMaximum (v + x) := by
    have h := finiteMaximum_convex.2 (mem_univ (u + x)) (mem_univ (v + x)) ha hb hab
    convert h using 1
    congr 1
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc
      a * u i + b * v i + x i = a * u i + b * v i + (a + b) * x i := by rw [hab, one_mul]
      _ = a * (u i + x i) + b * (v i + x i) := by ring
  have hi := ((regularizedMaxCoords_integrable δ u).const_mul a).add
    ((regularizedMaxCoords_integrable δ v).const_mul b)
  change (∫ x, finiteMaximum (a • u + b • v + x) * regularizedMaxProductKernel δ x) ≤
    a * (∫ x, finiteMaximum (u + x) * regularizedMaxProductKernel δ x) +
    b * (∫ x, finiteMaximum (v + x) * regularizedMaxProductKernel δ x)
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add
    ((regularizedMaxCoords_integrable δ u).const_mul a)
    ((regularizedMaxCoords_integrable δ v).const_mul b)]
  apply integral_mono (regularizedMaxCoords_integrable δ (a • u + b • v)) hi
  intro x
  simpa only [Pi.add_apply, add_mul, mul_assoc] using
    mul_le_mul_of_nonneg_right (hpoint x) (regularizedMaxProductKernel_nonneg δ x)

theorem regularizedMaxCoords_le {κ : Type*} [Fintype κ] [Nonempty κ]
    (δ z : κ → ℝ) (hδ : ∀ i, 0 < δ i) {B : ℝ}
    (hB : ∀ i, z i + δ i ≤ B) : regularizedMaxCoords δ z ≤ B := by
  have hmass : (∫ x : κ → ℝ, B * regularizedMaxProductKernel δ x) = B := by
    rw [integral_const_mul, regularizedMaxProductKernel_mass, mul_one]
  rw [← hmass]
  apply integral_mono (regularizedMaxCoords_integrable δ z)
    ((regularizedMaxProductKernel_integrable δ).const_mul B)
  intro x
  by_cases hx : regularizedMaxProductKernel δ x = 0
  · simp only [hx, mul_zero, le_refl]
  · apply mul_le_mul_of_nonneg_right _ (regularizedMaxProductKernel_nonneg δ x)
    apply finiteMaximum_le
    intro i
    have hxi : regularizedMaxKernel (δ i) (x i) ≠ 0 := by
      classical
      exact (Finset.prod_ne_zero_iff.mp hx) i (Finset.mem_univ i)
    have hxs := (abs_lt.mp (regularizedMaxKernel_support_of_pos (hδ i) hxi)).2
    change z i + x i ≤ B
    linarith [hB i]

/-- A finite active family in an arbitrary index type. The ambient index type
need not itself be finite. -/
def regularizedMax {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (δ v : ι → ℝ) : ℝ :=
  regularizedMaxCoords (fun i : s => δ i) (fun i : s => v i)

theorem regularizedMax_empty {ι : Type*} [DecidableEq ι] (δ v : ι → ℝ) :
    regularizedMax ∅ δ v = 0 := by
  have h : ¬Nonempty (↥(∅ : Finset ι)) := by simp
  simp only [regularizedMax, regularizedMaxCoords, finiteMaximum, dif_neg h,
    zero_mul, integral_zero]

theorem regularizedMax_smooth {ι : Type*} [DecidableEq ι] (s : Finset ι) (δ : ι → ℝ) :
    ContDiff ℝ ∞ (fun z : s → ℝ =>
      regularizedMax s δ (fun i => if h : i ∈ s then z ⟨i, h⟩ else 0)) := by
  convert regularizedMaxCoords_smooth (fun i : s => δ i) using 1
  funext z
  unfold regularizedMax
  congr 1
  ext i
  simp only [dif_pos i.property]

theorem regularizedMax_monotone {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (δ : ι → ℝ) : Monotone (regularizedMax s δ) := by
  intro u v huv
  exact regularizedMaxCoords_monotone _ (fun i => huv i)

theorem regularizedMax_convex {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (δ : ι → ℝ) : ConvexOn ℝ univ (regularizedMax s δ) := by
  refine ⟨convex_univ, ?_⟩
  intro u _ v _ a b ha hb hab
  exact (regularizedMaxCoords_convex (fun i : s => δ i)).2
    (mem_univ (fun i : s => u i)) (mem_univ (fun i : s => v i)) ha hb hab

theorem regularizedMax_add_const {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty) (δ v : ι → ℝ) (c : ℝ) :
    regularizedMax s δ (fun i => v i + c) = regularizedMax s δ v + c := by
  letI : Nonempty s := hs.to_subtype
  exact regularizedMaxCoords_add_const _ _ _

theorem regularizedMax_ge {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (δ v : ι → ℝ) {i : ι} (hi : i ∈ s) :
    v i ≤ regularizedMax s δ v :=
  regularizedMaxCoords_ge (fun j : s => δ j) (fun j : s => v j) ⟨i, hi⟩

theorem regularizedMax_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty) (δ v : ι → ℝ)
    (hδ : ∀ i ∈ s, 0 < δ i) {B : ℝ} (hB : ∀ i ∈ s, v i + δ i ≤ B) :
    regularizedMax s δ v ≤ B := by
  letI : Nonempty s := hs.to_subtype
  exact regularizedMaxCoords_le (fun i : s => δ i) (fun i : s => v i)
    (fun i => hδ i i.property) (fun i => hB i i.property)

end Yau.LeafProofs.L22Aux
