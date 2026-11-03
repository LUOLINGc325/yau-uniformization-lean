import Yau.LeafProofs.L16OneDimensionalSobolev
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-!
# Mixed Sobolev evaluation on finite real coordinate spaces

Every derivative below is an actual Fréchet derivative, evaluated on a coordinate
basis vector. All integrals use Lebesgue volume on the finite product.
-/

namespace Yau.LeafProofs.L16Aux

open MeasureTheory Set
open scoped BigOperators ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Iterated coordinate derivatives; the first letter acts outermost. -/
noncomputable def coordinateWordDerivative {m : ℕ} (f : (Fin m → ℝ) → ℝ) :
    List (Fin m) → (Fin m → ℝ) → ℝ
  | [] => f
  | i :: w => fun x ↦ fderiv ℝ (coordinateWordDerivative f w) x (Pi.single i 1)

/-- The mixed derivative indexed by a subset, in increasing coordinate order. -/
noncomputable def mixedDerivative {m : ℕ} (f : (Fin m → ℝ) → ℝ)
    (s : Finset (Fin m)) : (Fin m → ℝ) → ℝ :=
  coordinateWordDerivative f (s.sort (· ≤ ·))

@[simp] theorem coordinateWordDerivative_nil {m : ℕ} (f : (Fin m → ℝ) → ℝ) :
    coordinateWordDerivative f [] = f := rfl

@[simp] theorem mixedDerivative_empty {m : ℕ} (f : (Fin m → ℝ) → ℝ) :
    mixedDerivative f ∅ = f := by simp [mixedDerivative]

theorem contDiff_coordinateWordDerivative {m : ℕ} {f : (Fin m → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) (w : List (Fin m)) :
    ContDiff ℝ ∞ (coordinateWordDerivative f w) := by
  induction w with
  | nil => exact hf
  | cons i w ih =>
      exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

theorem hasCompactSupport_coordinateWordDerivative {m : ℕ}
    {f : (Fin m → ℝ) → ℝ} (hcf : HasCompactSupport f) (w : List (Fin m)) :
    HasCompactSupport (coordinateWordDerivative f w) := by
  induction w with
  | nil => exact hcf
  | cons i w ih => exact ih.fderiv_apply ℝ (Pi.single i 1)

theorem contDiff_mixedDerivative {m : ℕ} {f : (Fin m → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) (s : Finset (Fin m)) :
    ContDiff ℝ ∞ (mixedDerivative f s) :=
  contDiff_coordinateWordDerivative hf _

theorem hasCompactSupport_mixedDerivative {m : ℕ} {f : (Fin m → ℝ) → ℝ}
    (hcf : HasCompactSupport f) (s : Finset (Fin m)) :
    HasCompactSupport (mixedDerivative f s) :=
  hasCompactSupport_coordinateWordDerivative hcf _

theorem integrable_sq_mixedDerivative {m : ℕ} {f : (Fin m → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) (s : Finset (Fin m)) :
    Integrable (fun x ↦ (mixedDerivative f s x) ^ 2) := by
  have hc : Continuous (fun x ↦ (mixedDerivative f s x) ^ 2) :=
    (contDiff_mixedDerivative hf s).continuous.pow 2
  have hcs : HasCompactSupport (fun x ↦ (mixedDerivative f s x) ^ 2) :=
    (hasCompactSupport_mixedDerivative hcf s).comp_left (g := fun z : ℝ ↦ z ^ 2) (by simp)
  exact hc.integrable_of_hasCompactSupport hcs

private theorem compactSupport_comp_of_leftInverse
    {A B : Type*} [TopologicalSpace A] [T2Space A] [TopologicalSpace B]
    {f : B → ℝ} (hcf : HasCompactSupport f) {e : A → B} {r : B → A}
    (hr : Continuous r) (hre : Function.LeftInverse r e) :
    HasCompactSupport (fun x ↦ f (e x)) := by
  apply HasCompactSupport.of_support_subset_isCompact (hcf.image hr)
  intro x hx
  exact ⟨e x, subset_closure hx, hre x⟩

private theorem smooth_cons_slice {m : ℕ} (t : ℝ) :
    ContDiff ℝ ∞ (fun y : Fin m → ℝ ↦ (Fin.cons t y : Fin (m + 1) → ℝ)) := by
  apply contDiff_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simpa using (contDiff_const : ContDiff ℝ ∞ (fun _ : Fin m → ℝ ↦ t))
  · simpa using (contDiff_apply ℝ (fun _ : Fin m ↦ ℝ) j : ContDiff ℝ ∞ (fun y : Fin m → ℝ ↦ y j))

private theorem smooth_cons_line {m : ℕ} (y : Fin m → ℝ) :
    ContDiff ℝ ∞ (fun t : ℝ ↦ (Fin.cons t y : Fin (m + 1) → ℝ)) := by
  apply contDiff_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · change ContDiff ℝ ∞ (fun t : ℝ ↦ t)
    exact contDiff_id
  · simpa using (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ ↦ y j))

private theorem compactSupport_cons_slice {m : ℕ} {f : (Fin (m + 1) → ℝ) → ℝ}
    (hcf : HasCompactSupport f) (t : ℝ) :
    HasCompactSupport (fun y : Fin m → ℝ ↦ f (Fin.cons t y)) := by
  apply compactSupport_comp_of_leftInverse hcf
    (r := fun x : Fin (m + 1) → ℝ ↦ fun i : Fin m ↦ x i.succ)
  · exact continuous_pi (fun i ↦ continuous_apply i.succ)
  · intro y; rfl

private theorem compactSupport_cons_line {m : ℕ} {f : (Fin (m + 1) → ℝ) → ℝ}
    (hcf : HasCompactSupport f) (y : Fin m → ℝ) :
    HasCompactSupport (fun t : ℝ ↦ f (Fin.cons t y)) := by
  exact compactSupport_comp_of_leftInverse hcf (continuous_apply 0) (fun _ ↦ rfl)

private theorem derivative_cons_slice {m : ℕ} {f : (Fin (m + 1) → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) (t : ℝ) (i : Fin m) (y : Fin m → ℝ) :
    fderiv ℝ (fun z : Fin m → ℝ ↦ f (Fin.cons t z)) y (Pi.single i 1) =
      fderiv ℝ f (Fin.cons t y) (Pi.single i.succ 1) := by
  have he : HasFDerivAt (fun z : Fin m → ℝ ↦ (Fin.cons t z : Fin (m + 1) → ℝ))
      ((0 : (Fin m → ℝ) →L[ℝ] ℝ).finCons (ContinuousLinearMap.id ℝ _)) y :=
    (hasFDerivAt_const t y).finCons (hasFDerivAt_id y)
  have hd := ((hf.differentiable (by simp) (Fin.cons t y)).hasFDerivAt.comp y he).fderiv
  change fderiv ℝ (fun z : Fin m → ℝ ↦ f (Fin.cons t z)) y = _ at hd
  rw [hd]
  change fderiv ℝ f (Fin.cons t y) _ = _
  congr 1
  ext j
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · simp
  · simp [Pi.single_apply]

private theorem derivative_cons_line {m : ℕ} {f : (Fin (m + 1) → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) (y : Fin m → ℝ) (t : ℝ) :
    deriv (fun r : ℝ ↦ f (Fin.cons r y)) t =
      fderiv ℝ f (Fin.cons t y) (Pi.single 0 1) := by
  have he : HasDerivAt (fun r : ℝ ↦ (Fin.cons r y : Fin (m + 1) → ℝ))
      (Fin.cons 1 (0 : Fin m → ℝ)) t :=
    (hasDerivAt_id t).finCons (hasDerivAt_const t y)
  have hd := ((hf.differentiable (by simp) (Fin.cons t y)).hasFDerivAt.comp_hasDerivAt t he).deriv
  change deriv (fun r : ℝ ↦ f (Fin.cons r y)) t = _ at hd
  rw [hd]
  congr 1
  ext j
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · simp
  · simp

private theorem wordDerivative_cons_slice {m : ℕ} {f : (Fin (m + 1) → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) (t : ℝ) (w : List (Fin m)) :
    coordinateWordDerivative (fun z : Fin m → ℝ ↦ f (Fin.cons t z)) w =
      fun z ↦ coordinateWordDerivative f (w.map Fin.succ) (Fin.cons t z) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      simp only [coordinateWordDerivative, List.map_cons]
      rw [ih]
      funext z
      exact derivative_cons_slice (contDiff_coordinateWordDerivative hf _) t i z

private theorem integral_cons {m : ℕ} (g : (Fin (m + 1) → ℝ) → ℝ) :
    (∫ p : ℝ × (Fin m → ℝ), g (Fin.cons p.1 p.2)) = ∫ x, g x := by
  have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) 0).symm
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Fin.zero_succAbove, Function.comp_def, Equiv.coe_fn_mk, cast_eq] using he.integral_comp' g

private theorem integrable_cons {m : ℕ} {g : (Fin (m + 1) → ℝ) → ℝ}
    (hg : Integrable g) :
    Integrable (fun p : ℝ × (Fin m → ℝ) ↦ g (Fin.cons p.1 p.2)) := by
  have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) 0).symm
  have hi := (he.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _) (g := g)).mpr hg
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Fin.zero_succAbove, Function.comp_def, Equiv.coe_fn_mk, cast_eq] using hi

private theorem sort_tailSet {m : ℕ} (s : Finset (Fin m)) :
    (s.map (Fin.succEmb m)).sort (· ≤ ·) = (s.sort (· ≤ ·)).map Fin.succ := by
  symm
  exact Finset.map_sort (s := s) (f := Fin.succEmb m) (r := (· ≤ ·))
    (r' := (· ≤ ·)) (fun a _ b _ ↦ Fin.succ_le_succ_iff.symm)

private theorem sort_insert_zero_tailSet {m : ℕ} (s : Finset (Fin m)) :
    (insert 0 (s.map (Fin.succEmb m))).sort (· ≤ ·) =
      0 :: (s.sort (· ≤ ·)).map Fin.succ := by
  rw [Finset.sort_insert (· ≤ ·) (fun b _ ↦ Fin.zero_le b) (by simp), sort_tailSet]

private theorem mixedDerivative_cons_slice {m : ℕ}
    {f : (Fin (m + 1) → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (t : ℝ)
    (s : Finset (Fin m)) :
    mixedDerivative (fun z : Fin m → ℝ ↦ f (Fin.cons t z)) s =
      fun z ↦ mixedDerivative f (s.map (Fin.succEmb m)) (Fin.cons t z) := by
  simp only [mixedDerivative, sort_tailSet]
  exact wordDerivative_cons_slice hf t _

private theorem mixedDerivative_insert_zero_tailSet {m : ℕ}
    (f : (Fin (m + 1) → ℝ) → ℝ) (s : Finset (Fin m)) :
    mixedDerivative f (insert 0 (s.map (Fin.succEmb m))) =
      fun z ↦ fderiv ℝ (mixedDerivative f (s.map (Fin.succEmb m))) z (Pi.single 0 1) := by
  simp only [mixedDerivative, sort_insert_zero_tailSet, coordinateWordDerivative, sort_tailSet]

private theorem integral_sq_cons_slice_le {m : ℕ}
    {g : (Fin (m + 1) → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (t : ℝ) :
    (∫ y : Fin m → ℝ, (g (Fin.cons t y)) ^ 2) ≤
      (∫ x, (g x) ^ 2) + ∫ x, (fderiv ℝ g x (Pi.single 0 1)) ^ 2 := by
  let d : (Fin (m + 1) → ℝ) → ℝ := fun x ↦ fderiv ℝ g x (Pi.single 0 1)
  have hd : ContDiff ℝ ∞ d := (hg.fderiv_right (by simp)).clm_apply contDiff_const
  have hcd : HasCompactSupport d := hcg.fderiv_apply ℝ _
  have hgi : Integrable (fun x ↦ (g x) ^ 2) := by
    simpa only [mixedDerivative_empty] using integrable_sq_mixedDerivative hg hcg ∅
  have hdi : Integrable (fun x ↦ (d x) ^ 2) := by
    simpa only [mixedDerivative_empty] using integrable_sq_mixedDerivative hd hcd ∅
  have hgp := integrable_cons hgi
  have hdp := integrable_cons hdi
  have hsi : Integrable (fun y : Fin m → ℝ ↦ (g (Fin.cons t y)) ^ 2) := by
    simpa only [mixedDerivative_empty, Function.comp_def] using integrable_sq_mixedDerivative
      (hg.comp (smooth_cons_slice t)) (compactSupport_cons_slice hcg t) ∅
  have hpoint (y : Fin m → ℝ) : (g (Fin.cons t y)) ^ 2 ≤
      (∫ r : ℝ, (g (Fin.cons r y)) ^ 2) + ∫ r : ℝ, (d (Fin.cons r y)) ^ 2 := by
    have h := sq_le_integral_sq_add_integral_deriv_sq
      ((hg.comp (smooth_cons_line y)).of_le (by simp)) (compactSupport_cons_line hcg y) t
    simpa only [Function.comp_def, derivative_cons_line hg, d] using h
  calc
    _ ≤ ∫ y : Fin m → ℝ,
        ((∫ r : ℝ, (g (Fin.cons r y)) ^ 2) + ∫ r : ℝ, (d (Fin.cons r y)) ^ 2) :=
      integral_mono hsi (hgp.integral_prod_right.add hdp.integral_prod_right) hpoint
    _ = (∫ y : Fin m → ℝ, ∫ r : ℝ, (g (Fin.cons r y)) ^ 2) +
        ∫ y : Fin m → ℝ, ∫ r : ℝ, (d (Fin.cons r y)) ^ 2 :=
      integral_add hgp.integral_prod_right hdp.integral_prod_right
    _ = (∫ p : ℝ × (Fin m → ℝ), (g (Fin.cons p.1 p.2)) ^ 2) +
        ∫ p : ℝ × (Fin m → ℝ), (d (Fin.cons p.1 p.2)) ^ 2 := by
      rw [← integral_prod_symm _ hgp, ← integral_prod_symm _ hdp]
      rfl
    _ = _ := by
      exact congrArg₂ (· + ·) (integral_cons (fun x ↦ (g x) ^ 2))
        (integral_cons (fun x ↦ (d x) ^ 2))

private theorem sum_finset_fin_succ {m : ℕ} (F : Finset (Fin (m + 1)) → ℝ) :
    (∑ s : Finset (Fin (m + 1)), F s) =
      (∑ s : Finset (Fin m), F (s.map (Fin.succEmb m))) +
        ∑ s : Finset (Fin m), F (insert 0 (s.map (Fin.succEmb m))) := by
  classical
  have hu : (Finset.univ : Finset (Fin (m + 1))) =
      insert 0 ((Finset.univ : Finset (Fin m)).image Fin.succ) := by
    ext j
    refine Fin.cases ?_ (fun k ↦ ?_) j <;> simp
  have hi : Function.Injective (fun s : Finset (Fin m) ↦ s.image Fin.succ) :=
    Finset.image_injective (Fin.succ_injective m)
  calc
    _ = ∑ s ∈ (insert 0 ((Finset.univ : Finset (Fin m)).image Fin.succ)).powerset,
        F s := by rw [← hu, Finset.powerset_univ]
    _ = (∑ s ∈ ((Finset.univ : Finset (Fin m)).image Fin.succ).powerset, F s) +
        ∑ s ∈ ((Finset.univ : Finset (Fin m)).image Fin.succ).powerset,
          F (insert 0 s) :=
      Finset.sum_powerset_insert (by simp) F
    _ = _ := by
      rw [Finset.powerset_image, Finset.sum_image (fun a _ b _ h ↦ hi h),
        Finset.sum_image (fun a _ b _ h ↦ hi h)]
      simp only [Finset.powerset_univ, Finset.map_eq_image, Fin.coe_succEmb]

/-- The mixed Sobolev evaluation bound, with constant one in every finite dimension.
Each coordinate is differentiated at most once in each summand. -/
theorem sq_le_sum_integral_sq_mixedDerivative {m : ℕ} {f : (Fin m → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) (x : Fin m → ℝ) :
    (f x) ^ 2 ≤ ∑ s : Finset (Fin m), ∫ y, (mixedDerivative f s y) ^ 2 := by
  induction m with
  | zero =>
      have hs : ∀ s : Finset (Fin 0), s = ∅ := fun s ↦ Subsingleton.elim _ _
      have hu : (Finset.univ : Finset (Finset (Fin 0))) = {∅} := by
        ext s
        exact iff_of_true (Finset.mem_univ s) (Finset.mem_singleton.mpr (hs s))
      rw [hu, Finset.sum_singleton, mixedDerivative_empty]
      rw [volume_pi, Measure.pi_of_empty]
      simp only [integral_dirac]
      exact le_of_eq (congrArg (fun y ↦ (f y) ^ 2) (Subsingleton.elim _ _))
  | succ m ih =>
      let fs : (Fin m → ℝ) → ℝ := fun y ↦ f (Fin.cons (x 0) y)
      have hfs : ContDiff ℝ ∞ fs := hf.comp (smooth_cons_slice (x 0))
      have hcfs : HasCompactSupport fs := compactSupport_cons_slice hcf (x 0)
      have hx : Fin.cons (x 0) (fun i : Fin m ↦ x i.succ) = x := by
        ext j
        exact Fin.cases rfl (fun i ↦ rfl) j
      have hb := ih hfs hcfs (fun i : Fin m ↦ x i.succ)
      have hbound : (f x) ^ 2 ≤
          ∑ s : Finset (Fin m), ∫ y : Fin m → ℝ,
            (mixedDerivative f (s.map (Fin.succEmb m)) (Fin.cons (x 0) y)) ^ 2 := by
        simpa only [fs, mixedDerivative_cons_slice hf, hx] using hb
      calc
        _ ≤ ∑ s : Finset (Fin m), ∫ y : Fin m → ℝ,
            (mixedDerivative f (s.map (Fin.succEmb m)) (Fin.cons (x 0) y)) ^ 2 := hbound
        _ ≤ ∑ s : Finset (Fin m),
            ((∫ y, (mixedDerivative f (s.map (Fin.succEmb m)) y) ^ 2) +
              ∫ y, (mixedDerivative f (insert 0 (s.map (Fin.succEmb m))) y) ^ 2) := by
          apply Finset.sum_le_sum
          intro s _
          simpa only [mixedDerivative_insert_zero_tailSet] using
            integral_sq_cons_slice_le (contDiff_mixedDerivative hf (s.map (Fin.succEmb m)))
              (hasCompactSupport_mixedDerivative hcf (s.map (Fin.succEmb m))) (x 0)
        _ = _ := by
          rw [Finset.sum_add_distrib]
          exact (sum_finset_fin_succ
            (fun s : Finset (Fin (m + 1)) ↦ ∫ y, (mixedDerivative f s y) ^ 2)).symm

/-- Coordinate word derivatives are linear on smooth functions. -/
theorem coordinateWordDerivative_sub {m : ℕ} {f g : (Fin m → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (w : List (Fin m)) :
    coordinateWordDerivative (fun x ↦ f x - g x) w =
      fun x ↦ coordinateWordDerivative f w x - coordinateWordDerivative g w x := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      simp only [coordinateWordDerivative]
      rw [ih]
      funext x
      rw [fderiv_fun_sub ((contDiff_coordinateWordDerivative hf w).differentiable (by simp) x)
        ((contDiff_coordinateWordDerivative hg w).differentiable (by simp) x)]
      rfl

/-- The mixed derivatives of a difference are the differences of its actual mixed derivatives. -/
theorem mixedDerivative_sub {m : ℕ} {f g : (Fin m → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (s : Finset (Fin m)) :
    mixedDerivative (fun x ↦ f x - g x) s =
      fun x ↦ mixedDerivative f s x - mixedDerivative g s x :=
  coordinateWordDerivative_sub hf hg _

/-- Mixed Sobolev evaluation for the difference of two smooth compactly supported functions. -/
theorem sub_sq_le_sum_integral_sub_sq_mixedDerivative {m : ℕ}
    {f g : (Fin m → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f)
    (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) (x : Fin m → ℝ) :
    (f x - g x) ^ 2 ≤ ∑ s : Finset (Fin m),
      ∫ y, (mixedDerivative f s y - mixedDerivative g s y) ^ 2 := by
  simpa only [mixedDerivative_sub hf hg] using
    sq_le_sum_integral_sq_mixedDerivative (hf.sub hg) (hcf.sub hcg) x

/-- Cauchy control of the finitely many mixed `L²` differences gives uniform
Cauchy control of the actual smooth functions. -/
theorem uniform_cauchy_of_mixed_integral_sq_cauchy {m : ℕ}
    {f : ℕ → (Fin m → ℝ) → ℝ} (hf : ∀ k, ContDiff ℝ ∞ (f k))
    (hcf : ∀ k, HasCompactSupport (f k))
    (hcauchy : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ k ≥ N, ∀ l ≥ N,
      (∑ s : Finset (Fin m),
        ∫ y, (mixedDerivative (f k) s y - mixedDerivative (f l) s y) ^ 2) < δ) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k ≥ N, ∀ l ≥ N, ∀ x : Fin m → ℝ,
      |f k x - f l x| < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := hcauchy (ε ^ 2) (sq_pos_of_pos hε)
  refine ⟨N, fun k hk l hl x ↦ ?_⟩
  have hb := sub_sq_le_sum_integral_sub_sq_mixedDerivative
    (hf k) (hcf k) (hf l) (hcf l) x
  have hsquare : (f k x - f l x) ^ 2 < ε ^ 2 := hb.trans_lt (hN k hk l hl)
  exact (sq_lt_sq₀ (abs_nonneg _) hε.le).mp (by simpa only [sq_abs] using hsquare)

end Yau.LeafProofs.L16Aux
