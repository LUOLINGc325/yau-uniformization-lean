import Yau.Proofs.F05BootstrapGoodAlgebra

/-! Finite sums and continuous linear evaluations preserve the actual
one-variable good calculus, including the closed terminal time. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic
variable {n : ℕ}

theorem F05_good_diff_add {T : ℝ} {d : Option (RIdx n)} {Q : Set (Point n)}
    {f g : Point n → ℝ} (hf : F05GoodDiffOn T d f Q) (hg : F05GoodDiffOn T d g Q) :
    F05GoodDiffOn T d (fun z => f z+g z) Q := by
  intro z hz
  cases d with
  | none => exact (hf z hz).add (hg z hz)
  | some k => exact (hf z hz).add (hg z hz)

theorem F05_good_diff_finset_sum {ι : Type*} (s : Finset ι) {T : ℝ}
    {d : Option (RIdx n)} {Q : Set (Point n)} {f : ι → Point n → ℝ}
    (hf : ∀ i ∈ s, F05GoodDiffOn T d (f i) Q) :
    F05GoodDiffOn T d (fun z => ∑ i ∈ s,f i z) Q := by
  intro z hz
  cases d with
  | none => exact DifferentiableWithinAt.fun_sum (fun i hi => hf i hi z hz)
  | some k => exact DifferentiableAt.fun_sum (fun i hi => hf i hi z hz)

theorem F05_good_partial_finset_sum {ι : Type*} (s : Finset ι) {T : ℝ}
    {d : Option (RIdx n)} {Q : Set (Point n)} {f : ι → Point n → ℝ}
    (hf : ∀ i ∈ s, F05GoodDiffOn T d (f i) Q) {z : Point n} (hz : z ∈ Q) :
    F05GoodPartial T d (fun p => ∑ i ∈ s,f i p) z = ∑ i ∈ s,F05GoodPartial T d (f i) z := by
  cases d with
  | none => exact derivWithin_fun_sum (fun i hi => hf i hi z hz)
  | some k =>
    simpa only [F05GoodPartial,zero_smul,add_zero] using deriv_fun_sum (fun i hi => hf i hi z hz)

theorem F05_good_diff_list_sum {ι : Type*} (xs : List ι) {T : ℝ}
    {d : Option (RIdx n)} {Q : Set (Point n)} {f : ι → Point n → ℝ}
    (hf : ∀ i ∈ xs, F05GoodDiffOn T d (f i) Q) :
    F05GoodDiffOn T d (fun z => (xs.map (fun i => f i z)).sum) Q := by
  induction xs with
  | nil =>
    intro z hz
    cases d with
    | none => exact differentiableWithinAt_const (0 : ℝ)
    | some k => exact differentiableAt_const (0 : ℝ)
  | cons i xs ih =>
    exact F05_good_diff_add (hf i List.mem_cons_self)
      (ih (fun j hj => hf j (List.mem_cons_of_mem _ hj)))

theorem F05_good_partial_list_sum {ι : Type*} (xs : List ι) {T : ℝ}
    {d : Option (RIdx n)} {Q : Set (Point n)} {f : ι → Point n → ℝ}
    (hf : ∀ i ∈ xs, F05GoodDiffOn T d (f i) Q) {z : Point n} (hz : z ∈ Q) :
    F05GoodPartial T d (fun p => (xs.map (fun i => f i p)).sum) z =
      (xs.map (fun i => F05GoodPartial T d (f i) z)).sum := by
  induction xs with
  | nil => cases d <;> simp only [List.map_nil,List.sum_nil,F05GoodPartial,derivWithin_fun_const,Pi.zero_apply,deriv_const]
  | cons i xs ih =>
    have hTail := fun j hj => hf j (List.mem_cons_of_mem i hj)
    change F05GoodPartial T d (fun p => f i p+(xs.map (fun j => f j p)).sum) z = _
    rw [F05_good_partial_add (hf i List.mem_cons_self) (F05_good_diff_list_sum xs hTail) hz,ih hTail]
    rfl

theorem F05_good_diff_clm {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (L : V →L[ℝ] W)
    {T : ℝ} {d : Option (RIdx n)} {Q : Set (Point n)} {f : Point n → V}
    (hf : F05GoodDiffOn T d f Q) : F05GoodDiffOn T d (fun z => L (f z)) Q := by
  intro z hz
  cases d with
  | none => exact L.differentiableAt.comp_differentiableWithinAt z.2 (hf z hz)
  | some k => exact L.differentiableAt.comp 0 (hf z hz)

theorem F05_good_partial_clm {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (L : V →L[ℝ] W)
    {T : ℝ} {d : Option (RIdx n)} {Q : Set (Point n)} {f : Point n → V}
    (hf : F05GoodDiffOn T d f Q) {z : Point n} (hz : z ∈ Q) (ht : z.2 ∈ Ioc 0 T) :
    F05GoodPartial T d (fun p => L (f p)) z = L (F05GoodPartial T d f z) := by
  cases d with
  | none =>
    exact (L.hasFDerivAt.comp_hasDerivWithinAt z.2 (hf z hz).hasDerivWithinAt).derivWithin
      (uniqueDiffOn_Ioc 0 T z.2 ht)
  | some k =>
    simpa only [F05GoodPartial,Function.comp_def] using
      (L.hasFDerivAt.comp_hasDerivAt 0 (hf z hz).hasDerivAt).deriv

end Yau.Proofs.F05Aux
