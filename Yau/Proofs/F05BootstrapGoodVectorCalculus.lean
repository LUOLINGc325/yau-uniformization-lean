import Yau.Proofs.F05BootstrapFiniteCalculus

/-! Vector-valued good calculus for actual nonlinear principal coefficients.
The scalar-vector product rules hold at the closed terminal time. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic
variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem F05_good_vector_diff_add {T : ℝ} {d : Option (RIdx n)} {Q : Set (Point n)}
    {f g : Point n → V} (hf : F05GoodDiffOn T d f Q) (hg : F05GoodDiffOn T d g Q) :
    F05GoodDiffOn T d (fun z => f z+g z) Q := by
  intro z hz
  cases d with
  | none => exact (hf z hz).add (hg z hz)
  | some k => exact (hf z hz).add (hg z hz)

theorem F05_good_vector_partial_add {T : ℝ} {d : Option (RIdx n)} {Q : Set (Point n)}
    {f g : Point n → V} (hf : F05GoodDiffOn T d f Q) (hg : F05GoodDiffOn T d g Q)
    {z : Point n} (hz : z ∈ Q) :
    F05GoodPartial T d (fun p => f p+g p) z = F05GoodPartial T d f z+F05GoodPartial T d g z := by
  cases d with
  | none => exact derivWithin_fun_add (hf z hz) (hg z hz)
  | some k => exact deriv_fun_add (hf z hz) (hg z hz)

theorem F05_good_vector_diff_list_sum {ι : Type*} (xs : List ι) {T : ℝ}
    {d : Option (RIdx n)} {Q : Set (Point n)} {f : ι → Point n → V}
    (hf : ∀ i ∈ xs, F05GoodDiffOn T d (f i) Q) :
    F05GoodDiffOn T d (fun z => (xs.map (fun i => f i z)).sum) Q := by
  induction xs with
  | nil =>
    intro z hz
    cases d with
    | none => exact differentiableWithinAt_const (0 : V)
    | some k => exact differentiableAt_const (0 : V)
  | cons i xs ih =>
    exact F05_good_vector_diff_add (hf i List.mem_cons_self)
      (ih (fun j hj => hf j (List.mem_cons_of_mem _ hj)))

theorem F05_good_vector_partial_list_sum {ι : Type*} (xs : List ι) {T : ℝ}
    {d : Option (RIdx n)} {Q : Set (Point n)} {f : ι → Point n → V}
    (hf : ∀ i ∈ xs, F05GoodDiffOn T d (f i) Q) {z : Point n} (hz : z ∈ Q) :
    F05GoodPartial T d (fun p => (xs.map (fun i => f i p)).sum) z =
      (xs.map (fun i => F05GoodPartial T d (f i) z)).sum := by
  induction xs with
  | nil => cases d <;> simp only [List.map_nil,List.sum_nil,F05GoodPartial,derivWithin_fun_const,Pi.zero_apply,deriv_const]
  | cons i xs ih =>
    have hTail := fun j hj => hf j (List.mem_cons_of_mem i hj)
    change F05GoodPartial T d (fun p => f i p+(xs.map (fun j => f j p)).sum) z = _
    rw [F05_good_vector_partial_add (hf i List.mem_cons_self) (F05_good_vector_diff_list_sum xs hTail) hz,ih hTail]
    rfl

theorem F05_good_diff_smul {T : ℝ} {d : Option (RIdx n)} {Q : Set (Point n)}
    {c : Point n → ℝ} {f : Point n → V} (hc : F05GoodDiffOn T d c Q)
    (hf : F05GoodDiffOn T d f Q) : F05GoodDiffOn T d (fun z => c z • f z) Q := by
  intro z hz
  cases d with
  | none => exact (hc z hz).smul (hf z hz)
  | some k => exact (hc z hz).smul (hf z hz)

theorem F05_good_partial_smul {T : ℝ} {d : Option (RIdx n)} {Q : Set (Point n)}
    {c : Point n → ℝ} {f : Point n → V} (hc : F05GoodDiffOn T d c Q)
    (hf : F05GoodDiffOn T d f Q) {z : Point n} (hz : z ∈ Q) :
    F05GoodPartial T d (fun p => c p • f p) z =
      F05GoodPartial T d c z • f z+c z • F05GoodPartial T d f z := by
  cases d with
  | none => exact (derivWithin_fun_smul (hc z hz) (hf z hz)).trans (add_comm _ _)
  | some k =>
    simpa only [F05GoodPartial,zero_smul,add_zero] using
      (deriv_fun_smul (hc z hz) (hf z hz)).trans (add_comm _ _)

theorem F05_vector_list_sum_flatMap_pairs {ι : Type*} (xs : List ι) (f g : ι → V) :
    (xs.flatMap (fun i => [f i,g i])).sum = (xs.map (fun i => f i+g i)).sum := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    simp only [List.flatMap_cons,List.sum_append,List.sum_cons,List.sum_nil,List.map_cons,ih,add_zero,add_assoc]

end Yau.Proofs.F05Aux
