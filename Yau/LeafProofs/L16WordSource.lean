import Yau.LeafProofs.L16SpatialSchwarz

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

def commutatorSplits {E : Type*} : List E → List (List E × List E)
  | [] => []
  | e :: w => ([e],w)::(commutatorSplits w).flatMap
      (fun st => [(e::st.1,st.2),(st.1,e::st.2)])

theorem commutatorSplits_properties {E : Type*} (w : List E) (st : List E × List E)
    (h : st ∈ commutatorSplits w) : st.1 ≠ [] ∧ st.1.length+st.2.length = w.length := by
  induction w generalizing st with
  | nil => simp only [commutatorSplits,List.not_mem_nil] at h
  | cons e w ih =>
    rcases List.mem_cons.mp h with hst | hst
    · subst st
      exact ⟨by simp,by simp only [List.length_cons,List.length_nil]; omega⟩
    · obtain ⟨st',hst',hChoice⟩ := List.mem_flatMap.mp hst
      obtain ⟨hne,hLength⟩ := ih st' hst'
      rcases List.mem_cons.mp hChoice with hChoice | hChoice
      · subst st
        exact ⟨by simp,by simp only [List.length_cons]; omega⟩
      · have hChoice' : st = (st'.1,e::st'.2) := by simpa only [List.mem_singleton] using hChoice
        subst st
        exact ⟨hne,by simp only [List.length_cons]; omega⟩

theorem commutatorSplits_lower_length {E : Type*} (w : List E) (st : List E × List E)
    (h : st ∈ commutatorSplits w) : st.2.length+1 ≤ w.length := by
  obtain ⟨hne,hLength⟩ := commutatorSplits_properties w st h
  have hPos : 1 ≤ st.1.length := by
    cases hs : st.1 with
    | nil => exact False.elim (hne hs)
    | cons a s => simp only [List.length_cons]; omega
  omega

def matrixEntryCLM {n : ℕ} (i j : Yau.RIdx n) : Mat n →L[ℝ] ℝ :=
  ({ toFun := fun A => A i j
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : Mat n →ₗ[ℝ] ℝ).mkContinuous 1
    (fun A => by
      change |A i j| ≤ 1*‖A‖
      simpa only [one_mul] using frobenius_entry_abs_le A i j)

theorem matrixEntryCLM_apply {n : ℕ} (i j : Yau.RIdx n) (A : Mat n) : matrixEntryCLM i j A = A i j := rfl

theorem spatialPartial_matrix_entry {n : ℕ} {a : Point n → Mat n} {p : Point n}
    (ha : DifferentiableAt ℝ (fun x => a (x,p.2)) p.1) (e : Space n) (i j : Yau.RIdx n) :
    spatialPartial (fun q => a q i j) e p = spatialPartial a e p i j := by
  have h := congrArg (fun L : Space n →L[ℝ] ℝ => L e)
    (((matrixEntryCLM i j).hasFDerivAt.comp p.1 ha.hasFDerivAt).fderiv)
  change fderiv ℝ (fun x => a (x,p.2) i j) p.1 e =
    fderiv ℝ (fun x => a (x,p.2)) p.1 e i j at h
  exact h

theorem matrixEntry_spatial_differentiableAt {n : ℕ} {a : Point n → Mat n} {p : Point n}
    (ha : DifferentiableAt ℝ (fun x => a (x,p.2)) p.1) (i j : Yau.RIdx n) :
    DifferentiableAt ℝ (fun x => a (x,p.2) i j) p.1 := by
  change DifferentiableAt ℝ ((matrixEntryCLM i j) ∘ (fun x => a (x,p.2))) p.1
  exact (matrixEntryCLM i j).differentiableAt.comp p.1 ha

theorem holderBound_list_sum {n : ℕ} {ι : Type*} {α : ℝ} {Q : Set (Point n)}
    (xs : List ι) (f : ι → Point n → ℝ)
    (hf : ∀ i ∈ xs, ∃ C : ℝ, HolderBound α Q (f i) C) :
    ∃ C : ℝ, HolderBound α Q (fun p => (xs.map (fun i => f i p)).sum) C := by
  induction xs with
  | nil => exact ⟨0,by simp [HolderBound]⟩
  | cons i xs ih =>
    obtain ⟨C,hC⟩ := hf i List.mem_cons_self
    obtain ⟨D,hD⟩ := ih (fun j hj => hf j (List.mem_cons_of_mem _ hj))
    exact ⟨C+D,by simpa only [List.map_cons,List.sum_cons] using holderBound_add hC hD⟩

def wordCorrection {n : ℕ} (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
    (u : Point n → ℝ) (s t : List (Space n)) (p : Point n) : ℝ :=
  (∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n,
    spatialWordDerivative s a p i j*spatialDD (spatialWordDerivative t u) p (Yau.realVec i) (Yau.realVec j))+
  ∑ i : Yau.RIdx n, spatialWordDerivative s (fun q => b q i) p*
    spatialD (spatialWordDerivative t u) p (Yau.realVec i)

def wordSource {n : ℕ} (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
    (f u : Point n → ℝ) (w : List (Space n)) (p : Point n) : ℝ :=
  spatialWordDerivative w f p+((commutatorSplits w).map
    (fun st => wordCorrection a b u st.1 st.2 p)).sum

def wordSourceDerivative {n : ℕ} (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
    (f u : Point n → ℝ) (e : Space n) (w : List (Space n)) (p : Point n) : ℝ :=
  spatialWordDerivative (e::w) f p+((commutatorSplits w).map
    (fun st => wordCorrection a b u (e::st.1) st.2 p+wordCorrection a b u st.1 (e::st.2) p)).sum

theorem list_sum_flatMap_pairs {ι : Type*} (xs : List ι) (f g : ι → ℝ) :
    (xs.flatMap (fun i => [f i,g i])).sum = (xs.map (fun i => f i+g i)).sum := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    simp only [List.flatMap_cons,List.sum_append,List.sum_cons,List.sum_nil,List.map_cons,ih,add_zero,add_assoc]

theorem wordSource_cons {n : ℕ} (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
    (f u : Point n → ℝ) (e : Space n) (w : List (Space n)) :
    wordSource a b f u (e::w) = fun p => wordSourceDerivative a b f u e w p+wordCorrection a b u [e] w p := by
  funext p
  simp only [wordSource,wordSourceDerivative,commutatorSplits,List.map_cons,List.sum_cons,
    List.map_flatMap,List.map_nil]
  rw [list_sum_flatMap_pairs]
  ring

theorem wordSource_nil {n : ℕ} (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
    (f u : Point n → ℝ) : wordSource a b f u [] = f := by
  funext p
  simp only [wordSource,commutatorSplits,List.map_nil,List.sum_nil,spatialWordDerivative,add_zero]

theorem spatialPartial_spatialPartial_eq_spatialDD {n : ℕ} {T : ℝ} {u : Point n → ℝ}
    (hu : C2 (cylinder Set.univ 0 T) u) (e v : Space n) {p : Point n}
    (hp : p ∈ cylinder Set.univ 0 T) :
    spatialPartial (spatialPartial u v) e p = spatialDD u p e v := by
  have hD : ContDiff ℝ 1 (fderiv ℝ (fun x : Space n => u (x,p.2))) :=
    (c2_spatialSlice_contDiff hu hp.2).fderiv_right (by norm_num)
  exact fderiv_clm_const_eval (hD.differentiable (by norm_num) p.1) v e

theorem spatialPartial_add {n : ℕ} {f g : Point n → ℝ} {p : Point n}
    (hf : DifferentiableAt ℝ (fun x => f (x,p.2)) p.1)
    (hg : DifferentiableAt ℝ (fun x => g (x,p.2)) p.1) (e : Space n) :
    spatialPartial (fun q => f q+g q) e p = spatialPartial f e p+spatialPartial g e p := by
  have h := congrArg (fun L : Space n →L[ℝ] ℝ => L e) (fderiv_fun_add hf hg)
  simpa only [spatialPartial,add_apply] using h

theorem spatialPartial_mul {n : ℕ} {f g : Point n → ℝ} {p : Point n}
    (hf : DifferentiableAt ℝ (fun x => f (x,p.2)) p.1)
    (hg : DifferentiableAt ℝ (fun x => g (x,p.2)) p.1) (e : Space n) :
    spatialPartial (fun q => f q*g q) e p = spatialPartial f e p*g p+f p*spatialPartial g e p := by
  have h := congrArg (fun L : Space n →L[ℝ] ℝ => L e) (fderiv_fun_mul hf hg)
  simp only [spatialPartial,add_apply,smul_apply,smul_eq_mul] at h ⊢
  linarith

theorem spatialPartial_finset_sum {n : ℕ} {ι : Type*} (s : Finset ι) {f : ι → Point n → ℝ} {p : Point n}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (fun x => f i (x,p.2)) p.1) (e : Space n) :
    spatialPartial (fun q => ∑ i ∈ s, f i q) e p = ∑ i ∈ s, spatialPartial (f i) e p := by
  have h := congrArg (fun L : Space n →L[ℝ] ℝ => L e) (fderiv_fun_sum hf)
  simpa only [spatialPartial,sum_apply] using h

theorem spatial_list_sum_differentiableAt {n : ℕ} {ι : Type*} (xs : List ι) {f : ι → Point n → ℝ} {p : Point n}
    (hf : ∀ i ∈ xs, DifferentiableAt ℝ (fun x => f i (x,p.2)) p.1) :
    DifferentiableAt ℝ (fun x => (xs.map (fun i => f i (x,p.2))).sum) p.1 := by
  induction xs with
  | nil => exact differentiableAt_const _
  | cons i xs ih =>
    exact (hf i List.mem_cons_self).add (ih (fun j hj => hf j (List.mem_cons_of_mem _ hj)))

theorem spatialPartial_list_sum {n : ℕ} {ι : Type*} (xs : List ι) {f : ι → Point n → ℝ} {p : Point n}
    (hf : ∀ i ∈ xs, DifferentiableAt ℝ (fun x => f i (x,p.2)) p.1) (e : Space n) :
    spatialPartial (fun q => (xs.map (fun i => f i q)).sum) e p =
      (xs.map (fun i => spatialPartial (f i) e p)).sum := by
  induction xs with
  | nil => simp only [List.map_nil,List.sum_nil,spatialPartial,fderiv_fun_const,Pi.zero_apply,zero_apply]
  | cons i xs ih =>
    have hTail (j : ι) (hj : j ∈ xs) := hf j (List.mem_cons_of_mem _ hj)
    change spatialPartial (fun q => f i q+(xs.map (fun j => f j q)).sum) e p = _
    rw [spatialPartial_add (hf i List.mem_cons_self) (spatial_list_sum_differentiableAt xs hTail) e,ih hTail]
    rfl

theorem wordCorrection_holderBound {n : ℕ} {α T M U : ℝ}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {u : Point n → ℝ}
    (s t : List (Space n))
    (ha : HolderBound α (cylinder Set.univ 0 T) (spatialWordDerivative s a) M)
    (hb : ∀ i, HolderBound α (cylinder Set.univ 0 T) (spatialWordDerivative s (fun p => b p i)) M)
    (hu : SchauderBound α (cylinder Set.univ 0 T) (spatialWordDerivative t u) U)
    (hLow : HolderBound α (cylinder Set.univ 0 T)
      (fun p => (spatialWordDerivative t u p,spatialD (spatialWordDerivative t u) p)) U) :
    HolderBound α (cylinder Set.univ 0 T) (wordCorrection a b u s t) (linearizedSourceBudget n 0 M U) := by
  have hPrincipal := hessian_contraction_holderBound ha.1 hu.2.1
    (fun i j => holderBound_matrix_entry ha i j)
    (fun i j p hp => by simpa only [Real.norm_eq_abs] using (holderBound_matrix_entry ha i j).2.1 p hp)
    hu.2.2.2.1 hu.2.2.2.1.2.1
  have hDrift := holderBound_finset_sum Finset.univ (fun i _ =>
    holderBound_mul (hb i) (holderBound_gradient_component (holderBound_snd hLow) i))
  change HolderBound α (cylinder Set.univ 0 T) (fun p => wordCorrection a b u s t p) _
  simpa only [wordCorrection,linearizedSourceBudget,zero_add,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using
    holderBound_add hPrincipal hDrift

theorem wordSourceDerivative_holder {n : ℕ} {α T : ℝ}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {f u : Point n → ℝ}
    (hCoeff : ∀ s : List (Space n), ∃ M : ℝ,
      HolderBound α (cylinder Set.univ 0 T) (spatialWordDerivative s a) M ∧
      ∀ i, HolderBound α (cylinder Set.univ 0 T) (spatialWordDerivative s (fun p => b p i)) M)
    (hf : ∀ s : List (Space n), ∃ F : ℝ,
      HolderBound α (cylinder Set.univ 0 T) (spatialWordDerivative s f) F)
    (k : ℕ) (hU : ∀ t : List (Space n), t.length ≤ k → ∃ U : ℝ,
      SchauderBound α (cylinder Set.univ 0 T) (spatialWordDerivative t u) U ∧
      HolderBound α (cylinder Set.univ 0 T)
        (fun p => (spatialWordDerivative t u p,spatialD (spatialWordDerivative t u) p)) U)
    (e : Space n) (w : List (Space n)) (hw : w.length ≤ k) :
    ∃ F : ℝ, HolderBound α (cylinder Set.univ 0 T) (wordSourceDerivative a b f u e w) F := by
  obtain ⟨F,hF⟩ := hf (e::w)
  obtain ⟨D,hD⟩ := holderBound_list_sum (commutatorSplits w)
    (fun st p => wordCorrection a b u (e::st.1) st.2 p+wordCorrection a b u st.1 (e::st.2) p) (by
      intro st hst
      have hLength := commutatorSplits_lower_length w st hst
      obtain ⟨U,hUt,hUtLow⟩ := hU st.2 (by omega)
      obtain ⟨V,hVt,hVtLow⟩ := hU (e::st.2) (by simp only [List.length_cons]; omega)
      obtain ⟨M,hMA,hMB⟩ := hCoeff (e::st.1)
      obtain ⟨N,hNA,hNB⟩ := hCoeff st.1
      exact ⟨_,holderBound_add (wordCorrection_holderBound _ _ hMA hMB hUt hUtLow)
        (wordCorrection_holderBound _ _ hNA hNB hVt hVtLow)⟩)
  refine ⟨F+D,?_⟩
  change HolderBound α (cylinder Set.univ 0 T) (fun p => wordSourceDerivative a b f u e w p) _
  simpa only [wordSourceDerivative] using holderBound_add hF hD

end Yau.LeafProofs.L16Aux
