import Yau.LeafProofs.L05PucciHarnackAlgebra

open Filter MeasureTheory Set
open scoped Topology
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

def harnackIntervalUnion : List (ℝ × ℝ) → Set ℝ
  | [] => ∅
  | I::L => Ioc I.1 I.2 ∪ harnackIntervalUnion L

def harnackIntervalMerge (A B : ℝ) : List (ℝ × ℝ) → List (ℝ × ℝ)
  | [] => [(A,B)]
  | (C,D)::L => if C ≤ B then harnackIntervalMerge A (max B D) L else (A,B)::(C,D)::L

def harnackIntervalComponents : List (ℝ × ℝ) → List (ℝ × ℝ)
  | [] => []
  | I::L => harnackIntervalMerge I.1 I.2 (harnackIntervalComponents L)

theorem harnack_intervalUnion_mem {L : List (ℝ × ℝ)} {t : ℝ} :
    t∈harnackIntervalUnion L ↔ ∃ I∈L, t∈Ioc I.1 I.2 := by
  induction L with
  | nil => simp [harnackIntervalUnion]
  | cons I L ih => simp only [harnackIntervalUnion,mem_union,ih,List.mem_cons]; aesop

theorem harnack_intervalMerge_lower {L : List (ℝ × ℝ)} {A B ell : ℝ}
    (hA : ell ≤ A) (hL : ∀ I∈L, ell ≤ I.1) :
    ∀ I∈harnackIntervalMerge A B L, ell ≤ I.1 := by
  induction L generalizing B with
  | nil => simpa only [harnackIntervalMerge,List.mem_singleton] using fun I h => h ▸ hA
  | cons I L ih =>
    rcases I with ⟨C,D⟩
    simp only [harnackIntervalMerge]
    split_ifs with h
    · exact ih (fun I hI => hL I (List.mem_cons_of_mem _ hI))
    · intro I hI
      rcases List.mem_cons.mp hI with hI | hI
      · subst I; exact hA
      · exact hL I hI

theorem harnack_intervalComponents_lower {L : List (ℝ × ℝ)} {ell : ℝ}
    (hL : ∀ I∈L, ell ≤ I.1) :
    ∀ I∈harnackIntervalComponents L, ell ≤ I.1 := by
  induction L with
  | nil => simp [harnackIntervalComponents]
  | cons I L ih =>
    exact harnack_intervalMerge_lower (hL I (List.mem_cons_self))
      (ih (fun J hJ => hL J (List.mem_cons_of_mem _ hJ)))

theorem harnack_intervalMerge_properties {L : List (ℝ × ℝ)} {A B : ℝ}
    (hAB : A < B) (hLower : ∀ I∈L, A ≤ I.1)
    (hProper : ∀ I∈L, I.1 < I.2) (hGap : L.Pairwise (fun I J => I.2 < J.1)) :
    let C := harnackIntervalMerge A B L
    (∀ I∈C, I.1 < I.2) ∧ C.Pairwise (fun I J => I.2 < J.1) ∧
      harnackIntervalUnion C=Ioc A B ∪ harnackIntervalUnion L ∧
      (∃ I∈C, Ioc A B ⊆ Ioc I.1 I.2) ∧
      (∀ I∈L, ∃ J∈C, Ioc I.1 I.2 ⊆ Ioc J.1 J.2) := by
  induction L generalizing B with
  | nil =>
    refine ⟨?_,by simp [harnackIntervalMerge],by simp [harnackIntervalMerge,harnackIntervalUnion],?_,by simp⟩
    · intro I hI
      simp only [harnackIntervalMerge,List.mem_singleton] at hI
      subst I
      exact hAB
    · exact ⟨(A,B),by simp [harnackIntervalMerge],Subset.rfl⟩
  | cons I L ih =>
    rcases I with ⟨D,E⟩
    have hDE := hProper (D,E) List.mem_cons_self
    have hAD := hLower (D,E) List.mem_cons_self
    have hLowerL : ∀ I∈L, A ≤ I.1 := fun I hI => hLower I (List.mem_cons_of_mem _ hI)
    have hProperL : ∀ I∈L, I.1 < I.2 := fun I hI => hProper I (List.mem_cons_of_mem _ hI)
    have hGapL := hGap.tail
    have hHeadGap : ∀ I∈L, E < I.1 := (List.pairwise_cons.mp hGap).1
    by_cases hDB : D ≤ B
    · have hAM : A < max B E := hAB.trans_le (le_max_left _ _)
      obtain ⟨hProp,hGaps,hUnion,hNew,hOld⟩ := ih hAM hLowerL hProperL hGapL
      have hEq : harnackIntervalMerge A B ((D,E)::L)=harnackIntervalMerge A (max B E) L := by
        simp only [harnackIntervalMerge,ite_eq_left hDB]
      rw [hEq]
      refine ⟨hProp,hGaps,?_,?_,?_⟩
      · rw [hUnion,harnackIntervalUnion,← union_assoc]
        have hMerge : Ioc A B ∪ Ioc D E=Ioc A (max B E) := by
          rw [Ioc_union_Ioc' hDB (hAD.trans hDE.le),min_eq_left hAD]
        rw [hMerge]
      · obtain ⟨J,hJ,hContains⟩ := hNew
        exact ⟨J,hJ,(Ioc_subset_Ioc le_rfl (le_max_left B E)).trans hContains⟩
      · intro I hI
        rcases List.mem_cons.mp hI with hI | hI
        · subst I
          obtain ⟨J,hJ,hContains⟩ := hNew
          exact ⟨J,hJ,(Ioc_subset_Ioc hAD (le_max_right B E)).trans hContains⟩
        · exact hOld I hI
    · have hBD : B < D := lt_of_not_ge hDB
      have hEq : harnackIntervalMerge A B ((D,E)::L)=(A,B)::(D,E)::L := by
        simp only [harnackIntervalMerge,ite_eq_right hDB]
      rw [hEq]
      refine ⟨?_,?_,rfl,⟨(A,B),by simp,Subset.rfl⟩,?_⟩
      · intro I hI
        rcases List.mem_cons.mp hI with hI | hI
        · subst I; exact hAB
        · exact hProper I hI
      · rw [List.pairwise_cons]
        refine ⟨?_,hGap⟩
        intro I hI
        rcases List.mem_cons.mp hI with hI | hI
        · subst I; exact hBD
        · exact (hBD.trans hDE).trans (hHeadGap I hI)
      · intro I hI
        exact ⟨I,List.mem_cons_of_mem _ hI,Subset.rfl⟩

theorem harnack_intervalComponents_properties {L : List (ℝ × ℝ)}
    (hProper : ∀ I∈L, I.1 < I.2) (hSorted : L.Pairwise (fun I J => I.1 ≤ J.1)) :
    let C := harnackIntervalComponents L
    (∀ I∈C, I.1 < I.2) ∧ C.Pairwise (fun I J => I.2 < J.1) ∧
      harnackIntervalUnion C=harnackIntervalUnion L ∧
      (∀ I∈L, ∃ J∈C, Ioc I.1 I.2 ⊆ Ioc J.1 J.2) := by
  induction L with
  | nil => simp [harnackIntervalComponents,harnackIntervalUnion]
  | cons I L ih =>
    obtain ⟨hProp,hGap,hUnion,hOld⟩ := ih
      (fun J hJ => hProper J (List.mem_cons_of_mem _ hJ)) hSorted.tail
    have hLower : ∀ J∈harnackIntervalComponents L, I.1 ≤ J.1 :=
      harnack_intervalComponents_lower ((List.pairwise_cons.mp hSorted).1)
    obtain ⟨hProp',hGap',hUnion',hNew',hOld'⟩ :=
      harnack_intervalMerge_properties (hProper I List.mem_cons_self) hLower hProp hGap
    refine ⟨hProp',hGap',?_,?_⟩
    · change harnackIntervalUnion (harnackIntervalMerge I.1 I.2 (harnackIntervalComponents L))=_
      rw [hUnion',hUnion]
      rfl
    · intro J hJ
      rcases List.mem_cons.mp hJ with hJ | hJ
      · subst J; exact hNew'
      · obtain ⟨K,hK,hJK⟩ := hOld J hJ
        obtain ⟨P,hP,hKP⟩ := hOld' K hK
        exact ⟨P,hP,hJK.trans hKP⟩

theorem harnack_interval_components_exist (L : List (ℝ × ℝ))
    (hProper : ∀ I∈L, I.1 < I.2) :
    ∃ C : List (ℝ × ℝ), (∀ I∈C, I.1 < I.2) ∧
      C.Pairwise (fun I J => I.2 < J.1) ∧ harnackIntervalUnion C=harnackIntervalUnion L ∧
      (∀ I∈L, ∃ J∈C, Ioc I.1 I.2 ⊆ Ioc J.1 J.2) := by
  let S := L.mergeSort (fun I J => decide (I.1 ≤ J.1))
  have hPerm : S.Perm L := List.mergeSort_perm _ _
  have hSorted : S.Pairwise (fun I J => I.1 ≤ J.1) := by
    have h := List.pairwise_mergeSort (le := fun I J : ℝ × ℝ => decide (I.1 ≤ J.1))
      (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; exact hab.trans hbc)
      (fun a b => by rcases le_total a.1 b.1 with h | h <;> simp [h]) L
    simpa only [decide_eq_true_eq] using h
  have hPropS : ∀ I∈S, I.1 < I.2 := fun I hI => hProper I (hPerm.mem_iff.mp hI)
  obtain ⟨hProp,hGap,hUnion,hContains⟩ := harnack_intervalComponents_properties hPropS hSorted
  refine ⟨harnackIntervalComponents S,hProp,hGap,?_,?_⟩
  · rw [hUnion]
    ext t
    simp only [harnack_intervalUnion_mem]
    constructor
    · rintro ⟨I,hI,ht⟩
      exact ⟨I,hPerm.mem_iff.mp hI,ht⟩
    · rintro ⟨I,hI,ht⟩
      exact ⟨I,hPerm.mem_iff.mpr hI,ht⟩
  · exact fun I hI => hContains I (hPerm.mem_iff.mpr hI)

def harnackIntervalExpand (m : ℝ) (I : ℝ × ℝ) : ℝ × ℝ :=
  (I.1-(I.2-I.1)/m,I.2)

theorem harnack_original_interval_subset_expansion {m a b A B : ℝ}
    (hm : 0 < m) (hab : a < b)
    (hSub : Ioc b (b+m*(b-a)) ⊆ Ioc A B) :
    Ioc a b ⊆ Ioc (A-(B-A)/m) B := by
  have hForward : b < b+m*(b-a) := by nlinarith
  have hEndpoints := (Ioc_subset_Ioc_iff hForward).mp hSub
  have hRight : b ≤ B := (le_of_lt hForward).trans hEndpoints.1
  have hLeft : A-(B-A)/m ≤ a := by
    have hProd : (A-a)*m ≤ B-A := by nlinarith [hEndpoints.1,hEndpoints.2]
    have hDiv := (le_div_iff₀ hm).mpr hProd
    linarith
  exact Ioc_subset_Ioc hLeft hRight

theorem harnack_intervalUnion_measurable (L : List (ℝ × ℝ)) :
    MeasurableSet (harnackIntervalUnion L) := by
  induction L with
  | nil => exact MeasurableSet.empty
  | cons I L ih => exact measurableSet_Ioc.union ih

theorem harnack_intervalUnion_measure_ne_top (L : List (ℝ × ℝ)) :
    (volume : Measure ℝ) (harnackIntervalUnion L) ≠ ⊤ := by
  induction L with
  | nil => simp [harnackIntervalUnion]
  | cons I L ih =>
    exact measure_union_lt_top (by simp [Real.volume_Ioc]) ih.lt_top |>.ne

theorem harnack_intervalUnion_disjoint_first {A B : ℝ} {L : List (ℝ × ℝ)}
    (hGap : ∀ I∈L, B < I.1) : Disjoint (Ioc A B) (harnackIntervalUnion L) := by
  rw [disjoint_left]
  intro t ht htUnion
  obtain ⟨I,hI,hIt⟩ := harnack_intervalUnion_mem.mp htUnion
  exact not_lt_of_ge ht.2 ((hGap I hI).trans hIt.1)

theorem harnack_intervalUnion_measure_sum {L : List (ℝ × ℝ)}
    (hProper : ∀ I∈L, I.1 < I.2) (hGap : L.Pairwise (fun I J => I.2 < J.1)) :
    ((volume : Measure ℝ) (harnackIntervalUnion L)).toReal=
      (L.map (fun I => I.2-I.1)).sum := by
  induction L with
  | nil => simp [harnackIntervalUnion]
  | cons I L ih =>
    have hP := hProper I List.mem_cons_self
    have hPL : ∀ J∈L, J.1 < J.2 := fun J hJ => hProper J (List.mem_cons_of_mem _ hJ)
    have hDis := harnack_intervalUnion_disjoint_first (A := I.1) (List.pairwise_cons.mp hGap).1
    have hEq := measureReal_union (μ := (volume : Measure ℝ)) hDis
      (harnack_intervalUnion_measurable L) (by simp [Real.volume_Ioc])
      (harnack_intervalUnion_measure_ne_top L)
    change ((volume : Measure ℝ) (harnackIntervalUnion (I::L))).toReal=_
    change ((volume : Measure ℝ) (Ioc I.1 I.2 ∪ harnackIntervalUnion L)).toReal=_ at hEq
    change ((volume : Measure ℝ) (Ioc I.1 I.2 ∪ harnackIntervalUnion L)).toReal=_
    rw [hEq]
    change ((volume : Measure ℝ) (Ioc I.1 I.2)).toReal+
      ((volume : Measure ℝ) (harnackIntervalUnion L)).toReal=_
    rw [Real.volume_Ioc,ENNReal.toReal_ofReal (sub_nonneg.mpr hP.le),ih hPL hGap.tail]
    rfl

theorem harnack_intervalUnion_measure_le_sum {L : List (ℝ × ℝ)}
    (hProper : ∀ I∈L, I.1 < I.2) :
    ((volume : Measure ℝ) (harnackIntervalUnion L)).toReal ≤
      (L.map (fun I => I.2-I.1)).sum := by
  induction L with
  | nil => simp [harnackIntervalUnion]
  | cons I L ih =>
    have hP := hProper I List.mem_cons_self
    have hPL : ∀ J∈L, J.1 < J.2 := fun J hJ => hProper J (List.mem_cons_of_mem _ hJ)
    have h := measureReal_union_le (μ := (volume : Measure ℝ)) (Ioc I.1 I.2) (harnackIntervalUnion L)
    change ((volume : Measure ℝ) (harnackIntervalUnion (I::L))).toReal ≤ _
    calc
      _ ≤ ((volume : Measure ℝ) (Ioc I.1 I.2)).toReal+
          ((volume : Measure ℝ) (harnackIntervalUnion L)).toReal := h
      _ ≤ _ := by
        rw [Real.volume_Ioc,ENNReal.toReal_ofReal (sub_nonneg.mpr hP.le)]
        simpa only [List.map_cons,List.sum_cons,add_comm] using add_le_add_left (ih hPL) (I.2-I.1)

def harnackForwardInterval (m : ℝ) (I : ℝ × ℝ) : ℝ × ℝ :=
  (I.2,I.2+m*(I.2-I.1))

theorem harnack_forward_interval_measure_finite {m : ℝ} (hm : 0 < m)
    (L : List (ℝ × ℝ)) (hProper : ∀ I∈L, I.1 < I.2) :
    ((volume : Measure ℝ) (harnackIntervalUnion L)).toReal ≤
      (1+1/m)*((volume : Measure ℝ) (harnackIntervalUnion (L.map (harnackForwardInterval m)))).toReal := by
  have hFProper : ∀ I∈L.map (harnackForwardInterval m), I.1 < I.2 := by
    intro I hI
    obtain ⟨J,hJ,rfl⟩ := List.mem_map.mp hI
    have hJProper := hProper J hJ
    change J.2 < J.2+m*(J.2-J.1)
    nlinarith
  obtain ⟨C,hCProper,hCGap,hCUnion,hCContains⟩ :=
    harnack_interval_components_exist (L.map (harnackForwardInterval m)) hFProper
  have hExpandProper : ∀ I∈C.map (harnackIntervalExpand m), I.1 < I.2 := by
    intro I hI
    obtain ⟨J,hJ,rfl⟩ := List.mem_map.mp hI
    have hJProper := hCProper J hJ
    have hDiv := div_pos (sub_pos.mpr hJProper) hm
    change J.1-(J.2-J.1)/m < J.2
    linarith
  have hSubset : harnackIntervalUnion L ⊆ harnackIntervalUnion (C.map (harnackIntervalExpand m)) := by
    intro t ht
    obtain ⟨I,hI,hIt⟩ := harnack_intervalUnion_mem.mp ht
    obtain ⟨J,hJ,hSub⟩ := hCContains (harnackForwardInterval m I) (List.mem_map_of_mem hI)
    have hExpanded := harnack_original_interval_subset_expansion hm (hProper I hI) hSub
    exact harnack_intervalUnion_mem.mpr
      ⟨harnackIntervalExpand m J,List.mem_map_of_mem hJ,hExpanded hIt⟩
  have hSumAll : ∀ D : List (ℝ × ℝ),
      ((D.map (harnackIntervalExpand m)).map (fun I => I.2-I.1)).sum=
      (1+1/m)*(D.map (fun I => I.2-I.1)).sum := by
    intro D
    induction D with
    | nil => simp
    | cons I D ih =>
      simp only [List.map_cons,List.sum_cons,ih,harnackIntervalExpand]
      ring
  have hSum := hSumAll C
  calc
    _ ≤ ((volume : Measure ℝ) (harnackIntervalUnion (C.map (harnackIntervalExpand m)))).toReal :=
      ENNReal.toReal_mono (harnack_intervalUnion_measure_ne_top _) (measure_mono hSubset)
    _ ≤ ((C.map (harnackIntervalExpand m)).map (fun I => I.2-I.1)).sum :=
      harnack_intervalUnion_measure_le_sum hExpandProper
    _ = (1+1/m)*((volume : Measure ℝ) (harnackIntervalUnion C)).toReal := by
      rw [hSum,harnack_intervalUnion_measure_sum hCProper hCGap]
    _ = _ := by rw [hCUnion]

theorem harnack_intervalUnion_map {ι : Type*} (L : List ι) (f : ι → ℝ × ℝ) :
    harnackIntervalUnion (L.map f)=⋃ i∈L, Ioc (f i).1 (f i).2 := by
  ext t
  simp only [harnack_intervalUnion_mem,List.mem_map,mem_iUnion]
  aesop

theorem harnack_forward_interval_measure_finset {ι : Type*} {m : ℝ} (hm : 0 < m)
    (s : Finset ι) (a b : ι → ℝ) (hab : ∀ i∈s, a i < b i) :
    (volume : Measure ℝ) (⋃ i∈s, Ioc (a i) (b i)) ≤
      ENNReal.ofReal (1+1/m)*(volume : Measure ℝ) (⋃ i∈s, Ioc (b i) (b i+m*(b i-a i))) := by
  classical
  let L := s.toList.map (fun i => (a i,b i))
  have hProper : ∀ I∈L, I.1 < I.2 := by
    intro I hI
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hI
    exact hab i (Finset.mem_toList.mp hi)
  have h := ENNReal.ofReal_le_ofReal (harnack_forward_interval_measure_finite hm L hProper)
  rw [ENNReal.ofReal_toReal (harnack_intervalUnion_measure_ne_top L),
    ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1+1/m),
    ENNReal.ofReal_toReal (harnack_intervalUnion_measure_ne_top _)] at h
  have hFirst : harnackIntervalUnion L=⋃ i∈s, Ioc (a i) (b i) := by
    simp only [L,harnack_intervalUnion_map,Finset.mem_toList]
  have hSecond : harnackIntervalUnion (L.map (harnackForwardInterval m))=
      ⋃ i∈s, Ioc (b i) (b i+m*(b i-a i)) := by
    simp only [L,List.map_map,Function.comp_def,harnackForwardInterval,
      harnack_intervalUnion_map,Finset.mem_toList]
  rwa [hFirst,hSecond] at h

theorem harnack_forward_interval_measure_countable {m : ℝ} (hm : 0 < m)
    (p : ℕ → Prop) (a b : ℕ → ℝ) (hab : ∀ i, a i < b i) :
    (volume : Measure ℝ) (⋃ i, ⋃ (_ : p i), Ioc (a i) (b i)) ≤
      ENNReal.ofReal (1+1/m)*(volume : Measure ℝ)
        (⋃ i, ⋃ (_ : p i), Ioc (b i) (b i+m*(b i-a i))) := by
  classical
  let E : ℕ → Set ℝ := fun N => ⋃ i∈(Finset.range N).filter p, Ioc (a i) (b i)
  have hMono : Monotone E := by
    intro N M hNM t ht
    obtain ⟨i,hi,hIt⟩ := mem_iUnion₂.mp ht
    have hMember := Finset.mem_filter.mp hi
    exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ((Finset.mem_range.mp hMember.1).trans_le hNM),hMember.2⟩,hIt⟩⟩
  have hUnion : (⋃ N, E N)=⋃ i, ⋃ (_ : p i), Ioc (a i) (b i) := by
    ext t
    simp only [E,mem_iUnion]
    constructor
    · rintro ⟨N,i,hi,hIt⟩
      have hp := (Finset.mem_filter.mp hi).2
      exact ⟨i,hp,hIt⟩
    · rintro ⟨i,hp,hIt⟩
      exact ⟨i+1,i,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hp⟩,hIt⟩
  rw [← hUnion,hMono.measure_iUnion]
  apply iSup_le
  intro N
  have hN := harnack_forward_interval_measure_finset hm ((Finset.range N).filter p) a b
    (fun i _ => hab i)
  have hSubset : (⋃ i∈(Finset.range N).filter p, Ioc (b i) (b i+m*(b i-a i))) ⊆
      (⋃ i, ⋃ (_ : p i), Ioc (b i) (b i+m*(b i-a i))) := by
    intro t ht
    obtain ⟨i,hi,hIt⟩ := mem_iUnion₂.mp ht
    have hp := (Finset.mem_filter.mp hi).2
    exact mem_iUnion₂.mpr ⟨i,hp,hIt⟩
  exact hN.trans (mul_le_mul_of_nonneg_left (measure_mono hSubset) (zero_le : (0 : ENNReal) ≤ ENNReal.ofReal (1+1/m)))


theorem harnack_forward_stack_measure
    {n : ℕ} {m : ℝ} (hm : 0 < m)
    (S : ℕ → Set (Space n)) (a b : ℕ → ℝ)
    (hS : ∀ i, MeasurableSet (S i)) (hab : ∀ i, a i < b i) :
    (volume : Measure (Point n)) (⋃ i, S i ×ˢ Ioc (a i) (b i)) ≤
      ENNReal.ofReal (1+1/m)*(volume : Measure (Point n))
        (⋃ i, S i ×ˢ Ioc (b i) (b i+m*(b i-a i))) := by
  have hE : MeasurableSet (⋃ i, S i ×ˢ Ioc (a i) (b i)) :=
    MeasurableSet.iUnion (fun i => (hS i).prod measurableSet_Ioc)
  have hF : MeasurableSet (⋃ i, S i ×ˢ Ioc (b i) (b i+m*(b i-a i))) :=
    MeasurableSet.iUnion (fun i => (hS i).prod measurableSet_Ioc)
  have hSlice (x : Space n) :
      Prod.mk x ⁻¹' (⋃ i, S i ×ˢ Ioc (a i) (b i))=
        ⋃ i, ⋃ (_ : x∈S i), Ioc (a i) (b i) := by
    ext t
    simp only [mem_preimage,mem_iUnion,mem_prod]
    aesop
  have hForwardSlice (x : Space n) :
      Prod.mk x ⁻¹' (⋃ i, S i ×ˢ Ioc (b i) (b i+m*(b i-a i)))=
        ⋃ i, ⋃ (_ : x∈S i), Ioc (b i) (b i+m*(b i-a i)) := by
    ext t
    simp only [mem_preimage,mem_iUnion,mem_prod]
    aesop
  rw [Measure.volume_eq_prod,Measure.prod_apply hE,Measure.prod_apply hF]
  calc
    _ ≤ ∫⁻ x : Space n, ENNReal.ofReal (1+1/m)*(volume : Measure ℝ)
        (Prod.mk x ⁻¹' (⋃ i, S i ×ˢ Ioc (b i) (b i+m*(b i-a i)))) := by
      apply lintegral_mono
      intro x
      change (volume : Measure ℝ) (Prod.mk x ⁻¹' (⋃ i, S i ×ˢ Ioc (a i) (b i))) ≤
        ENNReal.ofReal (1+1/m)*(volume : Measure ℝ)
          (Prod.mk x ⁻¹' (⋃ i, S i ×ˢ Ioc (b i) (b i+m*(b i-a i))))
      rw [hSlice,hForwardSlice]
      exact harnack_forward_interval_measure_countable hm (fun i => x∈S i) a b hab
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem harnack_parent_stack_measure_transfer
    {n : ℕ} {m q : ℝ} (hm : 0 < m) (hq : 0 ≤ q)
    (S : ℕ → Set (Space n)) (a b : ℕ → ℝ)
    (hS : ∀ i, MeasurableSet (S i)) (hab : ∀ i, a i < b i)
    {A B : Set (Point n)} (hA : MeasurableSet A)
    (hPair : Pairwise (fun i j => Disjoint (S i ×ˢ Ioc (a i) (b i)) (S j ×ˢ Ioc (a j) (b j))))
    (hCover : A ⊆ ⋃ i, S i ×ˢ Ioc (a i) (b i))
    (hDensity : ∀ i, (volume : Measure (Point n)) (A ∩ (S i ×ˢ Ioc (a i) (b i))) ≤
      ENNReal.ofReal q*(volume : Measure (Point n)) (S i ×ˢ Ioc (a i) (b i)))
    (hForward : (⋃ i, S i ×ˢ Ioc (b i) (b i+m*(b i-a i))) ⊆ B) :
    (volume : Measure (Point n)) A ≤ ENNReal.ofReal (q*(1+1/m))*(volume : Measure (Point n)) B := by
  let P := fun i => S i ×ˢ Ioc (a i) (b i)
  have hPMeas (i : ℕ) : MeasurableSet (P i) := (hS i).prod measurableSet_Ioc
  have hPairInter : Pairwise (fun i j => Disjoint (A ∩ P i) (A ∩ P j)) :=
    fun i j hij => (hPair hij).mono inter_subset_right inter_subset_right
  have hAeq : (⋃ i, A ∩ P i)=A := by
    ext p
    constructor
    · intro hp
      obtain ⟨i,hp⟩ := mem_iUnion.mp hp
      exact hp.1
    · intro hp
      obtain ⟨i,hi⟩ := mem_iUnion.mp (hCover hp)
      exact mem_iUnion.mpr ⟨i,hp,hi⟩
  have hMeasureA : (volume : Measure (Point n)) A=
      ∑' i, (volume : Measure (Point n)) (A ∩ P i) := by
    conv_lhs => rw [← hAeq]
    exact measure_iUnion hPairInter (fun i => hA.inter (hPMeas i))
  have hMeasureP : (volume : Measure (Point n)) (⋃ i, P i)=
      ∑' i, (volume : Measure (Point n)) (P i) := measure_iUnion hPair hPMeas
  have hStack := harnack_forward_stack_measure hm S a b hS hab
  have hSub : (volume : Measure (Point n)) (⋃ i, S i ×ˢ Ioc (b i) (b i+m*(b i-a i))) ≤
      (volume : Measure (Point n)) B := measure_mono hForward
  calc
    _ = ∑' i, (volume : Measure (Point n)) (A ∩ P i) := hMeasureA
    _ ≤ ∑' i, ENNReal.ofReal q*(volume : Measure (Point n)) (P i) := ENNReal.tsum_le_tsum hDensity
    _ = ENNReal.ofReal q*(volume : Measure (Point n)) (⋃ i, P i) := by
      rw [ENNReal.tsum_mul_left,hMeasureP]
    _ ≤ ENNReal.ofReal q*(ENNReal.ofReal (1+1/m)*
        (volume : Measure (Point n)) (⋃ i, S i ×ˢ Ioc (b i) (b i+m*(b i-a i)))) :=
      mul_le_mul_of_nonneg_left hStack zero_le
    _ ≤ ENNReal.ofReal q*(ENNReal.ofReal (1+1/m)*(volume : Measure (Point n)) B) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hSub zero_le) zero_le
    _ = _ := by rw [← mul_assoc,← ENNReal.ofReal_mul hq]

end Yau.LeafProofs.L05Aux










