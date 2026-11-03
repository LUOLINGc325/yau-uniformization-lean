import Yau.LeafProofs.L16TimeTransport

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

def timePaste {n : ℕ} {V : Type*} (τ : ℝ) (u v : Point n → V) (p : Point n) : V :=
  if p.2 ≤ τ then u p else v p

theorem timePaste_eqOn_left {n : ℕ} {V : Type*} {τ : ℝ} (u v : Point n → V) :
    Set.EqOn (timePaste τ u v) u (cylinder Set.univ 0 τ) := by
  intro p hp
  simp [timePaste,hp.2.2]

theorem timePaste_eqOn_right {n : ℕ} {V : Type*} {τ T : ℝ} {u v : Point n → V}
    (hTrace : ∀ x, u (x,τ) = v (x,τ)) :
    Set.EqOn (timePaste τ u v) v (cylinder Set.univ τ T) := by
  intro p hp
  by_cases h : p.2 ≤ τ
  · have ht : p.2 = τ := le_antisymm h hp.2.1
    simpa [timePaste,h,← ht] using hTrace p.1
  · simp [timePaste,h]

private theorem timePaste_union {n : ℕ} {τ T : ℝ} (hτ : 0 ≤ τ) (hT : τ ≤ T) :
    cylinder (n := n) Set.univ 0 τ ∪ cylinder Set.univ τ T = cylinder Set.univ 0 T := by
  ext p
  simp only [Set.mem_union,Yau.Parabolic.cylinder,Set.mem_prod,Set.mem_univ,true_and,Set.mem_Icc]
  constructor
  · rintro (h | h) <;> constructor <;> linarith [h.1,h.2]
  · intro h
    by_cases ht : p.2 ≤ τ
    · exact Or.inl ⟨h.1,ht⟩
    · exact Or.inr ⟨le_of_not_ge ht,h.2⟩

theorem continuousOn_timePaste {n : ℕ} {V : Type*} [TopologicalSpace V]
    {τ T : ℝ} (hτ : 0 ≤ τ) (hT : τ ≤ T) {u v : Point n → V}
    (hu : ContinuousOn u (cylinder Set.univ 0 τ))
    (hv : ContinuousOn v (cylinder Set.univ τ T))
    (hTrace : ∀ x, u (x,τ) = v (x,τ)) :
    ContinuousOn (timePaste τ u v) (cylinder Set.univ 0 T) := by
  rw [← timePaste_union hτ hT]
  exact (hu.congr (timePaste_eqOn_left u v)).union_of_isClosed
    (hv.congr (timePaste_eqOn_right hTrace))
    (isClosed_univ.prod isClosed_Icc) (isClosed_univ.prod isClosed_Icc)

theorem spatialD_timePaste {n : ℕ} (τ : ℝ) (u v : Point n → ℝ) :
    spatialD (timePaste τ u v) = timePaste τ (spatialD u) (spatialD v) := by
  funext p
  by_cases h : p.2 ≤ τ <;> simp [spatialD,timePaste,h]

theorem spatialDD_timePaste {n : ℕ} (τ : ℝ) (u v : Point n → ℝ) :
    spatialDD (timePaste τ u v) = timePaste τ (spatialDD u) (spatialDD v) := by
  funext p
  by_cases h : p.2 ≤ τ <;> simp [spatialDD,timePaste,h]

private theorem timePaste_spatial_trace {n : ℕ} {τ : ℝ} {u v : Point n → ℝ}
    (hTrace : ∀ x, u (x,τ) = v (x,τ)) :
    (∀ x, spatialD u (x,τ) = spatialD v (x,τ)) ∧
    (∀ x, spatialDD u (x,τ) = spatialDD v (x,τ)) := by
  have h : (fun x => u (x,τ)) = (fun x => v (x,τ)) := funext hTrace
  constructor
  · intro x; simp only [spatialD,h]
  · intro x; simp only [spatialDD,h]

private theorem timePaste_hasDerivWithinAt {n : ℕ} {τ T : ℝ} (hτ : 0 < τ) (hT : τ < T)
    {u v : Point n → ℝ} (hu : C2 (cylinder Set.univ 0 τ) u)
    (hv : C2 (cylinder Set.univ τ T) v) (hTrace : ∀ x, u (x,τ) = v (x,τ))
    (htTrace : ∀ x, timeD (cylinder Set.univ 0 τ) u (x,τ) =
      timeD (cylinder Set.univ τ T) v (x,τ)) {p : Point n}
    (hp : p ∈ cylinder Set.univ 0 T) :
    HasDerivWithinAt (fun t => timePaste τ u v (p.1,t))
      (timePaste τ (timeD (cylinder Set.univ 0 τ) u)
        (timeD (cylinder Set.univ τ T) v) p) (Set.Icc 0 T) p.2 := by
  have hU {s : ℝ} (hs : s ∈ Set.Icc 0 τ) :
      HasDerivWithinAt (fun t => timePaste τ u v (p.1,t))
        (timeD (cylinder Set.univ 0 τ) u (p.1,s)) (Set.Icc 0 τ) s := by
    have h := (hu.2.2.2.2.2 (p.1,s) ⟨Set.mem_univ _,hs⟩).hasDerivWithinAt
    simp only [timeD,Yau.Parabolic.cylinder,Set.mem_ofPred_eq,Set.mem_prod,
      Set.mem_univ,true_and,Set.ofPred_mem_eq] at h ⊢
    exact h.congr_of_mem (fun t ht => timePaste_eqOn_left u v (x := (p.1,t)) ⟨Set.mem_univ _,ht⟩) hs
  have hV {s : ℝ} (hs : s ∈ Set.Icc τ T) :
      HasDerivWithinAt (fun t => timePaste τ u v (p.1,t))
        (timeD (cylinder Set.univ τ T) v (p.1,s)) (Set.Icc τ T) s := by
    have h := (hv.2.2.2.2.2 (p.1,s) ⟨Set.mem_univ _,hs⟩).hasDerivWithinAt
    simp only [timeD,Yau.Parabolic.cylinder,Set.mem_ofPred_eq,Set.mem_prod,
      Set.mem_univ,true_and,Set.ofPred_mem_eq] at h ⊢
    exact h.congr_of_mem (fun t ht => timePaste_eqOn_right hTrace (x := (p.1,t)) ⟨Set.mem_univ _,ht⟩) hs
  rcases lt_trichotomy p.2 τ with h | h | h
  · have hs : Set.Icc (0 : ℝ) τ ∈ 𝓝[Set.Icc 0 T] p.2 := by
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds h)] with t ht htτ
      exact ⟨ht.1,le_of_lt htτ⟩
    simpa [timePaste,le_of_lt h] using (hU ⟨hp.2.1,le_of_lt h⟩).mono_of_mem_nhdsWithin hs
  · have hh := (hU ⟨hτ.le,le_rfl⟩).union ((hV ⟨le_rfl,hT.le⟩).congr_deriv (htTrace p.1).symm)
    have hi : Set.Icc (0 : ℝ) τ ∪ Set.Icc τ T = Set.Icc 0 T := by
      ext t; simp only [Set.mem_union,Set.mem_Icc]; constructor
      · rintro (ht | ht) <;> constructor <;> linarith [ht.1,ht.2]
      · intro ht; by_cases hh : t ≤ τ
        · exact Or.inl ⟨ht.1,hh⟩
        · exact Or.inr ⟨le_of_not_ge hh,ht.2⟩
    have hpeta : p = (p.1,τ) := Prod.ext rfl h
    rw [hpeta]
    simpa [timePaste,hi] using hh
  · have hs : Set.Icc τ T ∈ 𝓝[Set.Icc 0 T] p.2 := by
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds h)] with t ht htτ
      exact ⟨le_of_lt htτ,ht.2⟩
    simpa [timePaste,not_le_of_gt h] using (hV ⟨le_of_lt h,hp.2.2⟩).mono_of_mem_nhdsWithin hs

theorem timeD_timePaste {n : ℕ} {τ T : ℝ} (hτ : 0 < τ) (hT : τ < T)
    {u v : Point n → ℝ} (hu : C2 (cylinder Set.univ 0 τ) u)
    (hv : C2 (cylinder Set.univ τ T) v) (hTrace : ∀ x, u (x,τ) = v (x,τ))
    (htTrace : ∀ x, timeD (cylinder Set.univ 0 τ) u (x,τ) =
      timeD (cylinder Set.univ τ T) v (x,τ)) {p : Point n}
    (hp : p ∈ cylinder Set.univ 0 T) :
    timeD (cylinder Set.univ 0 T) (timePaste τ u v) p =
      timePaste τ (timeD (cylinder Set.univ 0 τ) u) (timeD (cylinder Set.univ τ T) v) p := by
  have h := (timePaste_hasDerivWithinAt hτ hT hu hv hTrace htTrace hp).derivWithin
    (uniqueDiffOn_Icc (hτ.trans hT) _ hp.2)
  simpa only [timeD,Yau.Parabolic.cylinder,Set.mem_ofPred_eq,Set.mem_prod,
    Set.mem_univ,true_and,Set.ofPred_mem_eq] using h

theorem c2_timePaste {n : ℕ} {τ T : ℝ} (hτ : 0 < τ) (hT : τ < T)
    {u v : Point n → ℝ} (hu : C2 (cylinder Set.univ 0 τ) u)
    (hv : C2 (cylinder Set.univ τ T) v) (hTrace : ∀ x, u (x,τ) = v (x,τ))
    (htTrace : ∀ x, timeD (cylinder Set.univ 0 τ) u (x,τ) =
      timeD (cylinder Set.univ τ T) v (x,τ)) :
    C2 (cylinder Set.univ 0 T) (timePaste τ u v) := by
  have hJets := timePaste_spatial_trace hTrace
  refine ⟨continuousOn_timePaste hτ.le hT.le hu.1 hv.1 hTrace,?_,?_,?_,?_,?_⟩
  · rw [spatialD_timePaste]
    exact continuousOn_timePaste hτ.le hT.le hu.2.1 hv.2.1 hJets.1
  · rw [spatialDD_timePaste]
    exact continuousOn_timePaste hτ.le hT.le hu.2.2.1 hv.2.2.1 hJets.2
  · exact (continuousOn_timePaste hτ.le hT.le hu.2.2.2.1 hv.2.2.2.1 htTrace).congr
      (fun p hp => timeD_timePaste hτ hT hu hv hTrace htTrace hp)
  · intro p hp
    by_cases h : p.2 ≤ τ
    · simpa only [timePaste,ite_eq_left h] using hu.2.2.2.2.1 p ⟨Set.mem_univ _,hp.2.1,h⟩
    · simpa only [timePaste,ite_eq_right h] using hv.2.2.2.2.1 p ⟨Set.mem_univ _,le_of_not_ge h,hp.2.2⟩
  · intro p hp
    have h := (timePaste_hasDerivWithinAt hτ hT hu hv hTrace htTrace hp).differentiableWithinAt
    simpa only [Yau.Parabolic.cylinder,Set.mem_ofPred_eq,Set.mem_prod,
      Set.mem_univ,true_and,Set.ofPred_mem_eq] using h

theorem linearOp_timePaste {n : ℕ} {τ T : ℝ} (hτ : 0 < τ) (hT : τ < T)
    {u v : Point n → ℝ} (hu : C2 (cylinder Set.univ 0 τ) u)
    (hv : C2 (cylinder Set.univ τ T) v) (hTrace : ∀ x, u (x,τ) = v (x,τ))
    (htTrace : ∀ x, timeD (cylinder Set.univ 0 τ) u (x,τ) =
      timeD (cylinder Set.univ τ T) v (x,τ))
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
    {p : Point n} (hp : p ∈ cylinder Set.univ 0 T) :
    linearOp (cylinder Set.univ 0 T) a b (timePaste τ u v) p =
      timePaste τ (linearOp (cylinder Set.univ 0 τ) a b u)
        (linearOp (cylinder Set.univ τ T) a b v) p := by
  simp only [linearOp,timeD_timePaste hτ hT hu hv hTrace htTrace hp,
    spatialD_timePaste,spatialDD_timePaste]
  by_cases h : p.2 ≤ τ <;> simp [timePaste,h,linearOp]

theorem equation_timePaste {n : ℕ} {τ T : ℝ} (hτ : 0 < τ) (hT : τ < T)
    {u v f : Point n → ℝ} (hu : C2 (cylinder Set.univ 0 τ) u)
    (hv : C2 (cylinder Set.univ τ T) v) (hTrace : ∀ x, u (x,τ) = v (x,τ))
    (htTrace : ∀ x, timeD (cylinder Set.univ 0 τ) u (x,τ) =
      timeD (cylinder Set.univ τ T) v (x,τ))
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (huEq : ∀ p ∈ cylinder Set.univ 0 τ, linearOp (cylinder Set.univ 0 τ) a b u p = f p)
    (hvEq : ∀ p ∈ cylinder Set.univ τ T, linearOp (cylinder Set.univ τ T) a b v p = f p) :
    ∀ p ∈ cylinder Set.univ 0 T, linearOp (cylinder Set.univ 0 T) a b (timePaste τ u v) p = f p := by
  intro p hp
  rw [linearOp_timePaste hτ hT hu hv hTrace htTrace a b hp]
  by_cases h : p.2 ≤ τ
  · simpa [timePaste,h] using huEq p ⟨Set.mem_univ _,hp.2.1,h⟩
  · simpa [timePaste,h] using hvEq p ⟨Set.mem_univ _,le_of_not_ge h,hp.2.2⟩

private theorem timePaste_weight_symm {n : ℕ} (α : ℝ) (p q : Point n) :
    holderWeight α p q = holderWeight α q p := by
  simp only [holderWeight,norm_sub_rev,abs_sub_comm]

theorem holderBound_timePaste {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    {α C D τ T : ℝ} (hα : 0 < α) {u v : Point n → V}
    (hu : HolderBound α (cylinder Set.univ 0 τ) u C)
    (hv : HolderBound α (cylinder Set.univ τ T) v D)
    (hTrace : ∀ x, u (x,τ) = v (x,τ)) :
    HolderBound α (cylinder Set.univ 0 T) (timePaste τ u v) (2*(C+D)) := by
  have hC : C ≤ 2*(C+D) := by linarith [hu.1,hv.1]
  have hD : D ≤ 2*(C+D) := by linarith [hu.1,hv.1]
  have hw (p q : Point n) : 0 ≤ holderWeight α p q := by dsimp [holderWeight]; positivity
  have hCross (p q : Point n) (hp : p ∈ cylinder Set.univ 0 τ)
      (hq : q ∈ cylinder Set.univ τ T) :
      ‖u p-v q‖ ≤ 2*(C+D)*holderWeight α p q := by
    let z : Point n := (p.1,τ)
    have hzU : z ∈ cylinder Set.univ 0 τ := ⟨Set.mem_univ _,hp.2.1.trans hp.2.2,le_rfl⟩
    have hzV : z ∈ cylinder Set.univ τ T := ⟨Set.mem_univ _,le_rfl,hq.2.1.trans hq.2.2⟩
    have habs1 : |p.2-τ| ≤ |p.2-q.2| := by
      rw [abs_of_nonpos (by linarith [hp.2.2]),abs_of_nonpos (by linarith [hp.2.2,hq.2.1])]
      linarith [hq.2.1]
    have habs2 : |τ-q.2| ≤ |p.2-q.2| := by
      rw [abs_of_nonpos (by linarith [hq.2.1]),abs_of_nonpos (by linarith [hp.2.2,hq.2.1])]
      linarith [hp.2.2]
    have hw1 : holderWeight α p z ≤ holderWeight α p q := by
      simp only [holderWeight,z,Prod.fst,Prod.snd,sub_self,norm_zero,Real.zero_rpow (ne_of_gt hα),zero_add]
      exact (Real.rpow_le_rpow (abs_nonneg _) habs1 (by positivity)).trans
        (le_add_of_nonneg_left (by positivity))
    have hw2 : holderWeight α z q ≤ holderWeight α p q := by
      exact add_le_add le_rfl (Real.rpow_le_rpow (abs_nonneg _) habs2 (by positivity))
    calc
      ‖u p-v q‖ ≤ ‖u p-u z‖+‖u z-v q‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = ‖u p-u z‖+‖v z-v q‖ := by rw [show u z = v z from hTrace p.1]
      _ ≤ C*holderWeight α p z+D*holderWeight α z q := add_le_add (hu.2.2 p hp z hzU) (hv.2.2 z hzV q hq)
      _ ≤ C*holderWeight α p q+D*holderWeight α p q :=
        add_le_add (mul_le_mul_of_nonneg_left hw1 hu.1) (mul_le_mul_of_nonneg_left hw2 hv.1)
      _ ≤ 2*(C+D)*holderWeight α p q := by nlinarith [mul_nonneg (add_nonneg hu.1 hv.1) (hw p q)]
  refine ⟨by linarith [hu.1,hv.1],?_,?_⟩
  · intro p hp
    by_cases h : p.2 ≤ τ
    · simpa [timePaste,h] using (hu.2.1 p ⟨Set.mem_univ _,hp.2.1,h⟩).trans hC
    · simpa [timePaste,h] using (hv.2.1 p ⟨Set.mem_univ _,le_of_not_ge h,hp.2.2⟩).trans hD
  · intro p hp q hq
    by_cases h : p.2 ≤ τ <;> by_cases h' : q.2 ≤ τ
    · simpa [timePaste,h,h'] using (hu.2.2 p ⟨Set.mem_univ _,hp.2.1,h⟩ q ⟨Set.mem_univ _,hq.2.1,h'⟩).trans
        (mul_le_mul_of_nonneg_right hC (hw p q))
    · simpa [timePaste,h,h'] using hCross p q ⟨Set.mem_univ _,hp.2.1,h⟩ ⟨Set.mem_univ _,le_of_not_ge h',hq.2.2⟩
    · simpa [timePaste,h,h',norm_sub_rev,timePaste_weight_symm α q p] using
        hCross q p ⟨Set.mem_univ _,hq.2.1,h'⟩ ⟨Set.mem_univ _,le_of_not_ge h,hp.2.2⟩
    · simpa [timePaste,h,h'] using (hv.2.2 p ⟨Set.mem_univ _,le_of_not_ge h,hp.2.2⟩ q ⟨Set.mem_univ _,le_of_not_ge h',hq.2.2⟩).trans
        (mul_le_mul_of_nonneg_right hD (hw p q))

theorem schauderBound_timePaste {n : ℕ} {α C D τ T : ℝ}
    (hα : 0 < α) (hτ : 0 < τ) (hT : τ < T) {u v : Point n → ℝ}
    (hu : SchauderBound α (cylinder Set.univ 0 τ) u C)
    (hv : SchauderBound α (cylinder Set.univ τ T) v D)
    (hTrace : ∀ x, u (x,τ) = v (x,τ))
    (htTrace : ∀ x, timeD (cylinder Set.univ 0 τ) u (x,τ) =
      timeD (cylinder Set.univ τ T) v (x,τ)) :
    SchauderBound α (cylinder Set.univ 0 T) (timePaste τ u v) (2*(C+D)) := by
  letI : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
  letI : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
  letI : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
  have hJets := timePaste_spatial_trace hTrace
  refine ⟨c2_timePaste hτ hT hu.1 hv.1 hTrace htTrace,by linarith [hu.2.1,hv.2.1],?_,?_,?_⟩
  · intro p hp
    by_cases h : p.2 ≤ τ
    · have hB := hu.2.2.1 p ⟨Set.mem_univ _,hp.2.1,h⟩
      rw [spatialD_timePaste]
      simp only [timePaste,ite_eq_left h]
      constructor <;> linarith [hB.1,hB.2,hu.2.1,hv.2.1]
    · have hB := hv.2.2.1 p ⟨Set.mem_univ _,le_of_not_ge h,hp.2.2⟩
      rw [spatialD_timePaste]
      simp only [timePaste,ite_eq_right h]
      constructor <;> linarith [hB.1,hB.2,hu.2.1,hv.2.1]
  · rw [spatialDD_timePaste]
    exact holderBound_timePaste hα hu.2.2.2.1 hv.2.2.2.1 hJets.2
  · exact holderBound_congr_on (holderBound_timePaste hα hu.2.2.2.2 hv.2.2.2.2 htTrace)
      (fun p hp => (timeD_timePaste hτ hT hu.1 hv.1 hTrace htTrace hp).symm)

theorem lowPair_holderBound_timePaste {n : ℕ} {α C D τ T : ℝ}
    (hα : 0 < α) {u v : Point n → ℝ}
    (hu : HolderBound α (cylinder Set.univ 0 τ) (fun p => (u p,spatialD u p)) C)
    (hv : HolderBound α (cylinder Set.univ τ T) (fun p => (v p,spatialD v p)) D)
    (hTrace : ∀ x, u (x,τ) = v (x,τ)) :
    HolderBound α (cylinder Set.univ 0 T)
      (fun p => (timePaste τ u v p,spatialD (timePaste τ u v) p)) (2*(C+D)) := by
  letI : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
  have hJets := timePaste_spatial_trace hTrace
  apply holderBound_congr_on (holderBound_timePaste hα hu hv
    (fun x => Prod.ext (hTrace x) (hJets.1 x)))
  intro p hp
  rw [spatialD_timePaste]
  by_cases h : p.2 ≤ τ <;> simp [timePaste,h]

/-- Adjacent solutions with matching actual value and time-derivative traces glue
with a finite common budget for the Schauder and low spatial jet bounds. -/
theorem timePaste_solution {n : ℕ} {α C D τ T : ℝ}
    (hα : 0 < α) (hτ : 0 < τ) (hT : τ < T)
    {u v f : Point n → ℝ} {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (hu : SchauderBound α (cylinder Set.univ 0 τ) u C)
    (hv : SchauderBound α (cylinder Set.univ τ T) v D)
    (huLow : HolderBound α (cylinder Set.univ 0 τ) (fun p => (u p,spatialD u p)) C)
    (hvLow : HolderBound α (cylinder Set.univ τ T) (fun p => (v p,spatialD v p)) D)
    (hTrace : ∀ x, u (x,τ) = v (x,τ))
    (htTrace : ∀ x, timeD (cylinder Set.univ 0 τ) u (x,τ) =
      timeD (cylinder Set.univ τ T) v (x,τ))
    (huEq : ∀ p ∈ cylinder Set.univ 0 τ, linearOp (cylinder Set.univ 0 τ) a b u p = f p)
    (hvEq : ∀ p ∈ cylinder Set.univ τ T, linearOp (cylinder Set.univ τ T) a b v p = f p) :
    SchauderBound α (cylinder Set.univ 0 T) (timePaste τ u v) (2*(C+D)) ∧
    HolderBound α (cylinder Set.univ 0 T)
      (fun p => (timePaste τ u v p,spatialD (timePaste τ u v) p)) (2*(C+D)) ∧
    Set.EqOn (timePaste τ u v) u (cylinder Set.univ 0 τ) ∧
    Set.EqOn (timePaste τ u v) v (cylinder Set.univ τ T) ∧
    ∀ p ∈ cylinder Set.univ 0 T, linearOp (cylinder Set.univ 0 T) a b (timePaste τ u v) p = f p := by
  exact ⟨schauderBound_timePaste hα hτ hT hu hv hTrace htTrace,
    lowPair_holderBound_timePaste hα huLow hvLow hTrace,
    timePaste_eqOn_left u v,timePaste_eqOn_right hTrace,
    equation_timePaste hτ hT hu.1 hv.1 hTrace htTrace huEq hvEq⟩

end Yau.LeafProofs.L16Aux
