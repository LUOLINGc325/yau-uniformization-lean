import Yau.LeafProofs.L16TimeGluing
import Yau.LeafProofs.L16Continuation
import Yau.LeafProofs.L16LocalTimeTransport
import Yau.LeafProofs.L16InteriorDataLow

open Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types false

namespace Yau.LeafProofs.L16BoundaryTimeAux

open Yau.Parabolic Yau.ParabolicCandidates L16Aux

theorem timePaste_eqOn_left_space {n : ℕ} {V : Type*} {X : Set (Space n)} {τ : ℝ}
    (u v : Point n → V) : EqOn (timePaste τ u v) u (cylinder X 0 τ) := by
  intro p hp
  simp [timePaste,hp.2.2]

theorem timePaste_eqOn_right_space {n : ℕ} {V : Type*} {X : Set (Space n)} {τ T : ℝ}
    {u v : Point n → V} (hTrace : ∀ x ∈ X, u (x,τ) = v (x,τ)) :
    EqOn (timePaste τ u v) v (cylinder X τ T) := by
  intro p hp
  by_cases h : p.2 ≤ τ
  · have ht : p.2 = τ := le_antisymm h hp.2.1
    simpa [timePaste,h,← ht] using hTrace p.1 hp.1
  · simp [timePaste,h]

theorem cylinder_union_at_time {n : ℕ} {X : Set (Space n)} {τ T : ℝ}
    (hτ : 0 ≤ τ) (hT : τ ≤ T) :
    cylinder X 0 τ ∪ cylinder X τ T = cylinder X 0 T := by
  ext p
  simp only [cylinder,mem_union,mem_prod,mem_Icc]
  constructor
  · rintro (h | h) <;> refine ⟨h.1,?_,?_⟩ <;> linarith [h.2.1,h.2.2]
  · intro h
    by_cases ht : p.2 ≤ τ
    · exact Or.inl ⟨h.1,h.2.1,ht⟩
    · exact Or.inr ⟨h.1,le_of_not_ge ht,h.2.2⟩

theorem continuousOn_timePaste_space {n : ℕ} {V : Type*} [TopologicalSpace V]
    {X : Set (Space n)} (hX : IsClosed X) {τ T : ℝ} (hτ : 0 ≤ τ) (hT : τ ≤ T)
    {u v : Point n → V} (hu : ContinuousOn u (cylinder X 0 τ))
    (hv : ContinuousOn v (cylinder X τ T)) (hTrace : ∀ x ∈ X, u (x,τ) = v (x,τ)) :
    ContinuousOn (timePaste τ u v) (cylinder X 0 T) := by
  rw [← cylinder_union_at_time hτ hT]
  exact (hu.congr (timePaste_eqOn_left_space u v)).union_of_isClosed
    (hv.congr (timePaste_eqOn_right_space hTrace))
    (hX.prod isClosed_Icc) (hX.prod isClosed_Icc)

/-- Matching time derivatives are required only on X, including its genuine
boundary; nothing is asserted about time derivatives outside X. -/
theorem timePaste_hasDerivWithinAt_space {n : ℕ} {X : Set (Space n)} {τ T : ℝ}
    (hτ : 0 < τ) (hT : τ < T) {u v : Point n → ℝ}
    (hu : C2 (cylinder X 0 τ) u) (hv : C2 (cylinder X τ T) v)
    (hTrace : ∀ x ∈ X, u (x,τ) = v (x,τ))
    (htTrace : ∀ x ∈ X, timeD (cylinder X 0 τ) u (x,τ) = timeD (cylinder X τ T) v (x,τ))
    {p : Point n} (hp : p ∈ cylinder X 0 T) :
    HasDerivWithinAt (fun t => timePaste τ u v (p.1,t))
      (timePaste τ (timeD (cylinder X 0 τ) u) (timeD (cylinder X τ T) v) p) (Icc 0 T) p.2 := by
  have hU {s : ℝ} (hs : s ∈ Icc 0 τ) :
      HasDerivWithinAt (fun t => timePaste τ u v (p.1,t))
        (timeD (cylinder X 0 τ) u (p.1,s)) (Icc 0 τ) s := by
    have h := (hu.2.2.2.2.2 (p.1,s) ⟨hp.1,hs⟩).hasDerivWithinAt
    simp only [timeD,cylinder,mem_ofPred_eq,mem_prod,hp.1,true_and,ofPred_mem_eq] at h ⊢
    exact h.congr_of_mem (fun t ht => timePaste_eqOn_left_space u v
      (x := (p.1,t)) ⟨hp.1,ht⟩) hs
  have hV {s : ℝ} (hs : s ∈ Icc τ T) :
      HasDerivWithinAt (fun t => timePaste τ u v (p.1,t))
        (timeD (cylinder X τ T) v (p.1,s)) (Icc τ T) s := by
    have h := (hv.2.2.2.2.2 (p.1,s) ⟨hp.1,hs⟩).hasDerivWithinAt
    simp only [timeD,cylinder,mem_ofPred_eq,mem_prod,hp.1,true_and,ofPred_mem_eq] at h ⊢
    exact h.congr_of_mem (fun t ht => timePaste_eqOn_right_space hTrace
      (x := (p.1,t)) ⟨hp.1,ht⟩) hs
  rcases lt_trichotomy p.2 τ with h | h | h
  · have hs : Icc (0 : ℝ) τ ∈ 𝓝[Icc 0 T] p.2 := by
      filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds h)] with t ht htτ
      exact ⟨ht.1,htτ.le⟩
    simpa [timePaste,h.le] using (hU ⟨hp.2.1,h.le⟩).mono_of_mem_nhdsWithin hs
  · have hh := (hU ⟨hτ.le,le_rfl⟩).union
      ((hV ⟨le_rfl,hT.le⟩).congr_deriv (htTrace p.1 hp.1).symm)
    have hi : Icc (0 : ℝ) τ ∪ Icc τ T = Icc 0 T := by
      ext t
      simp only [mem_union,mem_Icc]
      constructor
      · rintro (ht | ht) <;> constructor <;> linarith [ht.1,ht.2]
      · intro ht
        by_cases h : t ≤ τ
        · exact Or.inl ⟨ht.1,h⟩
        · exact Or.inr ⟨le_of_not_ge h,ht.2⟩
    have hpeta : p = (p.1,τ) := Prod.ext rfl h
    rw [hpeta]
    simpa [timePaste,hi] using hh
  · have hs : Icc τ T ∈ 𝓝[Icc 0 T] p.2 := by
      filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds h)] with t ht htτ
      exact ⟨htτ.le,ht.2⟩
    simpa [timePaste,not_le_of_gt h] using (hV ⟨h.le,hp.2.2⟩).mono_of_mem_nhdsWithin hs

theorem timeD_timePaste_space {n : ℕ} {X : Set (Space n)} {τ T : ℝ}
    (hτ : 0 < τ) (hT : τ < T) {u v : Point n → ℝ}
    (hu : C2 (cylinder X 0 τ) u) (hv : C2 (cylinder X τ T) v)
    (hTrace : ∀ x ∈ X, u (x,τ) = v (x,τ))
    (htTrace : ∀ x ∈ X, timeD (cylinder X 0 τ) u (x,τ) = timeD (cylinder X τ T) v (x,τ))
    {p : Point n} (hp : p ∈ cylinder X 0 T) :
    timeD (cylinder X 0 T) (timePaste τ u v) p =
      timePaste τ (timeD (cylinder X 0 τ) u) (timeD (cylinder X τ T) v) p := by
  have h := (timePaste_hasDerivWithinAt_space hτ hT hu hv hTrace htTrace hp).derivWithin
    (uniqueDiffOn_Icc (hτ.trans hT) _ hp.2)
  simpa only [timeD,cylinder,mem_ofPred_eq,mem_prod,hp.1,true_and,ofPred_mem_eq] using h

theorem c2_timePaste_space {n : ℕ} {X : Set (Space n)} (hX : IsClosed X) {τ T : ℝ}
    (hτ : 0 < τ) (hT : τ < T) {u v : Point n → ℝ}
    (hu : C2 (cylinder X 0 τ) u) (hv : C2 (cylinder X τ T) v)
    (hTrace : ∀ x, u (x,τ) = v (x,τ))
    (htTrace : ∀ x ∈ X, timeD (cylinder X 0 τ) u (x,τ) = timeD (cylinder X τ T) v (x,τ)) :
    C2 (cylinder X 0 T) (timePaste τ u v) := by
  have hTraceX : ∀ x ∈ X, u (x,τ) = v (x,τ) := fun x _ => hTrace x
  refine ⟨continuousOn_timePaste_space hX hτ.le hT.le hu.1 hv.1 hTraceX,?_,?_,?_,?_,?_⟩
  · rw [spatialD_timePaste]
    exact continuousOn_timePaste_space hX hτ.le hT.le hu.2.1 hv.2.1
      (fun x _ => spatialD_eq_of_trace hTrace x)
  · rw [spatialDD_timePaste]
    exact continuousOn_timePaste_space hX hτ.le hT.le hu.2.2.1 hv.2.2.1
      (fun x _ => spatialDD_eq_of_trace hTrace x)
  · exact (continuousOn_timePaste_space hX hτ.le hT.le hu.2.2.2.1 hv.2.2.2.1 htTrace).congr
      (fun p hp => timeD_timePaste_space hτ hT hu hv hTraceX htTrace hp)
  · intro p hp
    by_cases h : p.2 ≤ τ
    · simpa only [timePaste,ite_eq_left h] using hu.2.2.2.2.1 p ⟨hp.1,hp.2.1,h⟩
    · simpa only [timePaste,ite_eq_right h] using hv.2.2.2.2.1 p ⟨hp.1,le_of_not_ge h,hp.2.2⟩
  · intro p hp
    have h := (timePaste_hasDerivWithinAt_space hτ hT hu hv hTraceX htTrace hp).differentiableWithinAt
    simpa only [cylinder,mem_ofPred_eq,mem_prod,hp.1,true_and,ofPred_mem_eq] using h

theorem linearOp_timePaste_space {n : ℕ} {X : Set (Space n)} {τ T : ℝ}
    (hτ : 0 < τ) (hT : τ < T) {u v : Point n → ℝ}
    (hu : C2 (cylinder X 0 τ) u) (hv : C2 (cylinder X τ T) v)
    (hTrace : ∀ x, u (x,τ) = v (x,τ))
    (htTrace : ∀ x ∈ X, timeD (cylinder X 0 τ) u (x,τ) = timeD (cylinder X τ T) v (x,τ))
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ) {p : Point n}
    (hp : p ∈ cylinder X 0 T) :
    linearOp (cylinder X 0 T) a b (timePaste τ u v) p =
      timePaste τ (linearOp (cylinder X 0 τ) a b u) (linearOp (cylinder X τ T) a b v) p := by
  simp only [linearOp,timeD_timePaste_space hτ hT hu hv (fun x _ => hTrace x) htTrace hp,
    spatialD_timePaste,spatialDD_timePaste]
  by_cases h : p.2 ≤ τ <;> simp [timePaste,h,linearOp]

/-- The lateral trace is constant as an actual function of time on the slab,
so its one-sided time derivative vanishes at both end faces too. -/
theorem timeD_zero_of_time_slice_zero {n : ℕ} {X : Set (Space n)} {l r : ℝ}
    {u : Point n → ℝ} {x : Space n} (hx : x ∈ X) {t : ℝ} (ht : t ∈ Icc l r)
    (hzero : ∀ s ∈ Icc l r, u (x,s) = 0) : timeD (cylinder X l r) u (x,t) = 0 := by
  have hf : {s | (x,s) ∈ cylinder X l r} = Icc l r := by ext s; simp [cylinder,hx]
  simp only [timeD,hf]
  rw [derivWithin_congr (fun s hs => hzero s hs) (hzero t ht)]
  simp

theorem holderBound_timePaste_space {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    {X : Set (Space n)} {α C D τ T : ℝ} (hα : 0 < α) {u v : Point n → V}
    (hu : HolderBound α (cylinder X 0 τ) u C) (hv : HolderBound α (cylinder X τ T) v D)
    (hTrace : ∀ x ∈ X, u (x,τ) = v (x,τ)) :
    HolderBound α (cylinder X 0 T) (timePaste τ u v) (2*(C+D)) := by
  have hC : C ≤ 2*(C+D) := by linarith [hu.1,hv.1]
  have hD : D ≤ 2*(C+D) := by linarith [hu.1,hv.1]
  have hw (p q : Point n) : 0 ≤ holderWeight α p q := by dsimp [holderWeight]; positivity
  have hCross (p q : Point n) (hp : p ∈ cylinder X 0 τ) (hq : q ∈ cylinder X τ T) :
      ‖u p-v q‖ ≤ 2*(C+D)*holderWeight α p q := by
    let z : Point n := (p.1,τ)
    have hzU : z ∈ cylinder X 0 τ := ⟨hp.1,hp.2.1.trans hp.2.2,le_rfl⟩
    have hzV : z ∈ cylinder X τ T := ⟨hp.1,le_rfl,hq.2.1.trans hq.2.2⟩
    have habs1 : |p.2-τ| ≤ |p.2-q.2| := by
      rw [abs_of_nonpos (by linarith [hp.2.2]),abs_of_nonpos (by linarith [hp.2.2,hq.2.1])]
      linarith [hq.2.1]
    have habs2 : |τ-q.2| ≤ |p.2-q.2| := by
      rw [abs_of_nonpos (by linarith [hq.2.1]),abs_of_nonpos (by linarith [hp.2.2,hq.2.1])]
      linarith [hp.2.2]
    have hw1 : holderWeight α p z ≤ holderWeight α p q := by
      simp only [holderWeight,z,Prod.fst,Prod.snd,sub_self,norm_zero,
        Real.zero_rpow (ne_of_gt hα),zero_add]
      exact (Real.rpow_le_rpow (abs_nonneg _) habs1 (by positivity)).trans
        (le_add_of_nonneg_left (by positivity))
    have hw2 : holderWeight α z q ≤ holderWeight α p q := by
      exact add_le_add le_rfl (Real.rpow_le_rpow (abs_nonneg _) habs2 (by positivity))
    calc
      ‖u p-v q‖ ≤ ‖u p-u z‖+‖u z-v q‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = ‖u p-u z‖+‖v z-v q‖ := by rw [show u z = v z from hTrace p.1 hp.1]
      _ ≤ C*holderWeight α p z+D*holderWeight α z q :=
        add_le_add (hu.2.2 p hp z hzU) (hv.2.2 z hzV q hq)
      _ ≤ C*holderWeight α p q+D*holderWeight α p q :=
        add_le_add (mul_le_mul_of_nonneg_left hw1 hu.1) (mul_le_mul_of_nonneg_left hw2 hv.1)
      _ ≤ 2*(C+D)*holderWeight α p q := by
        nlinarith [mul_nonneg (add_nonneg hu.1 hv.1) (hw p q)]
  refine ⟨by linarith [hu.1,hv.1],?_,?_⟩
  · intro p hp
    by_cases h : p.2 ≤ τ
    · simpa [timePaste,h] using (hu.2.1 p ⟨hp.1,hp.2.1,h⟩).trans hC
    · simpa [timePaste,h] using (hv.2.1 p ⟨hp.1,le_of_not_ge h,hp.2.2⟩).trans hD
  · intro p hp q hq
    by_cases h : p.2 ≤ τ <;> by_cases h' : q.2 ≤ τ
    · simpa [timePaste,h,h'] using (hu.2.2 p ⟨hp.1,hp.2.1,h⟩ q ⟨hq.1,hq.2.1,h'⟩).trans
        (mul_le_mul_of_nonneg_right hC (hw p q))
    · simpa [timePaste,h,h'] using hCross p q ⟨hp.1,hp.2.1,h⟩ ⟨hq.1,le_of_not_ge h',hq.2.2⟩
    · simpa [timePaste,h,h',norm_sub_rev,show holderWeight α q p = holderWeight α p q by
        simp only [holderWeight,norm_sub_rev,abs_sub_comm]] using
        hCross q p ⟨hq.1,hq.2.1,h'⟩ ⟨hp.1,le_of_not_ge h,hp.2.2⟩
    · simpa [timePaste,h,h'] using (hv.2.2 p ⟨hp.1,le_of_not_ge h,hp.2.2⟩
        q ⟨hq.1,le_of_not_ge h',hq.2.2⟩).trans (mul_le_mul_of_nonneg_right hD (hw p q))

theorem schauderBound_timePaste_space {n : ℕ} {X : Set (Space n)} (hX : IsClosed X)
    {α C D τ T : ℝ} (hα : 0 < α) (hτ : 0 < τ) (hT : τ < T) {u v : Point n → ℝ}
    (hu : SchauderBound α (cylinder X 0 τ) u C) (hv : SchauderBound α (cylinder X τ T) v D)
    (hTrace : ∀ x, u (x,τ) = v (x,τ))
    (htTrace : ∀ x ∈ X, timeD (cylinder X 0 τ) u (x,τ) = timeD (cylinder X τ T) v (x,τ)) :
    SchauderBound α (cylinder X 0 T) (timePaste τ u v) (2*(C+D)) := by
  letI boundaryTimeDualGroup : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
  letI boundaryTimeDualSpace : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
  letI boundaryTimeHessianGroup : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
  refine ⟨c2_timePaste_space hX hτ hT hu.1 hv.1 hTrace htTrace,by linarith [hu.2.1,hv.2.1],?_,?_,?_⟩
  · intro p hp
    rw [spatialD_timePaste]
    by_cases h : p.2 ≤ τ
    · have hB := hu.2.2.1 p ⟨hp.1,hp.2.1,h⟩
      simp only [timePaste,ite_eq_left h]
      constructor <;> linarith [hB.1,hB.2,hu.2.1,hv.2.1]
    · have hB := hv.2.2.1 p ⟨hp.1,le_of_not_ge h,hp.2.2⟩
      simp only [timePaste,ite_eq_right h]
      constructor <;> linarith [hB.1,hB.2,hu.2.1,hv.2.1]
  · rw [spatialDD_timePaste]
    exact holderBound_timePaste_space hα hu.2.2.2.1 hv.2.2.2.1
      (fun x _ => spatialDD_eq_of_trace hTrace x)
  · exact holderBound_congr_on (holderBound_timePaste_space hα hu.2.2.2.2 hv.2.2.2.2 htTrace)
      (fun p hp => (timeD_timePaste_space hτ hT hu.1 hv.1 (fun x _ => hTrace x) htTrace hp).symm)

theorem lowPair_holderBound_timePaste_space {n : ℕ} {X : Set (Space n)}
    {α C D τ T : ℝ} (hα : 0 < α) {u v : Point n → ℝ}
    (hu : HolderBound α (cylinder X 0 τ) (fun p => (u p,spatialD u p)) C)
    (hv : HolderBound α (cylinder X τ T) (fun p => (v p,spatialD v p)) D)
    (hTrace : ∀ x, u (x,τ) = v (x,τ)) :
    HolderBound α (cylinder X 0 T)
      (fun p => (timePaste τ u v p,spatialD (timePaste τ u v) p)) (2*(C+D)) := by
  letI boundaryTimeLowDualGroup : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
  apply holderBound_congr_on (holderBound_timePaste_space hα hu hv
    (fun x _ => Prod.ext (hTrace x) (spatialD_eq_of_trace hTrace x)))
  intro p hp
  rw [spatialD_timePaste]
  by_cases h : p.2 ≤ τ <;> simp [timePaste,h]

/-- The equations force matching time jets only on the physical closed
spatial set. The history produced here has no ambient-time C² assertion. -/
theorem timePaste_solution_space {n : ℕ} {X : Set (Space n)} (hX : IsClosed X)
    {α C D τ T : ℝ} (hα : 0 < α) (hτ : 0 < τ) (hT : τ < T)
    {u v f : Point n → ℝ} {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (hu : SchauderBound α (cylinder X 0 τ) u C) (hv : SchauderBound α (cylinder X τ T) v D)
    (huLow : HolderBound α (cylinder X 0 τ) (fun p => (u p,spatialD u p)) C)
    (hvLow : HolderBound α (cylinder X τ T) (fun p => (v p,spatialD v p)) D)
    (hTrace : ∀ x, u (x,τ) = v (x,τ))
    (huEq : ∀ p ∈ cylinder X 0 τ, linearOp (cylinder X 0 τ) a b u p = f p)
    (hvEq : ∀ p ∈ cylinder X τ T, linearOp (cylinder X τ T) a b v p = f p) :
    SchauderBound α (cylinder X 0 T) (timePaste τ u v) (2*(C+D)) ∧
    HolderBound α (cylinder X 0 T)
      (fun p => (timePaste τ u v p,spatialD (timePaste τ u v) p)) (2*(C+D)) ∧
    (∀ x, timePaste τ u v (x,T) = v (x,T)) ∧
    ∀ p ∈ cylinder X 0 T, linearOp (cylinder X 0 T) a b (timePaste τ u v) p = f p := by
  have htTrace : ∀ x ∈ X, timeD (cylinder X 0 τ) u (x,τ) = timeD (cylinder X τ T) v (x,τ) := by
    intro x hx
    apply timeD_eq_of_trace_and_operator a b hTrace x
    rw [huEq (x,τ) ⟨hx,hτ.le,le_rfl⟩,hvEq (x,τ) ⟨hx,le_rfl,hT.le⟩]
  refine ⟨schauderBound_timePaste_space hX hα hτ hT hu hv hTrace htTrace,
    lowPair_holderBound_timePaste_space hα huLow hvLow hTrace,?_,?_⟩
  · intro x
    simp [timePaste,not_le_of_gt hT]
  · intro p hp
    rw [linearOp_timePaste_space hτ hT hu.1 hv.1 hTrace htTrace a b hp]
    by_cases h : p.2 ≤ τ
    · simpa [timePaste,h] using huEq p ⟨hp.1,hp.2.1,h⟩
    · simpa [timePaste,h] using hvEq p ⟨hp.1,le_of_not_ge h,hp.2.2⟩

theorem traceCorrectedSource_corner {n : ℕ} {O : Set (Space n)} {l r τ : ℝ}
    {u f : Point n → ℝ} {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (hτ : τ ∈ Icc l r)
    (huEq : ∀ p ∈ cylinder (closure O) l r, linearOp (cylinder (closure O) l r) a b u p = f p)
    (hLat : ∀ x ∈ frontier O, ∀ t ∈ Icc l r, u (x,t) = 0) :
    ∀ x ∈ frontier O,
      traceCorrectedSource τ u (timeTranslate τ a) (timeTranslate τ b) (timeTranslate τ f) (x,0) = 0 := by
  intro x hx
  have hzero := timeD_zero_of_time_slice_zero (frontier_subset_closure hx) hτ (hLat x hx)
  have hEq := huEq (x,τ) ⟨frontier_subset_closure hx,hτ⟩
  simp only [linearOp,hzero] at hEq
  simp only [traceCorrectedSource,timeTranslate,timeTranslatePoint,Prod.fst,Prod.snd,zero_add,
    spatialDD_spatialTraceLift,spatialD_spatialTraceLift]
  linarith

theorem schauderBound_mono_space {n : ℕ} {S X : Set (Space n)} {α C l r : ℝ}
    (hSX : S ⊆ X) {u : Point n → ℝ} (hu : SchauderBound α (cylinder X l r) u C) :
    SchauderBound α (cylinder S l r) u C := by
  have hSub : cylinder S l r ⊆ cylinder X l r := fun p hp => ⟨hSX hp.1,hp.2⟩
  refine ⟨c2_cylinder_mono_space hSX hu.1,hu.2.1,fun p hp => hu.2.2.1 p (hSub hp),
    holderBound_mono hu.2.2.2.1 hSub,?_⟩
  exact holderBound_congr_on (holderBound_mono hu.2.2.2.2 hSub)
    (fun p hp => (timeD_cylinder_change_space u hp.1 (hSX hp.1)).symm)

theorem holderBound_timeTranslate_subslab_space {n : ℕ} {X : Set (Space n)}
    {V : Type*} [NormedAddCommGroup V] {α C T S τ : ℝ} (hτ : 0 ≤ τ) (hST : S+τ ≤ T)
    {u : Point n → V} (hu : HolderBound α (cylinder X 0 T) u C) :
    HolderBound α (cylinder X 0 S) (timeTranslate τ u) C := by
  apply holderBound_timeTranslate_on_space
  exact holderBound_mono hu (fun p hp => ⟨hp.1,by linarith [hp.2.1],hp.2.2.trans hST⟩)

theorem elliptic_timeTranslate_subslab_space {n : ℕ} {X : Set (Space n)}
    {T S τ lam upper : ℝ} (hτ : 0 ≤ τ) (hST : S+τ ≤ T) {a : Point n → Mat n}
    (ha : Elliptic (cylinder X 0 T) a lam upper) :
    Elliptic (cylinder X 0 S) (timeTranslate τ a) lam upper := by
  refine ⟨ha.1,ha.2.1,?_⟩
  intro p hp
  exact ha.2.2 (timeTranslatePoint τ p) ⟨hp.1,by dsimp [timeTranslatePoint]; linarith [hp.2.1],
    by dsimp [timeTranslatePoint]; linarith [hp.2.2]⟩

/-- The parent's short-time theorem, stated with its actual solution and jets.
Only the genuine initial corner vanishes; interior initial forcing may be nonzero. -/
def CompatibleAmbientShortInverse {n : ℕ} (O : Set (Space n))
    (α lam upper M δ Cs : ℝ) : Prop :=
  ∀ S : ℝ, 0 < S → S ≤ δ →
    ∀ (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ),
      HolderBound α (cylinder (closure O) 0 S) a M →
      (∀ i, HolderBound α (cylinder (closure O) 0 S) (fun p => b p i) M) →
      Elliptic (cylinder (closure O) 0 S) a lam upper →
      ∀ (g : Point n → ℝ) (G : ℝ), HolderBound α (cylinder (closure O) 0 S) g G →
      (∀ x ∈ frontier O, g (x,0) = 0) →
      ∃ v : Point n → ℝ, SchauderBound α (cylinder univ 0 S) v (Cs*G) ∧
        HolderBound α (cylinder univ 0 S) (fun p => (v p,spatialD v p)) (Cs*G) ∧
        (∀ x, v (x,0) = 0) ∧
        (∀ x ∈ frontier O, ∀ t ∈ Icc 0 S, v (x,t) = 0) ∧
        ∀ p ∈ cylinder (closure O) 0 S,
          linearOp (cylinder (closure O) 0 S) a b v p = g p

def traceSourceBudget (n : ℕ) (M : ℝ) : ℝ :=
  2*M*((Fintype.card (Yau.RIdx n) : ℝ)^2+(Fintype.card (Yau.RIdx n) : ℝ))

theorem traceSourceBudget_nonneg (n : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ traceSourceBudget n M := by dsimp [traceSourceBudget]; positivity

/-- Restart from the most recent ambient segment, never from an allegedly
ambient-regular pasted history. The corrected forcing has the true corner. -/
theorem restart_from_ambient_segment {n : ℕ} {O : Set (Space n)}
    {α lam upper M δ Cs T S l r τ D F : ℝ}
    (hα : 0 < α) (hS : 0 < S) (hSδ : S ≤ δ) (hτ : 0 ≤ τ) (hST : S+τ ≤ T)
    (hOldτ : τ ∈ Icc l r) (hShort : CompatibleAmbientShortInverse O α lam upper M δ Cs)
    {u f : Point n → ℝ} {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (hu : SchauderBound α (cylinder univ l r) u D)
    (huLow : HolderBound α (cylinder univ l r) (fun p => (u p,spatialD u p)) D)
    (huEq : ∀ p ∈ cylinder (closure O) l r,
      linearOp (cylinder (closure O) l r) a b u p = f p)
    (huLat : ∀ x ∈ frontier O, ∀ t ∈ Icc l r, u (x,t) = 0)
    (ha : HolderBound α (cylinder (closure O) 0 T) a M)
    (hb : ∀ i, HolderBound α (cylinder (closure O) 0 T) (fun p => b p i) M)
    (hEll : Elliptic (cylinder (closure O) 0 T) a lam upper)
    (hf : HolderBound α (cylinder (closure O) 0 T) f F) :
    ∃ w : Point n → ℝ,
      SchauderBound α (cylinder univ τ (τ+S)) w (D+Cs*(F+traceSourceBudget n M*D)) ∧
      HolderBound α (cylinder univ τ (τ+S)) (fun p => (w p,spatialD w p))
        (D+Cs*(F+traceSourceBudget n M*D)) ∧
      (∀ x, w (x,τ) = u (x,τ)) ∧
      (∀ x ∈ frontier O, ∀ t ∈ Icc τ (τ+S), w (x,t) = 0) ∧
      ∀ p ∈ cylinder (closure O) τ (τ+S),
        linearOp (cylinder (closure O) τ (τ+S)) a b w p = f p := by
  let aτ := timeTranslate τ a
  let bτ := timeTranslate τ b
  let fτ := timeTranslate τ f
  let g := traceCorrectedSource τ u aτ bτ fτ
  let G : ℝ := F+traceSourceBudget n M*D
  have haS : HolderBound α (cylinder (closure O) 0 S) aτ M :=
    holderBound_timeTranslate_subslab_space hτ hST ha
  have hbS (i : Yau.RIdx n) : HolderBound α (cylinder (closure O) 0 S) (fun p => bτ p i) M :=
    holderBound_timeTranslate_subslab_space hτ hST (hb i)
  have hfS : HolderBound α (cylinder (closure O) 0 S) fτ F :=
    holderBound_timeTranslate_subslab_space hτ hST hf
  have hEllS : Elliptic (cylinder (closure O) 0 S) aτ lam upper :=
    elliptic_timeTranslate_subslab_space hτ hST hEll
  have hg : HolderBound α (cylinder (closure O) 0 S) g G := by
    convert traceCorrectedSource_holderBound hα hu huLow hOldτ haS hbS hfS using 1
    dsimp [G,traceSourceBudget]
    ring
  have hg0 : ∀ x ∈ frontier O, g (x,0) = 0 := traceCorrectedSource_corner hOldτ huEq huLat
  obtain ⟨v,hv,hvLow,hv0,hvLat,hvEq⟩ := hShort S hS hSδ aτ bτ haS hbS hEllS g G hg hg0
  let P := spatialTraceLift τ u
  let w₀ : Point n → ℝ := fun p => P p+v p
  have hLift : SchauderBound α (cylinder univ 0 S) P D :=
    schauderBound_spatialTraceLift hα hu hOldτ _
  have hLiftLow : HolderBound α (cylinder univ 0 S) (fun p => (P p,spatialD P p)) D :=
    holderBound_spatialTraceLift hα huLow hOldτ _
  have hSum := schauderBound_add_with_low_pair hLift hv hLiftLow hvLow
  have hLiftX : C2 (cylinder (closure O) 0 S) P :=
    c2_cylinder_mono_space (subset_univ _) hLift.1
  have hvX : C2 (cylinder (closure O) 0 S) v := c2_cylinder_mono_space (subset_univ _) hv.1
  have hw₀Eq : ∀ p ∈ cylinder (closure O) 0 S,
      linearOp (cylinder (closure O) 0 S) aτ bτ w₀ p = fτ p := by
    intro p hp
    rw [linearOp_add hLiftX hvX hp,hvEq p hp]
    simp only [linearOp,P,g,timeD_spatialTraceLift,Pi.zero_apply,traceCorrectedSource]
    ring
  refine ⟨timeTranslate (-τ) w₀,schauderBound_timeUntranslate hS hSum.1,
    holderBound_timeUntranslate hSum.2,?_,?_,?_⟩
  · intro x
    simp only [timeTranslate,timeTranslatePoint,add_neg_cancel,w₀,P,spatialTraceLift,hv0,add_zero]
  · intro x hx t ht
    have htS : t+(-τ) ∈ Icc 0 S := ⟨by linarith [ht.1],by linarith [ht.2]⟩
    simp only [timeTranslate,timeTranslatePoint,w₀,P,spatialTraceLift,
      huLat x hx τ hOldτ,hvLat x hx _ htS,zero_add]
  · intro p hp
    have h0 : τ+(-τ) = 0 := by ring
    have h1 : τ+S+(-τ) = S := by ring
    have hw₀X : C2 (cylinder (closure O) 0 S) w₀ :=
      c2_cylinder_mono_space (subset_univ _) hSum.1.1
    have hShift : C2 (cylinder (closure O) (τ+(-τ)) (τ+S+(-τ))) w₀ := by
      simpa only [h0,h1] using hw₀X
    have hTransport := linearOp_timeTranslate_on_space (by linarith : τ < τ+S) hShift aτ bτ hp
    have hpS : timeTranslatePoint (-τ) p ∈ cylinder (closure O) 0 S :=
      ⟨hp.1,by dsimp [timeTranslatePoint]; linarith [hp.2.1],
        by dsimp [timeTranslatePoint]; linarith [hp.2.2]⟩
    change linearOp (cylinder (closure O) τ (τ+S)) (timeTranslate (-τ) (timeTranslate τ a))
      (timeTranslate (-τ) (timeTranslate τ b)) (timeTranslate (-τ) w₀) p = _ at hTransport
    rw [timeTranslate_cancel,timeTranslate_cancel,h0,h1,hw₀Eq _ hpS] at hTransport
    simpa only [fτ,timeTranslate,timeTranslatePoint,neg_add_cancel_right] using hTransport

def segmentBudget (κ Cs : ℝ) : ℕ → ℝ
  | 0 => Cs
  | j+1 => segmentBudget κ Cs j+Cs*(1+κ*segmentBudget κ Cs j)

def historyBudget (κ Cs : ℝ) : ℕ → ℝ
  | 0 => Cs
  | j+1 => 2*(historyBudget κ Cs j+segmentBudget κ Cs (j+1))

theorem segmentBudget_pos {κ Cs : ℝ} (hκ : 0 ≤ κ) (hCs : 0 < Cs) :
    ∀ j, 0 < segmentBudget κ Cs j := by
  intro j
  induction j with
  | zero => exact hCs
  | succ j ih =>
    exact add_pos ih (mul_pos hCs (by positivity))

theorem historyBudget_pos {κ Cs : ℝ} (hκ : 0 ≤ κ) (hCs : 0 < Cs) :
    ∀ j, 0 < historyBudget κ Cs j := by
  intro j
  induction j with
  | zero => exact hCs
  | succ j ih =>
    exact mul_pos (by norm_num) (add_pos ih (segmentBudget_pos hκ hCs (j+1)))

def gridTime (h : ℝ) (j : ℕ) : ℝ := (j : ℝ)*h

theorem gridTime_succ (h : ℝ) (j : ℕ) : gridTime h (j+1) = gridTime h j+h := by
  simp only [gridTime,Nat.cast_add,Nat.cast_one]
  ring

theorem gridTime_succ_pos {h : ℝ} (hh : 0 < h) (j : ℕ) : 0 < gridTime h (j+1) := by
  dsimp [gridTime]
  positivity

/-- The history has physical-domain regularity. Only its most recent
segment retains ambient regularity and provides the next spatial trace. -/
def ContinuationState {n : ℕ} (O : Set (Space n)) (α κ Cs h F : ℝ)
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ) (f : Point n → ℝ)
    (j : ℕ) (u v : Point n → ℝ) : Prop :=
  SchauderBound α (cylinder (closure O) 0 (gridTime h (j+1))) u (historyBudget κ Cs j*F) ∧
    HolderBound α (cylinder (closure O) 0 (gridTime h (j+1)))
      (fun p => (u p,spatialD u p)) (historyBudget κ Cs j*F) ∧
    (∀ x, u (x,0) = 0) ∧
    (∀ x ∈ frontier O, ∀ t ∈ Icc 0 (gridTime h (j+1)), u (x,t) = 0) ∧
    (∀ p ∈ cylinder (closure O) 0 (gridTime h (j+1)),
      linearOp (cylinder (closure O) 0 (gridTime h (j+1))) a b u p = f p) ∧
    SchauderBound α (cylinder univ (gridTime h j) (gridTime h (j+1))) v (segmentBudget κ Cs j*F) ∧
    HolderBound α (cylinder univ (gridTime h j) (gridTime h (j+1)))
      (fun p => (v p,spatialD v p)) (segmentBudget κ Cs j*F) ∧
    (∀ x ∈ frontier O, ∀ t ∈ Icc (gridTime h j) (gridTime h (j+1)), v (x,t) = 0) ∧
    (∀ p ∈ cylinder (closure O) (gridTime h j) (gridTime h (j+1)),
      linearOp (cylinder (closure O) (gridTime h j) (gridTime h (j+1))) a b v p = f p) ∧
    ∀ x, u (x,gridTime h (j+1)) = v (x,gridTime h (j+1))

/-- A finite grid preserves the two-object invariant, with all quantitative
growth factors independent of the coefficient fields and forcing. -/
theorem exists_grid_continuation {n : ℕ} {O : Set (Space n)}
    {α lam upper M δ Cs T h F : ℝ} (hα : 0 < α) (hh : 0 < h) (hhδ : h ≤ δ)
    (hShort : CompatibleAmbientShortInverse O α lam upper M δ Cs)
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {f : Point n → ℝ}
    (ha : HolderBound α (cylinder (closure O) 0 T) a M)
    (hb : ∀ i, HolderBound α (cylinder (closure O) 0 T) (fun p => b p i) M)
    (hEll : Elliptic (cylinder (closure O) 0 T) a lam upper)
    (hf : HolderBound α (cylinder (closure O) 0 T) f F)
    (hf0 : ∀ x ∈ frontier O, f (x,0) = 0) :
    ∀ j : ℕ, gridTime h (j+1) ≤ T → ∃ u v : Point n → ℝ,
      ContinuationState O α (traceSourceBudget n M) Cs h F a b f j u v := by
  intro j
  induction j with
  | zero =>
    intro hStop
    have hhT : h ≤ T := by simpa only [gridTime,Nat.zero_add,Nat.cast_one,one_mul] using hStop
    have hSub : cylinder (closure O) 0 h ⊆ cylinder (closure O) 0 T :=
      fun p hp => ⟨hp.1,hp.2.1,hp.2.2.trans hhT⟩
    obtain ⟨v,hv,hvLow,hv0,hvLat,hvEq⟩ := hShort h hh hhδ a b
      (holderBound_mono ha hSub) (fun i => holderBound_mono (hb i) hSub)
      (elliptic_mono hEll hSub) f F (holderBound_mono hf hSub) hf0
    refine ⟨v,v,?_⟩
    simp only [ContinuationState,historyBudget,segmentBudget,gridTime,
      Nat.zero_add,Nat.cast_zero,Nat.cast_one,zero_mul,one_mul]
    exact ⟨schauderBound_mono_space (subset_univ _) hv,
      holderBound_mono hvLow (fun p hp => ⟨mem_univ _,hp.2⟩),hv0,hvLat,hvEq,
      hv,hvLow,hvLat,hvEq,by intro x; trivial⟩
  | succ j ih =>
    intro hStop
    change gridTime h ((j+1)+1) ≤ T at hStop
    have hOldStop : gridTime h (j+1) ≤ T := by rw [gridTime_succ] at hStop; linarith
    obtain ⟨u,v,hu,huLow,hu0,huLat,huEq,hv,hvLow,hvLat,hvEq,hTerminal⟩ := ih hOldStop
    let τ : ℝ := gridTime h (j+1)
    have hτ : 0 < τ := gridTime_succ_pos hh j
    have hStep : h+τ ≤ T := by rw [gridTime_succ] at hStop; linarith
    have hOldτ : τ ∈ Icc (gridTime h j) (gridTime h (j+1)) := by
      refine ⟨?_,le_rfl⟩
      dsimp only [τ]
      rw [gridTime_succ]
      linarith
    obtain ⟨w,hw,hwLow,hw0,hwLat,hwEq⟩ := restart_from_ambient_segment hα hh hhδ hτ.le hStep hOldτ
      hShort hv hvLow hvEq hvLat ha hb hEll hf
    have hDBudget : segmentBudget (traceSourceBudget n M) Cs j*F+
        Cs*(F+traceSourceBudget n M*(segmentBudget (traceSourceBudget n M) Cs j*F)) =
        segmentBudget (traceSourceBudget n M) Cs (j+1)*F := by
      rw [segmentBudget]
      ring
    rw [hDBudget] at hw hwLow
    have hwX := schauderBound_mono_space (S := closure O) (subset_univ _) hw
    have hwLowX := holderBound_mono hwLow
      (show cylinder (closure O) τ (τ+h) ⊆ cylinder univ τ (τ+h) from
        fun p hp => ⟨mem_univ _,hp.2⟩)
    have hTrace : ∀ x, u (x,τ) = w (x,τ) := fun x => (hTerminal x).trans (hw0 x).symm
    have hPaste := timePaste_solution_space isClosed_closure hα hτ (by linarith : τ < τ+h)
      hu hwX huLow hwLowX hTrace huEq hwEq
    have hHBudget : 2*(historyBudget (traceSourceBudget n M) Cs j*F+
        segmentBudget (traceSourceBudget n M) Cs (j+1)*F) =
        historyBudget (traceSourceBudget n M) Cs (j+1)*F := by
      rw [historyBudget]
      ring
    have hHistSch := hPaste.1
    have hHistLow := hPaste.2.1
    rw [hHBudget] at hHistSch hHistLow
    refine ⟨timePaste τ u w,w,?_⟩
    change ContinuationState O α (traceSourceBudget n M) Cs h F a b f (j+1) (timePaste τ u w) w
    dsimp only [ContinuationState]
    rw [gridTime_succ h (j+1)]
    refine ⟨hHistSch,hHistLow,?_,?_,hPaste.2.2.2,hw,hwLow,hwLat,hwEq,hPaste.2.2.1⟩
    · intro x
      simp [timePaste,hτ.le,hu0]
    · intro x hx t ht
      by_cases htτ : t ≤ τ
      · simpa [timePaste,htτ] using huLat x hx t ⟨ht.1,htτ⟩
      · simpa [timePaste,htτ] using hwLat x hx t ⟨le_of_not_ge htτ,ht.2⟩

/-- A uniform compatible short-time solution theorem gives arbitrary fixed
time. The constant precedes every global coefficient field and source; the
result claims regularity only on the physical closed cylinder. -/
theorem arbitrary_time_of_compatible_ambient_short_inverse {n : ℕ} {O : Set (Space n)}
    {α lam upper M δ Cs : ℝ} (hα : 0 < α) (hM : 0 ≤ M) (hδ : 0 < δ) (hCs : 0 < Cs)
    (hShort : CompatibleAmbientShortInverse O α lam upper M δ Cs)
    {T : ℝ} (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ),
      HolderBound α (cylinder (closure O) 0 T) a M →
      (∀ i, HolderBound α (cylinder (closure O) 0 T) (fun p => b p i) M) →
      Elliptic (cylinder (closure O) 0 T) a lam upper →
      ∀ (f : Point n → ℝ) (F : ℝ), HolderBound α (cylinder (closure O) 0 T) f F →
      (∀ x ∈ frontier O, f (x,0) = 0) →
      ∃ u : Point n → ℝ, SchauderBound α (cylinder (closure O) 0 T) u (C*F) ∧
        HolderBound α (cylinder (closure O) 0 T) (fun p => (u p,spatialD u p)) (C*F) ∧
        (∀ x, u (x,0) = 0) ∧
        (∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, u (x,t) = 0) ∧
        ∀ p ∈ cylinder (closure O) 0 T,
          linearOp (cylinder (closure O) 0 T) a b u p = f p := by
  obtain ⟨N,hN⟩ := exists_nat_gt (T/δ)
  have hN0 : N ≠ 0 := by
    intro heq
    simp only [heq,Nat.cast_zero] at hN
    exact not_lt_of_ge (div_nonneg hT.le hδ.le) hN
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN0
  let h : ℝ := T/((m+1 : ℕ) : ℝ)
  have hh : 0 < h := by dsimp [h]; positivity
  have hhδ : h ≤ δ := by
    have hm : 0 < ((m+1 : ℕ) : ℝ) := by positivity
    have hmul : T < ((m+1 : ℕ) : ℝ)*δ := (div_lt_iff₀ hδ).mp hN
    exact (div_le_iff₀ hm).mpr (by linarith)
  have hTotal : gridTime h (m+1) = T := by dsimp [gridTime,h]; field_simp
  refine ⟨historyBudget (traceSourceBudget n M) Cs m,
    historyBudget_pos (traceSourceBudget_nonneg n hM) hCs m,?_⟩
  intro a b ha hb hEll f F hf hf0
  obtain ⟨u,v,hu,huLow,hu0,huLat,huEq,hv,hvLow,hvLat,hvEq,hTerminal⟩ :=
    exists_grid_continuation hα hh hhδ hShort ha hb hEll hf hf0 m hTotal.le
  refine ⟨u,?_,?_,hu0,?_,?_⟩
  · simpa only [hTotal] using hu
  · simpa only [hTotal] using huLow
  · simpa only [hTotal] using huLat
  · simpa only [hTotal] using huEq

end Yau.LeafProofs.L16BoundaryTimeAux
