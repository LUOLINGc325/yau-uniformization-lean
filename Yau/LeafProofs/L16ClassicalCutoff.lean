import Yau.LeafProofs.L16HolderOnlyInverse

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

theorem cylinder_subset_backward {n : ℕ} {R l r : ℝ} {O : Set (Space n)}
    (hO : O ⊆ Metric.ball 0 R) (hl : -(R^2) < l) (hr : r ≤ 0) :
    cylinder O l r ⊆ backward R := by
  intro p hp
  exact ⟨hO hp.1,hl.trans_le hp.2.1,hp.2.2.trans hr⟩

theorem timeD_backward_restrict {n : ℕ} {R l r : ℝ} {O : Set (Space n)}
    (hO : O ⊆ Metric.ball 0 R) (hl : -(R^2) < l) (hr : r ≤ 0) (hlr : l < r)
    {u : Point n → ℝ} (hu : C2 (backward R) u) {p : Point n}
    (hp : p ∈ cylinder O l r) :
    timeD (cylinder O l r) u p = timeD (backward R) u p := by
  have hSmall : {t | (p.1,t) ∈ cylinder O l r} = Set.Icc l r := by
    ext t
    simp [Yau.Parabolic.cylinder,hp.1]
  have hLarge : {t | (p.1,t) ∈ backward R} = Set.Ioc (-(R^2)) 0 := by
    ext t
    simp [backward,hO hp.1]
  simp only [timeD,hSmall,hLarge]
  have hSubset : Set.Icc l r ⊆ Set.Ioc (-(R^2)) 0 := by
    intro t ht
    exact ⟨hl.trans_le ht.1,ht.2.trans hr⟩
  apply derivWithin_subset hSubset (uniqueDiffOn_Icc hlr p.2 hp.2)
  simpa only [hLarge] using
    hu.2.2.2.2.2 p (cylinder_subset_backward hO hl hr hp)

theorem c2_backward_restrict {n : ℕ} {R l r : ℝ} {O : Set (Space n)}
    (hO : O ⊆ Metric.ball 0 R) (hl : -(R^2) < l) (hr : r ≤ 0) (hlr : l < r)
    {u : Point n → ℝ} (hu : C2 (backward R) u) :
    C2 (cylinder O l r) u := by
  have hs := cylinder_subset_backward hO hl hr
  refine ⟨hu.1.mono hs,hu.2.1.mono hs,hu.2.2.1.mono hs,?_,
    fun p hp => hu.2.2.2.2.1 p (hs hp),?_⟩
  · exact (hu.2.2.2.1.mono hs).congr
      (fun p hp => timeD_backward_restrict hO hl hr hlr hu hp)
  · intro p hp
    exact (hu.2.2.2.2.2 p (hs hp)).mono (fun t ht => hs ht)

theorem linearOp_backward_restrict {n : ℕ} {R l r : ℝ} {O : Set (Space n)}
    (hO : O ⊆ Metric.ball 0 R) (hl : -(R^2) < l) (hr : r ≤ 0) (hlr : l < r)
    {u : Point n → ℝ} (hu : C2 (backward R) u)
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
    {p : Point n} (hp : p ∈ cylinder O l r) :
    linearOp (cylinder O l r) a b u p = linearOp (backward R) a b u p := by
  simp only [linearOp,timeD_backward_restrict hO hl hr hlr hu hp]

theorem timeD_cylinder_change_space {n : ℕ} {l r : ℝ} {O S : Set (Space n)}
    (u : Point n → ℝ) {p : Point n} (hpO : p.1 ∈ O) (hpS : p.1 ∈ S) :
    timeD (cylinder O l r) u p = timeD (cylinder S l r) u p := by
  unfold timeD
  congr 1
  ext t
  simp [Yau.Parabolic.cylinder,hpO,hpS]

/-- A genuine spatial cutoff of a locally classical solution is classical
    on the whole slab, including outside the original spatial domain. -/
theorem c2_spatial_cutoff_extension {n : ℕ} {l r : ℝ} {O : Set (Space n)}
    (hO : IsOpen O) {φ : Space n → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hSupport : tsupport φ ⊆ O) {u : Point n → ℝ}
    (hu : C2 (cylinder O l r) u) :
    C2 (cylinder Set.univ l r) (fun p => φ p.1*u p) := by
  let Q : Set (Point n) := cylinder Set.univ l r
  let QO : Set (Point n) := cylinder O l r
  let w : Point n → ℝ := fun p => φ p.1*u p
  have hw : C2 QO w := c2_spatial_mul hφ hu
  have hZeroSlice (p : Point n) (hp : p.1 ∉ tsupport φ) :
      (fun x : Space n => w (x,p.2)) =ᶠ[𝓝 p.1] (fun _ => 0) := by
    have h := notMem_tsupport_iff_eventuallyEq.mp hp
    filter_upwards [h] with x hx
    change φ x*u (x,p.2) = 0
    simp only [Pi.zero_apply] at hx
    rw [hx,zero_mul]
  have hZeros (p : Point n) (hp : p.1 ∉ tsupport φ) :
      w p = 0 ∧ spatialD w p = 0 ∧ spatialDD w p = 0 ∧ timeD Q w p = 0 := by
    have hφ0 : φ p.1 = 0 := image_eq_zero_of_notMem_tsupport hp
    refine ⟨by dsimp only [w]; rw [hφ0,zero_mul],?_,?_,?_⟩
    · simpa only [spatialD,fderiv_fun_const,Pi.zero_apply] using (hZeroSlice p hp).fderiv_eq (𝕜 := ℝ)
    · simpa only [spatialDD,fderiv_fun_const,fderiv_zero,Pi.zero_apply] using
        ((hZeroSlice p hp).fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
    · change timeD Q (fun p => φ p.1*u p) p = 0
      rw [timeD_spatial_mul,hφ0,zero_mul]
  have hGlobalContinuous {V : Type} [NormedAddCommGroup V] (F : Point n → V)
      (hSmall : ContinuousOn F QO)
      (hZero : ∀ p : Point n, p.1 ∉ tsupport φ → F p = 0) :
      ContinuousOn F Q := by
    intro p hp
    by_cases hpS : p.1 ∈ tsupport φ
    · have hpO := hSupport hpS
      apply (hSmall p ⟨hpO,hp.2⟩).mono_of_mem_nhdsWithin
      have hNear : ∀ᶠ q : Point n in 𝓝 p, q.1 ∈ O :=
        (hO.preimage continuous_fst).mem_nhds hpO
      filter_upwards [self_mem_nhdsWithin,hNear.filter_mono nhdsWithin_le_nhds] with q hq hqO
      exact ⟨hqO,hq.2⟩
    · have hNear : ∀ᶠ q : Point n in 𝓝 p, q.1 ∉ tsupport φ :=
        (isClosed_tsupport φ).isOpen_compl.preimage continuous_fst |>.mem_nhds hpS
      apply (continuousWithinAt_const (b := (0 : V))).congr_of_eventuallyEq _ (hZero p hpS)
      filter_upwards [hNear.filter_mono nhdsWithin_le_nhds] with q hq
      exact hZero q hq
  have hTimeSmall : ContinuousOn (timeD Q w) QO := by
    apply hw.2.2.2.1.congr
    intro p hp
    exact timeD_cylinder_change_space w (Set.mem_univ p.1) hp.1
  refine ⟨hGlobalContinuous w hw.1 (fun p hp => (hZeros p hp).1),
    hGlobalContinuous (spatialD w) hw.2.1 (fun p hp => (hZeros p hp).2.1),
    hGlobalContinuous (spatialDD w) hw.2.2.1 (fun p hp => (hZeros p hp).2.2.1),
    hGlobalContinuous (timeD Q w) hTimeSmall (fun p hp => (hZeros p hp).2.2.2),?_,?_⟩
  · intro p hp
    by_cases hpS : p.1 ∈ tsupport φ
    · exact hw.2.2.2.2.1 p ⟨hSupport hpS,hp.2⟩
    · exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq (hZeroSlice p hpS)
  · intro p hp
    by_cases hpS : p.1 ∈ tsupport φ
    · have hpO := hSupport hpS
      have h := hw.2.2.2.2.2 p ⟨hpO,hp.2⟩
      convert h using 1
      ext t
      simp [QO,Yau.Parabolic.cylinder,hpO]
    · have hφ0 : φ p.1 = 0 := image_eq_zero_of_notMem_tsupport hpS
      have hEq : (fun t : ℝ => w (p.1,t)) = fun _ => 0 := by
        funext t
        change φ p.1*u (p.1,t) = 0
        rw [hφ0,zero_mul]
      rw [hEq]
      exact differentiableWithinAt_const 0

end Yau.LeafProofs.L16Aux
