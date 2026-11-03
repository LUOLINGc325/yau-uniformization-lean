import Yau.LeafProofs.L16DirichletKernel
import Yau.LeafProofs.L16ResidualEstimates

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1000000
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

/-- Orthogonal projection onto the actual flat boundary. -/
def halfSpaceBoundaryProjection {n : ℕ} (e : Space n) : Space n →L[ℝ] Space n :=
  (ℝ ∙ e)ᗮ.starProjection

theorem halfSpaceBoundaryProjection_normal {n : ℕ} (e x : Space n) :
    inner ℝ e (halfSpaceBoundaryProjection e x) = 0 := by
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp
    (Submodule.starProjection_apply_mem (ℝ ∙ e)ᗮ x)

theorem halfSpaceBoundaryProjection_apply {n : ℕ} {e : Space n} (he : ‖e‖ = 1)
    (x : Space n) : halfSpaceBoundaryProjection e x = x - (inner ℝ e x) • e := by
  rw [halfSpaceBoundaryProjection, Submodule.starProjection_orthogonal]
  simp only [sub_apply, ContinuousLinearMap.id_apply,
    Submodule.starProjection_singleton, he, RCLike.ofReal_real_eq_id, id_eq,
    one_pow, div_one]

theorem halfSpaceBoundaryProjection_distance {n : ℕ} {e : Space n} (he : ‖e‖ = 1)
    (x : Space n) : ‖x-halfSpaceBoundaryProjection e x‖ = |inner ℝ e x| := by
  rw [halfSpaceBoundaryProjection_apply he]
  simp only [sub_sub_cancel, norm_smul, Real.norm_eq_abs, he, mul_one]

theorem halfSpaceBoundaryProjection_nonexpansive {n : ℕ} (e : Space n) (x y : Space n) :
    ‖halfSpaceBoundaryProjection e x-halfSpaceBoundaryProjection e y‖ ≤ ‖x-y‖ := by
  rw [← map_sub]
  exact Submodule.norm_starProjection_apply_le _ _

theorem holderBound_halfSpace_boundary_trace {n : ℕ} {α F : ℝ} {I : Set ℝ}
    {e : Space n} {f : Point n → ℝ} (hα : 0 ≤ α)
    (hf : HolderBound α ({x : Space n | 0 ≤ inner ℝ e x} ×ˢ I) f F) :
    HolderBound α (Set.univ ×ˢ I)
      (fun p => f (halfSpaceBoundaryProjection e p.1,p.2)) F := by
  have hMem (p : Point n) (hp : p ∈ Set.univ ×ˢ I) :
      (halfSpaceBoundaryProjection e p.1,p.2) ∈ {x : Space n | 0 ≤ inner ℝ e x} ×ˢ I := by
    exact ⟨by simp only [Set.mem_ofPred_eq, halfSpaceBoundaryProjection_normal, le_refl],hp.2⟩
  refine ⟨hf.1,fun p hp => hf.2.1 _ (hMem p hp),?_⟩
  intro p hp q hq
  apply (hf.2.2 _ (hMem p hp) _ (hMem q hq)).trans
  apply mul_le_mul_of_nonneg_left _ hf.1
  change ‖halfSpaceBoundaryProjection e p.1-halfSpaceBoundaryProjection e q.1‖^α +
    |p.2-q.2|^(α/2) ≤ ‖p.1-q.1‖^α+|p.2-q.2|^(α/2)
  exact add_le_add (Real.rpow_le_rpow (norm_nonneg _)
    (halfSpaceBoundaryProjection_nonexpansive e p.1 q.1) hα) le_rfl

theorem zero_boundary_holder_value_bound {n : ℕ} {α F : ℝ} {I : Set ℝ}
    {e : Space n} (he : ‖e‖ = 1) (hα : 0 < α) {g : Point n → ℝ}
    (hg : HolderBound α ({x : Space n | 0 ≤ inner ℝ e x} ×ˢ I) g F)
    (hz : ∀ x : Space n, inner ℝ e x = 0 → ∀ t ∈ I, g (x,t) = 0)
    {p : Point n} (hp : p ∈ {x : Space n | 0 ≤ inner ℝ e x} ×ˢ I) :
    |g p| ≤ F*|inner ℝ e p.1|^α := by
  have hProj : (halfSpaceBoundaryProjection e p.1,p.2) ∈
      {x : Space n | 0 ≤ inner ℝ e x} ×ˢ I := by
    exact ⟨by simp only [Set.mem_ofPred_eq,halfSpaceBoundaryProjection_normal,le_refl],hp.2⟩
  have h := hg.2.2 p hp _ hProj
  rw [hz _ (halfSpaceBoundaryProjection_normal _ _) _ hp.2] at h
  simpa only [sub_zero,Real.norm_eq_abs,holderWeight,halfSpaceBoundaryProjection_distance he,
    sub_self,abs_zero,Real.zero_rpow (by positivity : α/2 ≠ 0),add_zero] using h


theorem normal_opposite_bounds {n : ℕ} {e x y : Space n} (he : ‖e‖ = 1)
    (hx : 0 ≤ inner ℝ e x) (hy : inner ℝ e y ≤ 0) :
    |inner ℝ e x| ≤ ‖x-y‖ ∧ |inner ℝ e y| ≤ ‖x-y‖ := by
  have h := abs_real_inner_le_norm e (x-y)
  rw [he,one_mul,inner_sub_right,abs_of_nonneg (by linarith)] at h
  rw [abs_of_nonneg hx,abs_of_nonpos hy]
  constructor <;> linarith

/-- Odd reflection is applied only to an actual zero-boundary source. -/
def halfSpaceOddExtension {n : ℕ} (e : Space n) (g : Point n → ℝ) : Point n → ℝ :=
  fun p => if 0 ≤ inner ℝ e p.1 then g p else -g (halfSpaceReflection e p.1,p.2)

theorem zero_boundary_holder_cross_bound {n : ℕ} {α F : ℝ} {I : Set ℝ}
    {e : Space n} (he : ‖e‖ = 1) (hα : 0 < α) {g : Point n → ℝ}
    (hg : HolderBound α ({x : Space n | 0 ≤ inner ℝ e x} ×ˢ I) g F)
    (hz : ∀ x : Space n, inner ℝ e x = 0 → ∀ t ∈ I, g (x,t) = 0)
    {p q : Point n} (hp : 0 ≤ inner ℝ e p.1) (hq : inner ℝ e q.1 ≤ 0)
    (hpt : p.2 ∈ I) (hqt : q.2 ∈ I) :
    |g p+g (halfSpaceReflection e q.1,q.2)| ≤ 2*F*holderWeight α p q := by
  have hRp : (halfSpaceReflection e q.1,q.2) ∈ {x : Space n | 0 ≤ inner ℝ e x} ×ˢ I :=
    ⟨by rw [Set.mem_ofPred_eq,halfSpaceReflection_normal he]; linarith,hqt⟩
  have hP := zero_boundary_holder_value_bound he hα hg hz (p := p) ⟨hp,hpt⟩
  have hQ := zero_boundary_holder_value_bound he hα hg hz (p := (halfSpaceReflection e q.1,q.2)) hRp
  rw [halfSpaceReflection_normal he,abs_neg] at hQ
  obtain ⟨hX,hY⟩ := normal_opposite_bounds he hp hq
  have hXP := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (abs_nonneg _) hX hα.le) hg.1
  have hYP := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (abs_nonneg _) hY hα.le) hg.1
  have hW : ‖p.1-q.1‖^α ≤ holderWeight α p q := by
    dsimp only [holderWeight]
    linarith [Real.rpow_nonneg (abs_nonneg (p.2-q.2)) (α/2)]
  calc
    |g p+g (halfSpaceReflection e q.1,q.2)| ≤ |g p|+|g (halfSpaceReflection e q.1,q.2)| := abs_add_le _ _
    _ ≤ 2*F*‖p.1-q.1‖^α := by linarith
    _ ≤ 2*F*holderWeight α p q := mul_le_mul_of_nonneg_left hW (mul_nonneg (by norm_num) hg.1)


theorem holderBound_halfSpace_odd_extension {n : ℕ} {α F : ℝ} {I : Set ℝ}
    {e : Space n} (he : ‖e‖ = 1) (hα : 0 < α) {g : Point n → ℝ}
    (hg : HolderBound α ({x : Space n | 0 ≤ inner ℝ e x} ×ˢ I) g F)
    (hz : ∀ x : Space n, inner ℝ e x = 0 → ∀ t ∈ I, g (x,t) = 0) :
    HolderBound α (Set.univ ×ˢ I) (halfSpaceOddExtension e g) (2*F) := by
  have hF : 0 ≤ F := hg.1
  have hRMem (p : Point n) (hp : p.2 ∈ I) (hpn : inner ℝ e p.1 ≤ 0) :
      (halfSpaceReflection e p.1,p.2) ∈ {x : Space n | 0 ≤ inner ℝ e x} ×ˢ I := by
    exact ⟨by rw [Set.mem_ofPred_eq,halfSpaceReflection_normal he]; linarith,hp⟩
  have hWeight (p q : Point n) :
      holderWeight α (halfSpaceReflection e p.1,p.2) (halfSpaceReflection e q.1,q.2) =
        holderWeight α p q := by
    simp only [holderWeight, ← map_sub, (halfSpaceReflection e).norm_map]
  have hScale (p q : Point n) :
      F*holderWeight α p q ≤ (2*F)*holderWeight α p q := by
    have hW : 0 ≤ holderWeight α p q := by dsimp only [holderWeight]; positivity
    nlinarith
  refine ⟨by positivity,?_,?_⟩
  · intro p hp
    by_cases hpn : 0 ≤ inner ℝ e p.1
    · rw [halfSpaceOddExtension,ite_eq_left hpn]
      exact (hg.2.1 p ⟨hpn,hp.2⟩).trans (by linarith)
    · rw [halfSpaceOddExtension,ite_eq_right hpn,norm_neg]
      exact (hg.2.1 _ (hRMem p hp.2 (le_of_lt (lt_of_not_ge hpn)))).trans (by linarith)
  · intro p hp q hq
    by_cases hpn : 0 ≤ inner ℝ e p.1 <;> by_cases hqn : 0 ≤ inner ℝ e q.1
    · rw [halfSpaceOddExtension,ite_eq_left hpn,halfSpaceOddExtension,ite_eq_left hqn]
      exact (hg.2.2 p ⟨hpn,hp.2⟩ q ⟨hqn,hq.2⟩).trans (hScale p q)
    · rw [halfSpaceOddExtension,ite_eq_left hpn,halfSpaceOddExtension,ite_eq_right hqn]
      simpa only [sub_neg_eq_add,Real.norm_eq_abs] using
        zero_boundary_holder_cross_bound he hα hg hz hpn (le_of_lt (lt_of_not_ge hqn)) hp.2 hq.2
    · rw [halfSpaceOddExtension,ite_eq_right hpn,halfSpaceOddExtension,ite_eq_left hqn]
      have hCross := zero_boundary_holder_cross_bound he hα hg hz hqn
        (le_of_lt (lt_of_not_ge hpn)) hq.2 hp.2
      have hSym : holderWeight α q p = holderWeight α p q := by
        simp only [holderWeight,norm_sub_rev,abs_sub_comm]
      rw [hSym] at hCross
      have hEq : -g (halfSpaceReflection e p.1,p.2)-g q =
          -(g q+g (halfSpaceReflection e p.1,p.2)) := by ring
      simpa only [hEq,Real.norm_eq_abs,abs_neg] using hCross
    · rw [halfSpaceOddExtension,ite_eq_right hpn,halfSpaceOddExtension,ite_eq_right hqn]
      have hPair := hg.2.2 _ (hRMem p hp.2 (le_of_lt (lt_of_not_ge hpn)))
        _ (hRMem q hq.2 (le_of_lt (lt_of_not_ge hqn)))
      rw [hWeight] at hPair
      have hEq : -g (halfSpaceReflection e p.1,p.2)- -g (halfSpaceReflection e q.1,q.2) =
          -(g (halfSpaceReflection e p.1,p.2)-g (halfSpaceReflection e q.1,q.2)) := by ring
      simpa only [hEq,norm_neg] using hPair.trans (hScale p q)


def halfSpaceZeroTraceResidual {n : ℕ} (e : Space n) (f : Point n → ℝ) : Point n → ℝ :=
  fun p => f p-f (halfSpaceBoundaryProjection e p.1,p.2)

theorem halfSpaceZeroTraceResidual_boundary {n : ℕ} {e : Space n} (he : ‖e‖ = 1)
    (f : Point n → ℝ) {x : Space n} (hx : inner ℝ e x = 0) (t : ℝ) :
    halfSpaceZeroTraceResidual e f (x,t) = 0 := by
  simp only [halfSpaceZeroTraceResidual,halfSpaceBoundaryProjection_apply he,hx,
    zero_smul,sub_zero,sub_self]

theorem holderBound_halfSpace_zero_trace_residual {n : ℕ} {α F : ℝ} {I : Set ℝ}
    {e : Space n} {f : Point n → ℝ} (hα : 0 ≤ α)
    (hf : HolderBound α ({x : Space n | 0 ≤ inner ℝ e x} ×ˢ I) f F) :
    HolderBound α ({x : Space n | 0 ≤ inner ℝ e x} ×ˢ I)
      (halfSpaceZeroTraceResidual e f) (2*F) := by
  have hTrace := holderBound_mono (holderBound_halfSpace_boundary_trace hα hf)
    (show {x : Space n | 0 ≤ inner ℝ e x} ×ˢ I ⊆ Set.univ ×ˢ I from
      fun p hp => ⟨Set.mem_univ _,hp.2⟩)
  change HolderBound α _ (fun p => f p-f (halfSpaceBoundaryProjection e p.1,p.2)) (2*F)
  simpa only [two_mul] using holderBound_sub hf hTrace

theorem holderBound_halfSpace_zero_trace_odd_extension {n : ℕ} {α F : ℝ} {I : Set ℝ}
    {e : Space n} (he : ‖e‖ = 1) (hα : 0 < α) {f : Point n → ℝ}
    (hf : HolderBound α ({x : Space n | 0 ≤ inner ℝ e x} ×ˢ I) f F) :
    HolderBound α (Set.univ ×ˢ I)
      (halfSpaceOddExtension e (halfSpaceZeroTraceResidual e f)) (4*F) := by
  have hZero : ∀ x : Space n, inner ℝ e x = 0 → ∀ t ∈ I,
      halfSpaceZeroTraceResidual e f (x,t) = 0 := by
    intro x hx t _ht
    exact halfSpaceZeroTraceResidual_boundary he f hx t
  convert holderBound_halfSpace_odd_extension he hα
    (holderBound_halfSpace_zero_trace_residual hα.le hf) hZero using 1; ring

theorem halfSpaceOddExtension_antireflection {n : ℕ} {e : Space n}
    (he : ‖e‖ = 1) {I : Set ℝ} {g : Point n → ℝ}
    (hz : ∀ x : Space n, inner ℝ e x = 0 → ∀ t ∈ I, g (x,t) = 0)
    (x : Space n) {t : ℝ} (ht : t ∈ I) :
    halfSpaceOddExtension e g (halfSpaceReflection e x,t) =
      -halfSpaceOddExtension e g (x,t) := by
  by_cases hx : 0 ≤ inner ℝ e x
  · by_cases hx0 : inner ℝ e x = 0
    · rw [halfSpaceReflection_boundary he hx0]
      simp only [halfSpaceOddExtension,ite_eq_left hx,hz x hx0 t ht,neg_zero]
    · have hR : ¬0 ≤ inner ℝ e (halfSpaceReflection e x) := by
        rw [halfSpaceReflection_normal he]
        linarith [lt_of_le_of_ne hx (Ne.symm hx0)]
      simp only [halfSpaceOddExtension,ite_eq_right hR,ite_eq_left hx,
        halfSpaceReflection_twice]
  · have hR : 0 ≤ inner ℝ e (halfSpaceReflection e x) := by
      rw [halfSpaceReflection_normal he]
      linarith
    simp only [halfSpaceOddExtension,ite_eq_left hR,ite_eq_right hx,neg_neg]


theorem heatAverage_halfSpace_odd_extension_boundary {n : ℕ} {e : Space n}
    (he : ‖e‖ = 1) {I : Set ℝ} {g : Point n → ℝ}
    (hz : ∀ x : Space n, inner ℝ e x = 0 → ∀ t ∈ I, g (x,t) = 0)
    {x : Space n} (hx : inner ℝ e x = 0) {t : ℝ} (ht : t ∈ I) (s : ℝ) :
    heatAverage s (fun y => halfSpaceOddExtension e g (y,t)) x = 0 := by
  let R := halfSpaceReflection e
  let v : Space n → ℝ := fun y => halfSpaceOddExtension e g (y,t)
  have hOdd (y : Space n) : v (R y) = -v y :=
    halfSpaceOddExtension_antireflection he hz y ht
  have hG (y : Space n) : gaussianKernel s (R y) = gaussianKernel s y := by
    simp only [gaussianKernel,R,(halfSpaceReflection e).norm_map]
  have hShift (y : Space n) : x-R y = R (x-y) := by
    rw [map_sub,halfSpaceReflection_boundary he hx]
  have hIntegral := R.measurePreserving.integral_comp
    R.toHomeomorph.measurableEmbedding (fun y => gaussianKernel s y*v (x-y))
  have hReflect : (fun y : Space n => gaussianKernel s (R y)*v (x-R y)) =
      fun y => -(gaussianKernel s y*v (x-y)) := by
    funext y
    rw [hG,hShift,hOdd,mul_neg]
  rw [hReflect,integral_neg] at hIntegral
  change -(heatAverage s v x) = heatAverage s v x at hIntegral
  change heatAverage s v x = 0
  linarith

theorem heatDuhamel_halfSpace_odd_extension_boundary {n : ℕ} {e : Space n}
    (he : ‖e‖ = 1) {T : ℝ} {g : Point n → ℝ}
    (hz : ∀ x : Space n, inner ℝ e x = 0 → ∀ t ∈ Set.Icc 0 T, g (x,t) = 0)
    {x : Space n} (hx : inner ℝ e x = 0) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    heatDuhamel (halfSpaceOddExtension e g) t x = 0 := by
  rw [heatDuhamel]
  have hEq : (∫ s in (0 : ℝ)..t,
      heatAverage (t-s) (fun y => halfSpaceOddExtension e g (y,s)) x) =
      ∫ _s in (0 : ℝ)..t, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le ht.1] at hs
    exact heatAverage_halfSpace_odd_extension_boundary he hz hx ⟨hs.1,hs.2.trans ht.2⟩ (t-s)
  exact hEq.trans intervalIntegral.integral_zero


/-- The zero-boundary residual is solved by the already proved genuine
    full-space heat potential. Only the boundary-trace layer remains. -/
theorem halfSpace_zero_trace_residual_schauder_solution {n : ℕ} {e : Space n}
    (he : ‖e‖ = 1) {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T F : ℝ, 0 < T → T ≤ 1 → ∀ f : Point n → ℝ,
      HolderBound α (cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T) f F →
      let u : Point n → ℝ := fun p => heatDuhamel
        (halfSpaceOddExtension e (halfSpaceZeroTraceResidual e f)) p.2 p.1
      SchauderBound α (cylinder Set.univ 0 T) u (C*F) ∧
      (∀ x : Space n, u (x,0) = 0) ∧
      (∀ x : Space n, inner ℝ e x = 0 → ∀ t ∈ Set.Icc 0 T, u (x,t) = 0) ∧
      ∀ p ∈ cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T,
        linearOp (cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T)
          (fun _ => (1 : Mat n)) (fun _ _ => 0) u p = halfSpaceZeroTraceResidual e f p := by
  obtain ⟨C,hC,hSolve⟩ := heatDuhamel_schauder_solution (n := n) hα hα1
  refine ⟨4*C,by positivity,?_⟩
  intro T F hT hT1 f hf
  dsimp only
  have hExt : HolderBound α (cylinder Set.univ 0 T)
      (halfSpaceOddExtension e (halfSpaceZeroTraceResidual e f)) (4*F) :=
    holderBound_halfSpace_zero_trace_odd_extension he hα hf
  obtain ⟨hu,hInit,hPDE⟩ := hSolve T (4*F) hT hT1 _ hExt
  have hBudget : C*(4*F) = (4*C)*F := by ring
  rw [hBudget] at hu
  refine ⟨hu,hInit,?_,?_⟩
  · intro x hx t ht
    apply heatDuhamel_halfSpace_odd_extension_boundary he _ hx ht
    intro y hy s _hs
    exact halfSpaceZeroTraceResidual_boundary he f hy s
  · intro p hp
    rw [linearOp_cylinder_restrict_space (hp := hp)]
    rw [hPDE p ⟨Set.mem_univ _,hp.2⟩]
    exact ite_eq_left hp.1

end Yau.LeafProofs.L16Aux
