import spec.CHAIN.LeafObligations
import Yau.LeafProofs.L16Localization
import Yau.LeafProofs.L16Normalization
import Mathlib.Topology.MetricSpace.Contracting

/-! Internal lemmas for the eight frozen parabolic leaf obligations. -/

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

noncomputable section

namespace Yau.LeafProofs.L16Aux

open Yau.Parabolic Yau.ParabolicCandidates

theorem spatialD_zero {n : ℕ} : spatialD (n := n) (fun _ => 0) = fun _ => 0 := by
  funext p
  simp [spatialD]

theorem spatialDD_zero {n : ℕ} : spatialDD (n := n) (fun _ => 0) = fun _ => 0 := by
  funext p
  simp [spatialDD]

theorem timeD_zero {n : ℕ} (Q : Set (Point n)) :
    timeD Q (fun _ => 0) = fun _ => 0 := by
  funext p
  simp [timeD]

theorem c2_zero {n : ℕ} (Q : Set (Point n)) : C2 Q (fun _ => 0) := by
  simp only [C2, spatialD_zero, spatialDD_zero, timeD_zero, continuousOn_const,
    contDiffAt_const, differentiableWithinAt_const, implies_true, and_self]

theorem schauderBound_zero {n : ℕ} (α : ℝ) (Q : Set (Point n)) :
    SchauderBound α Q (fun _ => 0) 0 := by
  simp [SchauderBound, c2_zero, spatialD_zero, spatialDD_zero, timeD_zero,
    HolderBound]
  constructor
  · intro x t ht
    exact ContinuousLinearMap.opNorm_zero.le
  · intro x t ht y s hs
    exact ContinuousLinearMap.opNorm_zero.le

theorem linearOp_zero {n : ℕ} (Q : Set (Point n)) (a : Point n → Mat n)
    (b : Point n → Yau.RIdx n → ℝ) (p : Point n) :
    linearOp Q a b (fun _ => 0) p = 0 := by
  simp [linearOp, timeD_zero, spatialD_zero, spatialDD_zero]

theorem holderBound_mono {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    {α C : ℝ} {Q S : Set (Point n)} {f : Point n → V}
    (h : HolderBound α Q f C) (hSQ : S ⊆ Q) : HolderBound α S f C :=
  ⟨h.1, fun p hp => h.2.1 p (hSQ hp),
    fun p hp q hq => h.2.2 p (hSQ hp) q (hSQ hq)⟩

theorem cylinder_mono_time {n : ℕ} {O : Set (Space n)} {ε T : ℝ}
    (hεT : ε ≤ T) : cylinder O 0 ε ⊆ cylinder O 0 T := by
  rintro p ⟨hp, hl, hr⟩
  exact ⟨hp, hl, hr.trans hεT⟩

theorem timeD_cylinder_restrict {n : ℕ} {O : Set (Space n)} {ε T : ℝ}
    {u : Point n → ℝ} (hε : 0 < ε) (hεT : ε ≤ T)
    (hu : C2 (cylinder O 0 T) u) {p : Point n} (hp : p ∈ cylinder O 0 ε) :
    timeD (cylinder O 0 ε) u p = timeD (cylinder O 0 T) u p := by
  have hf : {t | (p.1, t) ∈ cylinder O 0 ε} = Set.Icc 0 ε := by
    ext t
    simp [Yau.Parabolic.cylinder, hp.1]
  have hF : {t | (p.1, t) ∈ cylinder O 0 T} = Set.Icc 0 T := by
    ext t
    simp [Yau.Parabolic.cylinder, hp.1]
  simp only [timeD, hf, hF]
  apply derivWithin_subset (Set.Icc_subset_Icc le_rfl hεT)
    (uniqueDiffOn_Icc hε p.2 hp.2)
  simpa only [hF] using hu.2.2.2.2.2 p (cylinder_mono_time hεT hp)

theorem c2_cylinder_restrict {n : ℕ} {O : Set (Space n)} {ε T : ℝ}
    {u : Point n → ℝ} (hε : 0 < ε) (hεT : ε ≤ T)
    (hu : C2 (cylinder O 0 T) u) : C2 (cylinder O 0 ε) u := by
  have hs := cylinder_mono_time (O := O) hεT
  refine ⟨hu.1.mono hs, hu.2.1.mono hs, hu.2.2.1.mono hs, ?_,
    fun p hp => hu.2.2.2.2.1 p (hs hp), ?_⟩
  · apply (hu.2.2.2.1.mono hs).congr
    intro p hp
    exact timeD_cylinder_restrict hε hεT hu hp
  · intro p hp
    exact (hu.2.2.2.2.2 p (hs hp)).mono (fun t ht => hs ht)

theorem schauderBound_cylinder_restrict {n : ℕ} {O : Set (Space n)}
    {α C ε T : ℝ} {u : Point n → ℝ} (hε : 0 < ε) (hεT : ε ≤ T)
    (hu : SchauderBound α (cylinder O 0 T) u C) :
    SchauderBound α (cylinder O 0 ε) u C := by
  have hs := cylinder_mono_time (O := O) hεT
  refine ⟨c2_cylinder_restrict hε hεT hu.1, hu.2.1,
    fun p hp => hu.2.2.1 p (hs hp), holderBound_mono hu.2.2.2.1 hs, ?_⟩
  have he : ∀ p ∈ cylinder O 0 ε,
      timeD (cylinder O 0 ε) u p = timeD (cylinder O 0 T) u p :=
    fun p hp => timeD_cylinder_restrict hε hεT hu.1 hp
  refine ⟨hu.2.2.2.2.1, ?_, ?_⟩
  · intro p hp
    rw [he p hp]
    exact hu.2.2.2.2.2.1 p (hs hp)
  · intro p hp q hq
    rw [he p hp, he q hq]
    exact hu.2.2.2.2.2.2 p (hs hp) q (hs hq)

theorem linearOp_cylinder_restrict {n : ℕ} {O : Set (Space n)}
    {ε T : ℝ} {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    {u : Point n → ℝ} (hε : 0 < ε) (hεT : ε ≤ T)
    (hu : C2 (cylinder O 0 T) u) {p : Point n} (hp : p ∈ cylinder O 0 ε) :
    linearOp (cylinder O 0 ε) a b u p = linearOp (cylinder O 0 T) a b u p := by
  simp only [linearOp, timeD_cylinder_restrict hε hεT hu hp]

theorem holderBound_terminalExtension {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    {O : Set (Space n)} {α ε T F : ℝ} {f : Point n → V}
    (hα : 0 ≤ α) (hε : 0 ≤ ε)
    (hf : HolderBound α (cylinder O 0 ε) f F) :
    HolderBound α (cylinder O 0 T) (fun p => f (p.1, min p.2 ε)) F := by
  have hmem : ∀ p ∈ cylinder O 0 T, (p.1, min p.2 ε) ∈ cylinder O 0 ε := by
    intro p hp
    exact ⟨hp.1, le_min hp.2.1 hε, min_le_right _ _⟩
  refine ⟨hf.1, fun p hp => hf.2.1 _ (hmem p hp), ?_⟩
  intro p hp q hq
  apply (hf.2.2 _ (hmem p hp) _ (hmem q hq)).trans
  apply mul_le_mul_of_nonneg_left _ hf.1
  simp only [holderWeight]
  apply add_le_add_right
  apply Real.rpow_le_rpow (abs_nonneg _) _ (div_nonneg hα (by norm_num))
  have hdist := abs_min_sub_min_le_max p.2 ε q.2 ε
  simpa using hdist

/-- Fixed-horizon terminal extension gives the entire `0 < ε ≤ T` range
with one constant. The compatible Dirichlet theorem remains an explicit
dependency of this bridge. -/
theorem uniformSmallTimeInverse_of_compatibleDirichletSchauder
    (h : CompatibleDirichletSchauder) : UniformSmallTimeInverse := by
  intro n hn O hO T α lam upper M hT hα hα1 hM a b
  dsimp only
  intro hEll hA hb
  obtain ⟨C, hC, hsol⟩ := h n hn O hO T α lam upper M hT hα hα1 hM
    a b hEll hA hb
  refine ⟨C, hC, ?_⟩
  intro ε hε hεT f F hf hf0
  let fhat : Point n → ℝ := fun p => f (p.1, min p.2 ε)
  have hfhat : HolderBound α (cylinder (closure O) 0 T) fhat F :=
    holderBound_terminalExtension hα.le hε.le hf
  have hcompat : Compatible O T a b fhat (fun _ => 0) := by
    intro x hx
    rw [linearOp_zero]
    simp only [fhat, min_eq_left hε.le]
    exact (hf0 x (frontier_subset_closure hx)).symm
  obtain ⟨u, hu, hdata, heq, _⟩ := hsol fhat (fun _ => 0) F 0 hfhat
    (schauderBound_zero α (cylinder (closure O) 0 T)) hcompat
  have hu' : SchauderBound α (cylinder (closure O) 0 T) u (C * F) := by
    simpa only [add_zero] using hu
  refine ⟨u, schauderBound_cylinder_restrict hε hεT hu', ?_, ?_⟩
  · refine ⟨hdata.1, ?_⟩
    intro x hx t ht
    exact hdata.2 x hx t ⟨ht.1, ht.2.trans hεT⟩
  · intro z hz
    have hz' : z ∈ cylinder (closure O) 0 ε := ⟨subset_closure hz.1, hz.2⟩
    rw [linearOp_cylinder_restrict hε hεT hu'.1 hz',
      heq z (cylinder_mono_time hεT hz)]
    exact congrArg f (Prod.ext rfl (min_eq_left hz.2.2))

/-- The volume conversion uses the actual real Haar measure and dimension. -/
theorem exteriorMeasure_of_uniformExteriorBalls {n : ℕ} {O : Set (Space n)}
    {c r0 : ℝ} (hc : 0 < c) (hr0 : 0 < r0)
    (hballs : ∀ x ∈ frontier O, ∀ r : ℝ, 0 < r → r ≤ r0 →
      ∃ y : Space n, Metric.ball y (c*r) ⊆ Metric.ball x r \ O) :
    ∃ θ r0 : ℝ, 0 < θ ∧ 0 < r0 ∧ ∀ x ∈ frontier O, ∀ r : ℝ,
      0 < r → r ≤ r0 →
        ENNReal.ofReal θ * volume (Metric.ball x r) ≤ volume (Metric.ball x r \ O) := by
  refine ⟨c ^ Module.finrank ℝ (Space n), r0, pow_pos hc _, hr0, ?_⟩
  intro x hx r hr hrr0
  obtain ⟨y, hy⟩ := hballs x hx r hr hrr0
  calc
    ENNReal.ofReal (c ^ Module.finrank ℝ (Space n)) * volume (Metric.ball x r) =
        volume (Metric.ball y (c*r)) := by
      rw [Measure.addHaar_ball_center volume x r,
        Measure.addHaar_ball_mul_of_pos volume y hc r]
    _ ≤ volume (Metric.ball x r \ O) := measure_mono hy

/-- Strict differentiability controls increments between any two points of
one neighborhood, which is the uniformity needed at nearby boundary points. -/
theorem strict_remainder_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ρ : E → ℝ} {L : E →L[ℝ] ℝ} {x : E} (h : HasStrictFDerivAt ρ L x)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℝ, 0 < R ∧ ∀ y ∈ Metric.ball x R, ∀ z ∈ Metric.ball x R,
      |ρ z - ρ y - L (z-y)| ≤ δ * ‖z-y‖ := by
  obtain ⟨R, hR, hbound⟩ := Metric.mem_nhds_iff.mp (h.isLittleO.def hδ)
  refine ⟨R, hR, ?_⟩
  intro y hy z hz
  have hp : (z,y) ∈ Metric.ball (x,x) R := by
    simpa only [Metric.mem_ball, Prod.dist_eq, max_lt_iff] using
      And.intro hz hy
  simpa [Real.norm_eq_abs] using hbound hp

theorem definingFunction_zero_on_frontier {E : Type*} [TopologicalSpace E]
    {O V : Set E} {ρ : E → ℝ} (hO : IsOpen O) (hV : IsOpen V)
    (hρ : ContinuousOn ρ V) (hdef : O ∩ V = {y | y ∈ V ∧ ρ y < 0})
    {y : E} (hy : y ∈ frontier O) (hyV : y ∈ V) : ρ y = 0 := by
  have hn : y ∉ O := by
    intro hyO
    exact hy.2 (by simpa only [hO.interior_eq] using hyO)
  have hnonneg : 0 ≤ ρ y := by
    by_contra hneg
    exact hn (((Set.ext_iff.mp hdef y).mpr ⟨hyV, lt_of_not_ge hneg⟩).1)
  have hycl : y ∈ closure (O ∩ V) := by
    apply mem_closure_iff.mpr
    intro U hU hyU
    obtain ⟨z, hzUV, hzO⟩ := mem_closure_iff.mp (frontier_subset_closure hy)
      (U ∩ V) (hU.inter hV) ⟨hyU, hyV⟩
    exact ⟨z, hzUV.1, hzO, hzUV.2⟩
  have hnonpos : ρ y ≤ 0 := by
    apply ContinuousWithinAt.closure_le hycl
      (hρ.continuousAt (hV.mem_nhds hyV)).continuousWithinAt continuousWithinAt_const
    intro z hz
    exact (((Set.ext_iff.mp hdef z).mp hz).2).le
  exact le_antisymm hnonpos hnonneg

/-- A quantitative half-space cone contains a ball with radius proportional
to the original radius. All hypotheses are concrete increment estimates. -/
theorem shifted_ball_positive {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ρ : E → ℝ} {L : E →L[ℝ] ℝ} {w y z : E} {a c r : ℝ}
    (hw : L w = 1) (ha : 0 < a) (hc : 0 < c) (hr : 0 < r)
    (haeq : a * (‖w‖+1) = 1/2) (hceq : c * (‖L‖+1) = a/4)
    (hρy : ρ y = 0)
    (hz : z ∈ Metric.ball (y + (a*r) • w) (c*r))
    (hrem : |ρ z - ρ y - L (z-y)| ≤ (a/4) * ‖z-y‖) :
    z ∈ Metric.ball y r ∧ 0 < ρ z := by
  have hna := norm_nonneg w
  have hnL := norm_nonneg L
  have ha2 : a ≤ 1/2 := by nlinarith [mul_nonneg ha.le hna]
  have hc_a : c ≤ a/4 := by nlinarith [mul_nonneg hc.le hnL]
  have hc8 : c ≤ 1/8 := by linarith
  have hz' : ‖z - (y + (a*r) • w)‖ < c*r := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hz
  have hshift : ‖(a*r) • w‖ ≤ r/2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_pos ha hr).le]
    nlinarith [congrArg (fun t : ℝ => t*r) haeq, mul_pos ha hr]
  have hdist : ‖z-y‖ < r := by
    have ht := norm_add_le (z - (y + (a*r) • w)) ((a*r) • w)
    have hid : z - (y + (a*r) • w) + (a*r) • w = z-y := by abel
    rw [hid] at ht
    have hcr := mul_le_mul_of_nonneg_right hc8 hr.le
    linarith
  refine ⟨by simpa only [Metric.mem_ball, dist_eq_norm] using hdist, ?_⟩
  have hLbound := L.le_opNorm (z - (y + (a*r) • w))
  rw [Real.norm_eq_abs] at hLbound
  have hLlower : - (‖L‖ * (c*r)) ≤ L (z - (y + (a*r) • w)) := by
    have hm := mul_le_mul_of_nonneg_left hz'.le hnL
    have habs := neg_abs_le (L (z - (y + (a*r) • w)))
    linarith
  have hLeq : L (z-y) = L (z - (y + (a*r) • w)) + a*r := by
    have hid : z-y = z - (y + (a*r) • w) + (a*r) • w := by abel
    rw [hid, map_add, map_smul, hw, smul_eq_mul, mul_one]
  have hLc : ‖L‖ * (c*r) ≤ (a/4)*r := by
    have hmul := mul_le_mul_of_nonneg_right hc_a hr.le
    nlinarith [congrArg (fun t : ℝ => t*r) hceq]
  have herr : (a/4) * ‖z-y‖ ≤ (a/4)*r :=
    mul_le_mul_of_nonneg_left hdist.le (by positivity)
  rw [hρy, sub_zero] at hrem
  have habs := neg_abs_le (ρ z - L (z-y))
  have har := mul_pos ha hr
  nlinarith

/-- A nonzero defining differential gives exterior balls at every nearby
boundary point, with the same proportional radius. -/
theorem smoothDomain_local_exteriorBalls {n : ℕ} {O : Set (Space n)}
    (hO : SmoothDomain O) {x : Space n} (hx : x ∈ frontier O) :
    ∃ c R : ℝ, 0 < c ∧ 0 < R ∧
      ∀ y ∈ frontier O, y ∈ Metric.ball x R →
        ∀ r : ℝ, 0 < r → r ≤ R →
          ∃ z : Space n, Metric.ball z (c*r) ⊆ Metric.ball y r \ O := by
  obtain ⟨V, ρ, hV, hxV, hρ, hρx, hL, hdef⟩ := hO.2.2.2 x hx
  let L : Space n →L[ℝ] ℝ := fderiv ℝ ρ x
  have hv : ∃ v : Space n, L v ≠ 0 := by
    by_contra hh
    push Not at hh
    apply hL
    ext v
    exact hh v
  obtain ⟨v, hv⟩ := hv
  let w : Space n := (L v)⁻¹ • v
  have hw : L w = 1 := by simp [w, map_smul, hv]
  let a : ℝ := (1/2) / (‖w‖+1)
  have ha : 0 < a := by dsimp [a]; positivity
  have haeq : a * (‖w‖+1) = 1/2 :=
    div_mul_cancel₀ _ (by positivity)
  let c : ℝ := (a/4) / (‖L‖+1)
  have hc : 0 < c := by dsimp [c]; positivity
  have hceq : c * (‖L‖+1) = a/4 :=
    div_mul_cancel₀ _ (by positivity)
  have hca : c ≤ a/4 := by nlinarith [mul_nonneg hc.le (norm_nonneg L)]
  have ha2 : a ≤ 1/2 := by nlinarith [mul_nonneg ha.le (norm_nonneg w)]
  have hc8 : c ≤ 1/8 := by linarith
  have hstrict : HasStrictFDerivAt ρ L x :=
    (hρ.contDiffAt (hV.mem_nhds hxV)).hasStrictFDerivAt (by norm_num)
  obtain ⟨S, hS, hrem⟩ := strict_remainder_ball hstrict (show 0 < a/4 by positivity)
  obtain ⟨D, hD, hDV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hxV)
  let R : ℝ := min S D / 4
  have hR : 0 < R := by dsimp [R]; positivity
  have hRS : 2*R ≤ S := by
    have := min_le_left S D
    dsimp [R]
    linarith
  have hRD : 2*R ≤ D := by
    have := min_le_right S D
    dsimp [R]
    linarith
  refine ⟨c, R, hc, hR, ?_⟩
  intro y hy hyR r hr hrR
  have hyS : y ∈ Metric.ball x S :=
    Metric.ball_subset_ball (by linarith) hyR
  have hyV : y ∈ V := hDV (Metric.ball_subset_ball (by linarith) hyR)
  have hρy := definingFunction_zero_on_frontier hO.1 hV hρ.continuousOn hdef hy hyV
  refine ⟨y + (a*r) • w, ?_⟩
  intro z hz
  have hz' : ‖z - (y + (a*r) • w)‖ < c*r := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hz
  have hshift : ‖(a*r) • w‖ ≤ r/2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_pos ha hr).le]
    nlinarith [congrArg (fun t : ℝ => t*r) haeq, mul_pos ha hr]
  have hzy : ‖z-y‖ < r := by
    have ht := norm_add_le (z - (y + (a*r) • w)) ((a*r) • w)
    have hid : z - (y + (a*r) • w) + (a*r) • w = z-y := by abel
    rw [hid] at ht
    have hcr := mul_le_mul_of_nonneg_right hc8 hr.le
    linarith
  have hzx : dist z x < 2*R := by
    have ht := dist_triangle z y x
    have hzy' : dist z y < r := by simpa only [dist_eq_norm] using hzy
    have hyx : dist y x < R := hyR
    linarith
  have hzS : z ∈ Metric.ball x S := lt_of_lt_of_le hzx hRS
  have hzV : z ∈ V := hDV (lt_of_lt_of_le hzx hRD)
  have hpos := shifted_ball_positive hw ha hc hr haeq hceq hρy hz
    (hrem y hyS z hzS)
  refine ⟨hpos.1, ?_⟩
  intro hzO
  have hneg := ((Set.ext_iff.mp hdef z).mp ⟨hzO, hzV⟩).2
  linarith [hpos.2]

theorem finite_pos_lower_bound {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 < f i) : ∃ c : ℝ, 0 < c ∧ ∀ i ∈ s, c ≤ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨c, hc, hci⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    refine ⟨min c (f i), lt_min hc (hf i (Finset.mem_insert_self _ _)), ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hjs
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hci j hjs)

/-- Compactness of the actual boundary makes both local radii uniform. -/
theorem smoothDomain_uniformExteriorBalls {n : ℕ} {O : Set (Space n)}
    (hO : SmoothDomain O) :
    ∃ c r0 : ℝ, 0 < c ∧ 0 < r0 ∧
      ∀ x ∈ frontier O, ∀ r : ℝ, 0 < r → r ≤ r0 →
        ∃ y : Space n, Metric.ball y (c*r) ⊆ Metric.ball x r \ O := by
  classical
  choose c R hc hR hlocal using
    fun x : frontier O => smoothDomain_local_exteriorBalls hO x.property
  have hcompact : IsCompact (frontier O) :=
    hO.2.2.1.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hcover : frontier O ⊆ ⋃ x : frontier O, Metric.ball x.val (R x) := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hR ⟨x, hx⟩)⟩
  obtain ⟨s, hs⟩ := hcompact.elim_finite_subcover
    (fun x : frontier O => Metric.ball x.val (R x)) (fun _ => Metric.isOpen_ball) hcover
  obtain ⟨c0, hc0, hc0le⟩ := finite_pos_lower_bound s c (fun x _ => hc x)
  obtain ⟨r0, hr0, hr0le⟩ := finite_pos_lower_bound s R (fun x _ => hR x)
  refine ⟨c0, r0, hc0, hr0, ?_⟩
  intro x hx r hr hrr0
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hs hx)
  obtain ⟨his, hxi⟩ := Set.mem_iUnion.mp hi
  obtain ⟨y, hy⟩ := hlocal i x hx hxi r hr (hrr0.trans (hr0le i his))
  exact ⟨y, (Metric.ball_subset_ball
    (mul_le_mul_of_nonneg_right (hc0le i his) hr.le)).trans hy⟩

/-- The eighth component of the frozen L16 obligation. -/
theorem smoothDomainExteriorMeasure : SmoothDomainExteriorMeasure := by
  intro n hn O hO
  obtain ⟨c, r0, hc, hr0, hballs⟩ := smoothDomain_uniformExteriorBalls hO
  exact exteriorMeasure_of_uniformExteriorBalls hc hr0 hballs

/-- The principal coefficient of the exponential divergence equation has
fixed ellipticity constants depending only on the value bounds of q. -/
theorem elliptic_div_of_bounds {n : ℕ} {Q : Set (Point n)}
    {a : Point n → Mat n} {q : Point n → ℝ} {lam upper m B : ℝ}
    (hEll : Elliptic Q a lam upper) (hm : 0 < m) (hmB : m ≤ B)
    (hq : ∀ p ∈ Q, m ≤ q p ∧ q p ≤ B) :
    Elliptic Q (fun p => (q p)⁻¹ • a p) (lam/B) (upper/m) := by
  have hB : 0 < B := hm.trans_le hmB
  have hu : 0 < upper := hEll.1.trans_le hEll.2.1
  refine ⟨div_pos hEll.1 hB, ?_, ?_⟩
  · apply (div_le_div_iff₀ hB hm).mpr
    exact (mul_le_mul_of_nonneg_right hEll.2.1 hm.le).trans
      (mul_le_mul_of_nonneg_left hmB hu.le)
  · intro p hp
    obtain ⟨hSymm, hquad⟩ := hEll.2.2 p hp
    have hqp : 0 < q p := hm.trans_le (hq p hp).1
    refine ⟨?_, ?_⟩
    · change ((q p)⁻¹ • a p).transpose = (q p)⁻¹ • a p
      rw [Matrix.transpose_smul, hSymm]
    · intro v
      have hS : 0 ≤ ∑ i, (v i)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have heq : (∑ i, ∑ j, ((q p)⁻¹ • a p) i j * v i * v j) =
          (q p)⁻¹ * (∑ i, ∑ j, a p i j * v i * v j) := by
        simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      rw [heq]
      have hlo : lam/B ≤ (q p)⁻¹ * lam := by
        rw [mul_comm, ← div_eq_mul_inv]
        apply (div_le_div_iff₀ hB hqp).mpr
        exact mul_le_mul_of_nonneg_left (hq p hp).2 hEll.1.le
      have hhi : (q p)⁻¹ * upper ≤ upper/m := by
        rw [mul_comm, ← div_eq_mul_inv]
        apply (div_le_div_iff₀ hqp hm).mpr
        exact mul_le_mul_of_nonneg_left (hq p hp).1 hu.le
      constructor
      · calc
          lam/B * (∑ i, (v i)^2) ≤ (q p)⁻¹ * (lam * (∑ i, (v i)^2)) := by
            simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hlo hS
          _ ≤ (q p)⁻¹ * (∑ i, ∑ j, a p i j * v i * v j) :=
            mul_le_mul_of_nonneg_left (hquad v).1 (inv_nonneg.mpr hqp.le)
      · calc
          (q p)⁻¹ * (∑ i, ∑ j, a p i j * v i * v j) ≤
              (q p)⁻¹ * (upper * (∑ i, (v i)^2)) :=
            mul_le_mul_of_nonneg_left (hquad v).2 (inv_nonneg.mpr hqp.le)
          _ ≤ upper/m * (∑ i, (v i)^2) := by
            simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hhi hS

/-- Necessary second derivative condition, obtained from the one-variable
second derivative test and equality on a neighborhood. -/
theorem second_deriv_nonpos_of_isLocalMax {f : ℝ → ℝ} {x : ℝ}
    (h : IsLocalMax f x) (hf : ContinuousAt f x) : deriv (deriv f) x ≤ 0 := by
  by_contra hn
  have hp : 0 < deriv (deriv f) x := lt_of_not_ge hn
  have hmin := isLocalMin_of_deriv_deriv_pos hp h.deriv_eq_zero hf
  have heq : f =ᶠ[𝓝 x] fun _ => f x := by
    filter_upwards [h, hmin] with y hymax hymin
    exact le_antisymm hymax hymin
  have hz := heq.deriv.deriv_eq
  have hh : deriv (deriv f) x = 0 := by simpa using hz
  linarith

/-- The actual spatial Hessian is nonpositive on every direction at a
local maximum; joint space-time differentiability is unnecessary. -/
theorem secondFDeriv_nonpos_of_isLocalMax {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hmax : IsLocalMax f x) (v : E) :
    fderiv ℝ (fderiv ℝ f) x v v ≤ 0 := by
  let g : ℝ → ℝ := fun t => f (x + t • v)
  have hline : ContinuousAt (fun t : ℝ => x + t • v) 0 := by fun_prop
  have hline' : Tendsto (fun t : ℝ => x + t • v) (𝓝 0) (𝓝 x) := by
    simpa only [ContinuousAt, zero_smul, add_zero] using hline
  have hgmax : IsLocalMax g 0 := by
    have hmax' : IsLocalMax f (x + (0 : ℝ) • v) := by simpa using hmax
    exact hmax'.comp_continuous (g := fun t : ℝ => x + t • v) hline
  have hgcont : ContinuousAt g 0 := by
    have hcompose : Tendsto (fun t : ℝ => f (x + t • v)) (𝓝 0) (𝓝 (f x)) :=
      (show Tendsto f (𝓝 x) (𝓝 (f x)) from hf.continuousAt).comp hline'
    simpa only [ContinuousAt, g, zero_smul, add_zero] using hcompose
  have hgder : deriv g =ᶠ[𝓝 0] fun t => fderiv ℝ f (x + t • v) v := by
    filter_upwards [hline' (hf.eventually (by norm_num))] with t ht
    change ContDiffAt ℝ 2 f (x + t • v) at ht
    exact (ht.differentiableAt (by norm_num)).deriv_comp_add_smul
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdv : DifferentiableAt ℝ (fun y => fderiv ℝ f y v) (x + (0 : ℝ) • v) := by
    simpa using hd.clm_apply (differentiableAt_const v)
  have hd2 : deriv (fun t : ℝ => fderiv ℝ f (x + t • v) v) 0 =
      fderiv ℝ (fderiv ℝ f) x v v := by
    rw [hdv.deriv_comp_add_smul]
    simp only [zero_smul, add_zero]
    rw [fderiv_clm_apply hd (differentiableAt_const v)]
    simp
  have hnonpos := second_deriv_nonpos_of_isLocalMax hgmax hgcont
  rw [hgder.deriv_eq, hd2] at hnonpos
  exact hnonpos

open scoped MatrixOrder in
theorem posSemidef_eq_transpose_mul_self {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    ∃ S : Matrix ι ι ℝ, A = S.transpose * S := by
  refine ⟨CFC.sqrt A, ?_⟩
  have hS : (CFC.sqrt A).transpose = CFC.sqrt A :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian.isSymm
  rw [hS, ← sq]
  exact (CFC.sq_sqrt A hA.nonneg).symm

/-- Contracting a nonpositive bilinear form against a positive semidefinite
coefficient matrix is nonpositive, by the actual Gram decomposition. -/
theorem bilinear_contraction_nonpos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → E)
    (H : E →L[ℝ] E →L[ℝ] ℝ) {A : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hH : ∀ v : E, H v v ≤ 0) :
    (∑ i, ∑ j, A i j * H (e i) (e j)) ≤ 0 := by
  obtain ⟨S, rfl⟩ := posSemidef_eq_transpose_mul_self hA
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  calc
    (∑ i, ∑ j, ∑ k, S k i * S k j * H (e i) (e j)) =
        ∑ i, ∑ k, ∑ j, S k i * S k j * H (e i) (e j) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ i, ∑ j, S k i * S k j * H (e i) (e j) := Finset.sum_comm
    _ ≤ 0 := by
      apply Finset.sum_nonpos
      intro k hk
      convert hH (∑ i, S k i • e i) using 1
      simp [map_sum, map_smul, Finset.mul_sum, mul_assoc]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

theorem elliptic_posSemidef {n : ℕ} {Q : Set (Point n)} {a : Point n → Mat n}
    {lam upper : ℝ} (h : Elliptic Q a lam upper) {p : Point n} (hp : p ∈ Q) :
    (a p).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    ⟨Matrix.isHermitian_iff_isSymm.mpr (h.2.2 p hp).1, ?_⟩
  intro v
  calc
    0 ≤ lam * (∑ i, (v i)^2) :=
      mul_nonneg h.1.le (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    _ ≤ ∑ i, ∑ j, a p i j * v i * v j := ((h.2.2 p hp).2 v).1
    _ = star v ⬝ᵥ (a p *ᵥ v) := by
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- At a positive-time maximum, the within derivative from the left is
nonnegative, including the terminal time face. -/
theorem derivWithin_nonneg_at_Icc_max {f : ℝ → ℝ} {t T : ℝ}
    (ht : 0 < t) (htT : t ≤ T)
    (hf : DifferentiableWithinAt ℝ f (Set.Icc 0 T) t)
    (hmax : IsMaxOn f (Set.Icc 0 T) t) :
    0 ≤ derivWithin f (Set.Icc 0 T) t := by
  have hcone : -t ∈ posTangentConeAt (Set.Icc 0 T) t := by
    simpa only [zero_sub] using sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc (0 : ℝ) T).segment_subset ⟨ht.le, htT⟩ ⟨le_rfl, ht.le.trans htT⟩)
  have hh := hmax.isLocalMaxOn.hasFDerivWithinAt_nonpos hf.hasDerivWithinAt hcone
  change (-t) * derivWithin f (Set.Icc 0 T) t ≤ 0 at hh
  nlinarith

/-- The computed nondivergence operator is nonnegative at a positive-time
interior spatial maximum, with the final time face included. -/
theorem linearOp_nonneg_at_max {n : ℕ} {O : Set (Space n)} {T lam upper : ℝ}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {u : Point n → ℝ}
    (hO : IsOpen O) (hu : C2 (cylinder (closure O) 0 T) u)
    (hEll : Elliptic (cylinder (closure O) 0 T) a lam upper)
    {p : Point n} (hp : p ∈ O ×ˢ Set.Ioc 0 T)
    (hmax : IsMaxOn u (cylinder (closure O) 0 T) p) :
    0 ≤ linearOp (cylinder (closure O) 0 T) a b u p := by
  have hpQ : p ∈ cylinder (closure O) 0 T :=
    ⟨subset_closure hp.1, hp.2.1.le, hp.2.2⟩
  have hsmax : IsLocalMax (fun x => u (x,p.2)) p.1 := by
    have hh : IsMaxOn (fun x => u (x,p.2)) (closure O) p.1 := by
      intro x hx
      exact hmax ⟨hx, hp.2.1.le, hp.2.2⟩
    exact hh.isLocalMax (Filter.mem_of_superset (hO.mem_nhds hp.1) subset_closure)
  have hD : spatialD u p = 0 := hsmax.fderiv_eq_zero
  have hH : ∀ v : Space n, spatialDD u p v v ≤ 0 :=
    secondFDeriv_nonpos_of_isLocalMax (hu.2.2.2.2.1 p hpQ) hsmax
  have hcontract := bilinear_contraction_nonpos Yau.realVec (spatialDD u p)
    (elliptic_posSemidef hEll hpQ) hH
  have hfiber : {t | (p.1,t) ∈ cylinder (closure O) 0 T} = Set.Icc 0 T := by
    ext t
    simp only [Yau.Parabolic.cylinder, Set.mem_prod, Set.mem_ofPred_eq, hpQ.1, true_and]
  have htimeDiff : DifferentiableWithinAt ℝ (fun t => u (p.1,t)) (Set.Icc 0 T) p.2 := by
    simpa only [hfiber] using hu.2.2.2.2.2 p hpQ
  have htimeMax : IsMaxOn (fun t => u (p.1,t)) (Set.Icc 0 T) p.2 := by
    intro t ht
    exact hmax ⟨hpQ.1, ht⟩
  have htime : 0 ≤ timeD (cylinder (closure O) 0 T) u p := by
    simpa only [timeD, hfiber] using
      derivWithin_nonneg_at_Icc_max hp.2.1 hp.2.2 htimeDiff htimeMax
  simp only [linearOp, hD, zero_apply, mul_zero,
    Finset.sum_const_zero, sub_zero]
  exact sub_nonneg.mpr (hcontract.trans htime)

/-- Strict subsolutions with nonpositive parabolic boundary values cannot
have a positive maximum on the compact closed cylinder. -/
theorem strict_maximum_principle {n : ℕ} {O : Set (Space n)} {T lam upper : ℝ}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {u : Point n → ℝ}
    (hO : IsOpen O) (hcompact : IsCompact (closure O))
    (hu : C2 (cylinder (closure O) 0 T) u)
    (hEll : Elliptic (cylinder (closure O) 0 T) a lam upper)
    (hinit : ∀ x ∈ closure O, u (x,0) ≤ 0)
    (hlat : ∀ x ∈ frontier O, ∀ t ∈ Set.Icc 0 T, u (x,t) ≤ 0)
    (hop : ∀ p ∈ O ×ˢ Set.Ioc 0 T,
      linearOp (cylinder (closure O) 0 T) a b u p < 0) :
    ∀ p ∈ cylinder (closure O) 0 T, u p ≤ 0 := by
  intro p hp
  by_contra hn
  have hpos : 0 < u p := lt_of_not_ge hn
  obtain ⟨q, hq, hmax⟩ := (hcompact.prod isCompact_Icc).exists_isMaxOn ⟨p, hp⟩ hu.1
  have hposq : 0 < u q := hpos.trans_le (hmax hp)
  have hqO : q.1 ∈ O := by
    by_contra hnot
    have hfr : q.1 ∈ frontier O :=
      ⟨hq.1, by simpa only [hO.interior_eq] using hnot⟩
    exact not_lt_of_ge (hlat q.1 hfr q.2 hq.2) hposq
  have hqt : 0 < q.2 := by
    by_contra hnot
    have hz : q.2 = 0 := le_antisymm (le_of_not_gt hnot) hq.2.1
    have hh := hinit q.1 hq.1
    have heq : (q.1, (0 : ℝ)) = q := Prod.ext rfl hz.symm
    rw [heq] at hh
    exact not_lt_of_ge hh hposq
  have hq' : q ∈ O ×ˢ Set.Ioc 0 T := ⟨hqO, hqt, hq.2.2⟩
  exact not_lt_of_ge (linearOp_nonneg_at_max hO hu hEll hq' hmax) (hop q hq')

theorem spatialD_sub_timeAffine {n : ℕ} (u : Point n → ℝ) (δ : ℝ) :
    spatialD (fun p => u p - δ*(p.2+1)) = spatialD u := by
  funext p
  simp only [spatialD, fderiv_sub_const]

theorem spatialDD_sub_timeAffine {n : ℕ} (u : Point n → ℝ) (δ : ℝ) :
    spatialDD (fun p => u p - δ*(p.2+1)) = spatialDD u := by
  funext p
  simp only [spatialDD, fderiv_sub_const]

theorem timeD_sub_timeAffine {n : ℕ} {O : Set (Space n)} {T : ℝ}
    {u : Point n → ℝ} (hT : 0 < T) (hu : C2 (cylinder O 0 T) u) (δ : ℝ)
    {p : Point n} (hp : p ∈ cylinder O 0 T) :
    timeD (cylinder O 0 T) (fun p => u p - δ*(p.2+1)) p =
      timeD (cylinder O 0 T) u p - δ := by
  have hfiber : {t | (p.1,t) ∈ cylinder O 0 T} = Set.Icc 0 T := by
    ext t
    simp [Yau.Parabolic.cylinder, hp.1]
  have hc : HasDerivAt (fun t : ℝ => δ*(t+1)) δ p.2 := by
    convert ((hasDerivAt_id p.2).add_const 1).const_mul δ using 1 <;> simp
  simp only [timeD]
  rw [derivWithin_fun_sub (hu.2.2.2.2.2 p hp) hc.differentiableAt.differentiableWithinAt]
  congr 1
  rw [hfiber]
  exact hc.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hT p.2 hp.2)

theorem c2_sub_timeAffine {n : ℕ} {O : Set (Space n)} {T : ℝ}
    {u : Point n → ℝ} (hT : 0 < T) (hu : C2 (cylinder O 0 T) u) (δ : ℝ) :
    C2 (cylinder O 0 T) (fun p => u p - δ*(p.2+1)) := by
  have hc : Continuous (fun p : Point n => δ*(p.2+1)) := by fun_prop
  refine ⟨hu.1.sub hc.continuousOn, ?_, ?_, ?_, ?_, ?_⟩
  · rw [spatialD_sub_timeAffine]
    exact hu.2.1
  · rw [spatialDD_sub_timeAffine]
    exact hu.2.2.1
  · apply (hu.2.2.2.1.sub continuousOn_const).congr
    intro p hp
    exact timeD_sub_timeAffine hT hu δ hp
  · intro p hp
    have hc : ContDiffAt ℝ 2 (fun _ : Space n => δ*(p.2+1)) p.1 := contDiffAt_const
    exact (hu.2.2.2.2.1 p hp).sub hc
  · intro p hp
    exact (hu.2.2.2.2.2 p hp).sub (by fun_prop)

theorem linearOp_sub_timeAffine {n : ℕ} {O : Set (Space n)} {T : ℝ}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {u : Point n → ℝ}
    (hT : 0 < T) (hu : C2 (cylinder O 0 T) u) (δ : ℝ)
    {p : Point n} (hp : p ∈ cylinder O 0 T) :
    linearOp (cylinder O 0 T) a b (fun p => u p - δ*(p.2+1)) p =
      linearOp (cylinder O 0 T) a b u p - δ := by
  simp only [linearOp, spatialD_sub_timeAffine, spatialDD_sub_timeAffine,
    timeD_sub_timeAffine hT hu δ hp]
  ring

/-- Weak maximum principle for the actual parabolic C2 class and operator. -/
theorem maximum_principle {n : ℕ} {O : Set (Space n)} {T lam upper : ℝ}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {u : Point n → ℝ}
    (hO : IsOpen O) (hcompact : IsCompact (closure O)) (hT : 0 < T)
    (hu : C2 (cylinder (closure O) 0 T) u)
    (hEll : Elliptic (cylinder (closure O) 0 T) a lam upper)
    (hinit : ∀ x ∈ closure O, u (x,0) ≤ 0)
    (hlat : ∀ x ∈ frontier O, ∀ t ∈ Set.Icc 0 T, u (x,t) ≤ 0)
    (hop : ∀ p ∈ O ×ˢ Set.Ioc 0 T,
      linearOp (cylinder (closure O) 0 T) a b u p ≤ 0) :
    ∀ p ∈ cylinder (closure O) 0 T, u p ≤ 0 := by
  intro p hp
  by_contra hn
  have hpos : 0 < u p := lt_of_not_ge hn
  have hpt : 0 < p.2+1 := by linarith [hp.2.1]
  let δ : ℝ := u p / (2*(p.2+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδeq : δ*(p.2+1) = u p / 2 := by
    dsimp [δ]
    field_simp
  have htilt := c2_sub_timeAffine hT hu δ
  have hinit' : ∀ x ∈ closure O, u (x,0) - δ*((0 : ℝ)+1) ≤ 0 := by
    intro x hx
    have := hinit x hx
    simp only [zero_add, mul_one]
    linarith
  have hlat' : ∀ x ∈ frontier O, ∀ t ∈ Set.Icc 0 T,
      u (x,t) - δ*(t+1) ≤ 0 := by
    intro x hx t ht
    have := hlat x hx t ht
    have hmul : 0 ≤ δ*(t+1) := mul_nonneg hδ.le (by linarith [ht.1])
    linarith
  have hop' : ∀ z ∈ O ×ˢ Set.Ioc 0 T,
      linearOp (cylinder (closure O) 0 T) a b (fun z => u z - δ*(z.2+1)) z < 0 := by
    intro z hz
    rw [linearOp_sub_timeAffine hT hu δ ⟨subset_closure hz.1, hz.2.1.le, hz.2.2⟩]
    linarith [hop z hz]
  have hh := strict_maximum_principle hO hcompact htilt hEll hinit' hlat' hop' p hp
  rw [hδeq] at hh
  linarith

theorem spatialD_sub {n : ℕ} {Q : Set (Point n)} {u v : Point n → ℝ}
    (hu : C2 Q u) (hv : C2 Q v) {p : Point n} (hp : p ∈ Q) :
    spatialD (fun p => u p - v p) p = spatialD u p - spatialD v p := by
  exact fderiv_fun_sub ((hu.2.2.2.2.1 p hp).differentiableAt (by norm_num))
    ((hv.2.2.2.2.1 p hp).differentiableAt (by norm_num))

theorem secondFDeriv_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    fderiv ℝ (fderiv ℝ (fun y => f y-g y)) x =
      fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ g) x := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hgd : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have heq : fderiv ℝ (fun y => f y-g y) =ᶠ[𝓝 x]
      fun y => fderiv ℝ f y - fderiv ℝ g y := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hfy hgy
    exact fderiv_fun_sub (hfy.differentiableAt (by norm_num))
      (hgy.differentiableAt (by norm_num))
  exact heq.fderiv_eq.trans (fderiv_fun_sub hfd hgd)

theorem spatialDD_sub {n : ℕ} {Q : Set (Point n)} {u v : Point n → ℝ}
    (hu : C2 Q u) (hv : C2 Q v) {p : Point n} (hp : p ∈ Q) :
    spatialDD (fun p => u p - v p) p = spatialDD u p - spatialDD v p :=
  secondFDeriv_sub (hu.2.2.2.2.1 p hp) (hv.2.2.2.2.1 p hp)

theorem timeD_sub {n : ℕ} {Q : Set (Point n)} {u v : Point n → ℝ}
    (hu : C2 Q u) (hv : C2 Q v) {p : Point n} (hp : p ∈ Q) :
    timeD Q (fun p => u p - v p) p = timeD Q u p - timeD Q v p :=
  derivWithin_fun_sub (hu.2.2.2.2.2 p hp) (hv.2.2.2.2.2 p hp)

theorem c2_sub {n : ℕ} {Q : Set (Point n)} {u v : Point n → ℝ}
    (hu : C2 Q u) (hv : C2 Q v) : C2 Q (fun p => u p-v p) := by
  let : ContinuousSub (Space n →L[ℝ] Space n →L[ℝ] ℝ) :=
    IsTopologicalAddGroup.to_continuousSub (G := Space n →L[ℝ] Space n →L[ℝ] ℝ)
  refine ⟨hu.1.sub hv.1, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hu.2.1.sub hv.2.1).congr (fun p hp => spatialD_sub hu hv hp)
  · exact (hu.2.2.1.sub hv.2.2.1).congr (fun p hp => spatialDD_sub hu hv hp)
  · exact (hu.2.2.2.1.sub hv.2.2.2.1).congr (fun p hp => timeD_sub hu hv hp)
  · intro p hp
    exact (hu.2.2.2.2.1 p hp).sub (hv.2.2.2.2.1 p hp)
  · intro p hp
    exact (hu.2.2.2.2.2 p hp).sub (hv.2.2.2.2.2 p hp)

theorem linearOp_sub {n : ℕ} {Q : Set (Point n)}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {u v : Point n → ℝ}
    (hu : C2 Q u) (hv : C2 Q v) {p : Point n} (hp : p ∈ Q) :
    linearOp Q a b (fun p => u p-v p) p = linearOp Q a b u p - linearOp Q a b v p := by
  simp only [linearOp, timeD_sub hu hv hp, spatialD_sub hu hv hp, spatialDD_sub hu hv hp,
    sub_apply, mul_sub, Finset.sum_sub_distrib]
  ring

/-- Comparison applies to two concrete C2 functions, without a Hölder
regularity assumption on their derivatives. -/
theorem comparison_principle {n : ℕ} {O : Set (Space n)} {T lam upper : ℝ}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {u v : Point n → ℝ}
    (hO : IsOpen O) (hcompact : IsCompact (closure O)) (hT : 0 < T)
    (hu : C2 (cylinder (closure O) 0 T) u)
    (hv : C2 (cylinder (closure O) 0 T) v)
    (hEll : Elliptic (cylinder (closure O) 0 T) a lam upper)
    (hinit : ∀ x ∈ closure O, u (x,0) ≤ v (x,0))
    (hlat : ∀ x ∈ frontier O, ∀ t ∈ Set.Icc 0 T, u (x,t) ≤ v (x,t))
    (hop : ∀ p ∈ O ×ˢ Set.Ioc 0 T,
      linearOp (cylinder (closure O) 0 T) a b u p ≤
        linearOp (cylinder (closure O) 0 T) a b v p) :
    ∀ p ∈ cylinder (closure O) 0 T, u p ≤ v p := by
  have hh := maximum_principle hO hcompact hT (c2_sub hu hv) hEll
    (fun x hx => sub_nonpos.mpr (hinit x hx))
    (fun x hx t ht => sub_nonpos.mpr (hlat x hx t ht))
    (fun p hp => by
      rw [linearOp_sub hu hv ⟨subset_closure hp.1, hp.2.1.le, hp.2.2⟩]
      exact sub_nonpos.mpr (hop p hp))
  intro p hp
  exact sub_nonpos.mp (hh p hp)

/-- The uniqueness clause required by compatible Dirichlet Schauder
existence holds in the larger actual C2 competitor class. -/
theorem classical_dirichlet_unique {n : ℕ} {O : Set (Space n)} {T lam upper : ℝ}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    {u v f ψ : Point n → ℝ}
    (hO : IsOpen O) (hcompact : IsCompact (closure O)) (hT : 0 < T)
    (hu : C2 (cylinder (closure O) 0 T) u)
    (hv : C2 (cylinder (closure O) 0 T) v)
    (hEll : Elliptic (cylinder (closure O) 0 T) a lam upper)
    (hDu : DirichletData O T u ψ) (hDv : DirichletData O T v ψ)
    (hEu : ∀ z ∈ cylinder O 0 T, linearOp (cylinder (closure O) 0 T) a b u z = f z)
    (hEv : ∀ z ∈ cylinder O 0 T, linearOp (cylinder (closure O) 0 T) a b v z = f z) :
    Set.EqOn u v (cylinder (closure O) 0 T) := by
  have hinit : ∀ x ∈ closure O, u (x,0) = v (x,0) :=
    fun x hx => (hDu.1 x hx).trans (hDv.1 x hx).symm
  have hlat : ∀ x ∈ frontier O, ∀ t ∈ Set.Icc 0 T, u (x,t) = v (x,t) :=
    fun x hx t ht => (hDu.2 x hx t ht).trans (hDv.2 x hx t ht).symm
  have hop : ∀ z ∈ O ×ˢ Set.Ioc 0 T,
      linearOp (cylinder (closure O) 0 T) a b u z =
        linearOp (cylinder (closure O) 0 T) a b v z := by
    intro z hz
    have hz' : z ∈ cylinder O 0 T := ⟨hz.1, hz.2.1.le, hz.2.2⟩
    exact (hEu z hz').trans (hEv z hz').symm
  intro z hz
  apply le_antisymm
  · exact comparison_principle hO hcompact hT hu hv hEll
      (fun x hx => (hinit x hx).le) (fun x hx t ht => (hlat x hx t ht).le)
      (fun p hp => (hop p hp).le) z hz
  · exact comparison_principle hO hcompact hT hv hu hEll
      (fun x hx => (hinit x hx).symm.le) (fun x hx t ht => (hlat x hx t ht).symm.le)
      (fun p hp => (hop p hp).symm.le) z hz

theorem spatialD_add_const {n : ℕ} (u : Point n → ℝ) (K : ℝ) :
    spatialD (fun p => u p+K) = spatialD u := by
  funext p
  simp only [spatialD, fderiv_add_const]

theorem spatialDD_add_const {n : ℕ} (u : Point n → ℝ) (K : ℝ) :
    spatialDD (fun p => u p+K) = spatialDD u := by
  funext p
  simp only [spatialDD, fderiv_add_const]

theorem timeD_add_const {n : ℕ} (Q : Set (Point n)) (u : Point n → ℝ) (K : ℝ) :
    timeD Q (fun p => u p+K) = timeD Q u := by
  funext p
  simp only [timeD, derivWithin_add_const]

theorem c2_add_const {n : ℕ} {Q : Set (Point n)} {u : Point n → ℝ}
    (hu : C2 Q u) (K : ℝ) : C2 Q (fun p => u p+K) := by
  refine ⟨hu.1.add continuousOn_const, ?_, ?_, ?_, ?_, ?_⟩
  · rw [spatialD_add_const]
    exact hu.2.1
  · rw [spatialDD_add_const]
    exact hu.2.2.1
  · rw [timeD_add_const]
    exact hu.2.2.2.1
  · intro p hp
    exact (hu.2.2.2.2.1 p hp).add contDiffAt_const
  · intro p hp
    exact (hu.2.2.2.2.2 p hp).add (differentiableWithinAt_const K)

theorem linearOp_add_const {n : ℕ} (Q : Set (Point n))
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ) (u : Point n → ℝ) (K : ℝ) :
    linearOp Q a b (fun p => u p+K) = linearOp Q a b u := by
  funext p
  simp only [linearOp, spatialD_add_const, spatialDD_add_const, timeD_add_const]

/-- The elementary quantitative comparison estimate needed in the C2
approximation argument: boundary error plus elapsed time times residual. -/
theorem linear_subsolution_bound {n : ℕ} {O : Set (Space n)} {T lam upper E F : ℝ}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {u : Point n → ℝ}
    (hO : IsOpen O) (hcompact : IsCompact (closure O)) (hT : 0 < T)
    (hu : C2 (cylinder (closure O) 0 T) u)
    (hEll : Elliptic (cylinder (closure O) 0 T) a lam upper) (hF : 0 ≤ F)
    (hinit : ∀ x ∈ closure O, u (x,0) ≤ E)
    (hlat : ∀ x ∈ frontier O, ∀ t ∈ Set.Icc 0 T, u (x,t) ≤ E)
    (hop : ∀ p ∈ O ×ˢ Set.Ioc 0 T,
      linearOp (cylinder (closure O) 0 T) a b u p ≤ F) :
    ∀ p ∈ cylinder (closure O) 0 T, u p ≤ E + p.2*F := by
  let w : Point n → ℝ := fun p => (u p-F*(p.2+1))+(F-E)
  have hw : C2 (cylinder (closure O) 0 T) w :=
    c2_add_const (c2_sub_timeAffine hT hu F) (F-E)
  have hwinit : ∀ x ∈ closure O, w (x,0) ≤ 0 := by
    intro x hx
    dsimp [w]
    linarith [hinit x hx]
  have hwlat : ∀ x ∈ frontier O, ∀ t ∈ Set.Icc 0 T, w (x,t) ≤ 0 := by
    intro x hx t ht
    dsimp [w]
    nlinarith [hlat x hx t ht, mul_nonneg hF ht.1]
  have hwop : ∀ p ∈ O ×ˢ Set.Ioc 0 T,
      linearOp (cylinder (closure O) 0 T) a b w p ≤ 0 := by
    intro p hp
    dsimp only [w]
    rw [linearOp_add_const, linearOp_sub_timeAffine hT hu F
      ⟨subset_closure hp.1, hp.2.1.le, hp.2.2⟩]
    linarith [hop p hp]
  have hmax := maximum_principle hO hcompact hT hw hEll hwinit hwlat hwop
  intro p hp
  have hh := hmax p hp
  dsimp [w] at hh
  linarith

/-- Uniform approximation stability without any derivative bound on the
functions: only their parabolic boundary difference and PDE residual enter. -/
theorem linear_difference_sup_bound {n : ℕ} {O : Set (Space n)}
    {T lam upper E F : ℝ} {a : Point n → Mat n}
    {b : Point n → Yau.RIdx n → ℝ} {u v : Point n → ℝ}
    (hO : IsOpen O) (hcompact : IsCompact (closure O)) (hT : 0 < T)
    (hu : C2 (cylinder (closure O) 0 T) u)
    (hv : C2 (cylinder (closure O) 0 T) v)
    (hEll : Elliptic (cylinder (closure O) 0 T) a lam upper) (hF : 0 ≤ F)
    (hinit : ∀ x ∈ closure O, |u (x,0)-v (x,0)| ≤ E)
    (hlat : ∀ x ∈ frontier O, ∀ t ∈ Set.Icc 0 T, |u (x,t)-v (x,t)| ≤ E)
    (hop : ∀ p ∈ O ×ˢ Set.Ioc 0 T,
      |linearOp (cylinder (closure O) 0 T) a b u p -
        linearOp (cylinder (closure O) 0 T) a b v p| ≤ F) :
    ∀ p ∈ cylinder (closure O) 0 T, |u p-v p| ≤ E + T*F := by
  have huv := linear_subsolution_bound (E := E) (F := F) hO hcompact hT (c2_sub hu hv) hEll hF
    (fun x hx => (le_abs_self _).trans (hinit x hx))
    (fun x hx t ht => (le_abs_self _).trans (hlat x hx t ht))
    (fun p hp => by
      rw [linearOp_sub hu hv ⟨subset_closure hp.1, hp.2.1.le, hp.2.2⟩]
      exact (le_abs_self _).trans (hop p hp))
  have hvu := linear_subsolution_bound (E := E) (F := F) hO hcompact hT (c2_sub hv hu) hEll hF
    (fun x hx => by have := neg_le_abs (u (x,0)-v (x,0)); linarith [hinit x hx])
    (fun x hx t ht => by
      have := neg_le_abs (u (x,t)-v (x,t)); linarith [hlat x hx t ht])
    (fun p hp => by
      rw [linearOp_sub hv hu ⟨subset_closure hp.1, hp.2.1.le, hp.2.2⟩]
      have := neg_le_abs (linearOp (cylinder (closure O) 0 T) a b u p -
        linearOp (cylinder (closure O) 0 T) a b v p)
      linarith [hop p hp])
  intro p hp
  have htime := mul_le_mul_of_nonneg_right hp.2.2 hF
  rw [abs_le]
  constructor <;> linarith [huv p hp, hvu p hp]

theorem space_finrank_real (n : ℕ) : Module.finrank ℝ (Space n) = 2*n := by
  rw [finrank_real_of_complex]
  simp [Space, Yau.ComplexVector]

/-- The Euclidean heat kernel in the actual real dimension 2n. Its values
at nonpositive times play no role in the positive-time results below. -/
def gaussianKernel {n : ℕ} (t : ℝ) (x : Space n) : ℝ :=
  ((4*Real.pi*t)^n)⁻¹ * Real.exp (-‖x‖^2/(4*t))

theorem integrable_exp_neg_norm_sq {n : ℕ} {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : Space n => Real.exp (-b*‖x‖^2)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := Space n) (b := (b : ℂ)) (by simpa using hb) 0 0
  convert h.re using 1
  funext x
  simp only [zero_mul, add_zero]
  rw [← Complex.exp_ofReal_re]
  push_cast
  rfl

theorem gaussianKernel_pos {n : ℕ} {t : ℝ} (ht : 0 < t) (x : Space n) :
    0 < gaussianKernel t x := by
  unfold gaussianKernel
  positivity

theorem gaussianKernel_integrable {n : ℕ} {t : ℝ} (ht : 0 < t) :
    Integrable (gaussianKernel (n := n) t) := by
  have hb : 0 < (4*t)⁻¹ := by positivity
  convert (integrable_exp_neg_norm_sq (n := n) hb).const_mul (((4*Real.pi*t)^n)⁻¹) using 1
  funext x
  unfold gaussianKernel
  congr 2
  simp only [div_eq_mul_inv]
  ring

theorem gaussianKernel_integral {n : ℕ} {t : ℝ} (ht : 0 < t) :
    ∫ x : Space n, gaussianKernel t x = 1 := by
  have hb : 0 < (4*t)⁻¹ := by positivity
  have hgauss := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := Space n) hb
  rw [space_finrank_real] at hgauss
  have hdim : ((2*n : ℕ) : ℝ)/2 = (n : ℝ) := by push_cast; ring
  rw [hdim, Real.rpow_natCast] at hgauss
  have hscale : Real.pi/(4*t)⁻¹ = 4*Real.pi*t := by
    rw [div_inv_eq_mul]
    ring
  rw [hscale] at hgauss
  have hform : gaussianKernel (n := n) t = fun x =>
      ((4*Real.pi*t)^n)⁻¹ * Real.exp (-(4*t)⁻¹*‖x‖^2) := by
    funext x
    unfold gaussianKernel
    congr 2
    simp only [div_eq_mul_inv]
    ring
  rw [hform, integral_const_mul, hgauss]
  exact inv_mul_cancel₀ (pow_ne_zero n (by positivity))

theorem gaussianKernel_spatial_smooth {n : ℕ} (t : ℝ) :
    ContDiff ℝ ∞ (gaussianKernel (n := n) t) := by
  unfold gaussianKernel
  have hn : ContDiff ℝ ∞ (fun x : Space n => ‖x‖^2) := contDiff_id.norm_sq ℝ
  exact contDiff_const.mul ((hn.neg.div_const (4*t)).exp)

set_option backward.isDefEq.respectTransparency.types false in
theorem gaussianKernel_hasFDerivAt {n : ℕ} {t : ℝ} (ht : 0 < t) (x : Space n) :
    HasFDerivAt (gaussianKernel t)
      ((-gaussianKernel t x/(2*t)) • innerSL ℝ x) x := by
  have hnorm : HasFDerivAt (fun y : Space n => ‖y‖^2) (2 • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hinner : HasFDerivAt (fun y : Space n => -‖y‖^2/(4*t))
      ((-(4*t)⁻¹) • (2 • innerSL ℝ x)) x := by
    apply (hnorm.const_mul (-(4*t)⁻¹)).congr_of_eventuallyEq
    filter_upwards [] with y
    simp only [div_eq_mul_inv]
    ring
  have hmul := hinner.exp.const_mul (((4*Real.pi*t)^n)⁻¹)
  apply hmul.congr_fderiv
  ext v
  simp +instances only [smul_apply, smul_eq_mul, innerSL_apply_apply, Algebra.smul_def]
  unfold gaussianKernel
  field_simp [ht.ne', Real.pi_ne_zero]
  norm_num
  ring

theorem gaussianKernel_fderiv_apply {n : ℕ} {t : ℝ} (ht : 0 < t) (x v : Space n) :
    fderiv ℝ (gaussianKernel t) x v =
      -gaussianKernel t x/(2*t) * inner ℝ x v := by
  rw [(gaussianKernel_hasFDerivAt ht x).fderiv]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
theorem gaussianKernel_secondFDeriv_apply {n : ℕ} {t : ℝ}
    (ht : 0 < t) (x v w : Space n) :
    fderiv ℝ (fderiv ℝ (gaussianKernel t)) x v w =
      gaussianKernel t x * (inner ℝ x v * inner ℝ x w/(4*t^2) - inner ℝ v w/(2*t)) := by
  have hK : DifferentiableAt ℝ (gaussianKernel t) x :=
    (gaussianKernel_hasFDerivAt ht x).differentiableAt
  have hfd : DifferentiableAt ℝ (fderiv ℝ (gaussianKernel t)) x :=
    ((gaussianKernel_spatial_smooth t).contDiffAt.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  let c : ℝ := -(2*t)⁻¹
  have heq : (fun y : Space n => fderiv ℝ (gaussianKernel t) y w) =
      fun y => (c*gaussianKernel t y) * inner ℝ y w := by
    funext y
    rw [gaussianKernel_fderiv_apply ht y w]
    dsimp [c]
    ring
  have hi : DifferentiableAt ℝ (fun y : Space n => inner ℝ y w) x :=
    (innerSLFlip ℝ w).differentiableAt
  have hifd : fderiv ℝ (fun y : Space n => inner ℝ y w) x = innerSLFlip ℝ w :=
    (innerSLFlip ℝ w).fderiv
  calc
    fderiv ℝ (fderiv ℝ (gaussianKernel t)) x v w =
        fderiv ℝ (fun y : Space n => fderiv ℝ (gaussianKernel t) y w) x v := by
      rw [fderiv_clm_apply hfd (differentiableAt_const w)]
      simp
    _ = fderiv ℝ (fun y : Space n => (c*gaussianKernel t y) * inner ℝ y w) x v := by rw [heq]
    _ = _ := by
      rw [fderiv_fun_mul (hK.const_mul c) hi, fderiv_const_mul hK c, hifd]
      simp +instances only [add_apply, smul_apply, smul_eq_mul]
      rw [gaussianKernel_fderiv_apply ht x v]
      have hinner : (innerSLFlip ℝ w) v = inner ℝ v w := innerSLFlip_apply_apply ℝ w v
      rw [hinner]
      dsimp [c]
      field_simp
      ring

set_option backward.isDefEq.respectTransparency.types false in
theorem gaussianKernel_prefactor_hasDerivAt {n : ℕ} {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => ((4*Real.pi*s)^n)⁻¹)
      (-(n:ℝ)/t * ((4*Real.pi*t)^n)⁻¹) t := by
  have hb : 4*Real.pi*t ≠ 0 := by positivity
  have hraw := (((hasDerivAt_id t).const_mul (4*Real.pi)).pow n).inv (pow_ne_zero n hb)
  have hh : HasDerivAt (fun s : ℝ => ((4*Real.pi*s)^n)⁻¹)
      (-((n:ℝ)*(4*Real.pi*t)^(n-1)*(4*Real.pi)) / ((4*Real.pi*t)^n)^2) t := by
    convert hraw using 1
    · funext s
      rfl
    · simp only [Pi.pow_apply, id_eq, mul_one]
  apply hh.congr_deriv
  cases n with
  | zero => simp
  | succ k =>
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
    field_simp [ht.ne', Real.pi_ne_zero]

set_option backward.isDefEq.respectTransparency.types false in
theorem gaussianKernel_exponent_hasDerivAt {n : ℕ} {t : ℝ} (ht : 0 < t) (x : Space n) :
    HasDerivAt (fun s : ℝ => -‖x‖^2/(4*s)) (‖x‖^2/(4*t^2)) t := by
  have hb : 4*t ≠ 0 := by positivity
  have hraw := (((hasDerivAt_id t).const_mul (4 : ℝ)).inv hb).const_mul (-‖x‖^2)
  have hh : HasDerivAt (fun s : ℝ => -‖x‖^2/(4*s))
      ((-‖x‖^2)*(-4/(4*t)^2)) t := by
    convert hraw using 1
    · funext s
      simp only [Pi.inv_apply, id_eq, div_eq_mul_inv]
    · simp only [id_eq, mul_one]
  apply hh.congr_deriv
  field_simp

set_option backward.isDefEq.respectTransparency.types false in
theorem gaussianKernel_hasDerivAt {n : ℕ} {t : ℝ} (ht : 0 < t) (x : Space n) :
    HasDerivAt (fun s : ℝ => gaussianKernel s x)
      (gaussianKernel t x * (‖x‖^2/(4*t^2) - (n:ℝ)/t)) t := by
  have hc := gaussianKernel_prefactor_hasDerivAt (n := n) ht
  have he := (gaussianKernel_exponent_hasDerivAt ht x).exp
  have hprod := hc.mul he
  have hh : HasDerivAt (fun s : ℝ => gaussianKernel s x)
      ((-(n:ℝ)/t * ((4*Real.pi*t)^n)⁻¹) * Real.exp (-‖x‖^2/(4*t)) +
        ((4*Real.pi*t)^n)⁻¹ * (Real.exp (-‖x‖^2/(4*t)) * (‖x‖^2/(4*t^2)))) t := by
    convert hprod using 1
    rfl
  apply hh.congr_deriv
  unfold gaussianKernel
  ring

/-- Any nonnegative power is absorbed by a fixed amount of Gaussian decay. -/
theorem gaussian_weight_bounded {s b : ℝ} (hs : 0 ≤ s) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 ≤ r → r^s * Real.exp (-b*r^2) ≤ C := by
  let f : ℝ → ℝ := fun r => r^s * Real.exp (-b*r^2)
  have hf : Continuous f :=
    (Real.continuous_rpow_const hs).mul (by fun_prop)
  have hhalf : Tendsto (fun r : ℝ => (1/2 : ℝ)*r) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  have hexp : Tendsto (fun r : ℝ => Real.exp (-(1/2 : ℝ)*r)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp hhalf
  have hlim : Tendsto f atTop (𝓝 0) :=
    (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg hb s).tendsto_zero_of_tendsto hexp
  have hev : ∀ᶠ r in atTop, f r < 1 := hlim.eventually (gt_mem_nhds zero_lt_one)
  obtain ⟨R, hR⟩ := eventually_atTop.mp hev
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := max R 0)).bddAbove_image hf.continuousOn
  refine ⟨max 1 C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro r hr
  by_cases hrR : r ≤ max R 0
  · exact (hC ⟨r, ⟨hr, hrR⟩, rfl⟩).trans (le_max_right _ _)
  · exact (hR r ((le_max_left _ _).trans (le_of_not_ge hrR))).le.trans (le_max_left _ _)

theorem integrable_rpow_mul_exp_neg_norm_sq {n : ℕ} {s b : ℝ}
    (hs : 0 ≤ s) (hb : 0 < b) :
    Integrable (fun x : Space n => ‖x‖^s * Real.exp (-b*‖x‖^2)) := by
  obtain ⟨C, hC, hbound⟩ := gaussian_weight_bounded hs (show 0 < b/2 by positivity)
  have hmajor := (integrable_exp_neg_norm_sq (n := n) (show 0 < b/2 by positivity)).const_mul C
  have hcont : Continuous (fun x : Space n => ‖x‖^s * Real.exp (-b*‖x‖^2)) :=
    ((Real.continuous_rpow_const hs).comp continuous_norm).mul (by fun_prop)
  apply hmajor.mono' hcont.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (norm_nonneg x) s)
    (Real.exp_pos _).le)]
  calc
    ‖x‖^s * Real.exp (-b*‖x‖^2) =
        (‖x‖^s * Real.exp (-(b/2)*‖x‖^2)) * Real.exp (-(b/2)*‖x‖^2) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ C * Real.exp (-(b/2)*‖x‖^2) :=
      mul_le_mul_of_nonneg_right (hbound ‖x‖ (norm_nonneg x)) (Real.exp_pos _).le

theorem gaussianKernel_weight_integrable {n : ℕ} {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 < t) :
    Integrable (fun x : Space n => ‖x‖^s * gaussianKernel t x) := by
  have hh := (integrable_rpow_mul_exp_neg_norm_sq (n := n) hs
    (show 0 < (4*t)⁻¹ by positivity)).const_mul (((4*Real.pi*t)^n)⁻¹)
  convert hh using 1
  funext x
  unfold gaussianKernel
  have heq : -‖x‖^2/(4*t) = -(4*t)⁻¹*‖x‖^2 := by
    simp only [div_eq_mul_inv]
    ring
  rw [heq]
  ring

theorem real_inner_single {n : ℕ} (x : Space n) (i : Fin n) (z : ℂ) :
    inner ℝ x (EuclideanSpace.single i z) = inner ℝ (x i) z := by
  rw [PiLp.inner_apply, Finset.sum_eq_single i]
  · simp only [PiLp.single_apply, ite_true]
  · intro j hj hji
    simp [hji]
  · simp

theorem realVec_eq_single {n : ℕ} (a : Yau.RIdx n) :
    Yau.realVec a = EuclideanSpace.single a.1 (if a.2 = 0 then 1 else Complex.I) := by
  by_cases ha : a.2 = 0
  · simp [Yau.realVec, ha]
  · ext k
    simp [Yau.realVec, ha, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul]

theorem real_inner_realVec {n : ℕ} (x : Space n) (a : Yau.RIdx n) :
    inner ℝ x (Yau.realVec a) = Yau.realCoord x a := by
  rw [realVec_eq_single, real_inner_single]
  unfold Yau.realCoord
  split_ifs
  · rw [Complex.inner, one_mul]
    exact Complex.conj_re _
  · rw [Complex.inner, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.conj_im]
    ring

theorem realVec_norm {n : ℕ} (a : Yau.RIdx n) : ‖Yau.realVec a‖ = 1 := by
  by_cases h : a.2 = 0 <;> simp [Yau.realVec, h, norm_smul]

theorem sum_realCoord_sq {n : ℕ} (x : Space n) :
    (∑ a : Yau.RIdx n, (Yau.realCoord x a)^2) = ‖x‖^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Yau.realCoord,
    ite_eq_right (by decide : (1 : Fin 2) ≠ 0), ite_true]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem gaussianKernel_time_eq_laplacian {n : ℕ} {t : ℝ} (ht : 0 < t) (x : Space n) :
    deriv (fun s : ℝ => gaussianKernel s x) t =
      ∑ i : Yau.RIdx n, fderiv ℝ (fderiv ℝ (gaussianKernel t)) x (Yau.realVec i) (Yau.realVec i) := by
  rw [(gaussianKernel_hasDerivAt ht x).deriv]
  have hsecond : ∀ i : Yau.RIdx n,
      fderiv ℝ (fderiv ℝ (gaussianKernel t)) x (Yau.realVec i) (Yau.realVec i) =
        gaussianKernel t x * ((Yau.realCoord x i)^2/(4*t^2) - 1/(2*t)) := by
    intro i
    rw [gaussianKernel_secondFDeriv_apply ht, real_inner_self_eq_norm_sq, realVec_norm]
    simp only [real_inner_realVec, pow_two, one_mul]
  simp_rw [hsecond]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_div, sum_realCoord_sq]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp [ht.ne']

/-- The positive-time Euclidean heat kernel solves the actual operator,
including its within derivative on the terminal face. -/
theorem gaussianKernel_linearOp_zero {n : ℕ} {T : ℝ} (hT : 0 < T)
    {p : Point n} (hp : p ∈ cylinder Set.univ 0 T) (hpt : 0 < p.2) :
    linearOp (cylinder Set.univ 0 T) (fun _ => (1 : Mat n)) (fun _ => 0)
      (fun z => gaussianKernel z.2 z.1) p = 0 := by
  have hfiber : {t | (p.1,t) ∈ cylinder (Set.univ : Set (Space n)) 0 T} = Set.Icc 0 T := by
    ext t
    simp [Yau.Parabolic.cylinder]
  have hD := gaussianKernel_hasDerivAt hpt p.1
  have htime : timeD (cylinder Set.univ 0 T) (fun z => gaussianKernel z.2 z.1) p =
      deriv (fun s => gaussianKernel s p.1) p.2 := by
    rw [hD.deriv]
    simpa only [timeD, hfiber] using
      hD.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hT p.2 hp.2)
  have hsum : (∑ i, ∑ j, (1 : Mat n) i j *
      spatialDD (fun z => gaussianKernel z.2 z.1) p (Yau.realVec i) (Yau.realVec j)) =
      ∑ i : Yau.RIdx n, fderiv ℝ (fderiv ℝ (gaussianKernel p.2)) p.1 (Yau.realVec i) (Yau.realVec i) := by
    simp [Matrix.one_apply, spatialDD]
  simp only [linearOp, Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero]
  rw [htime, hsum, gaussianKernel_time_eq_laplacian hpt p.1, sub_self]

theorem gaussian_weight_tendsto_zero {s b : ℝ} (hb : 0 < b) :
    Tendsto (fun r : ℝ => r^s * Real.exp (-b*r^2)) atTop (𝓝 0) := by
  have hhalf : Tendsto (fun r : ℝ => (1/2 : ℝ)*r) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  have hexp : Tendsto (fun r : ℝ => Real.exp (-(1/2 : ℝ)*r)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp hhalf
  exact (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg hb s).tendsto_zero_of_tendsto hexp

theorem gaussianKernel_decay {n : ℕ} :
    Tendsto (fun x : Space n => ‖x‖^(Module.finrank ℝ (Space n)) * gaussianKernel 1 x)
      (Bornology.cobounded (Space n)) (𝓝 0) := by
  have hrad := gaussian_weight_tendsto_zero
    (s := (Module.finrank ℝ (Space n) : ℝ)) (b := (4 : ℝ)⁻¹) (by norm_num)
  have hnorm : Tendsto (fun x : Space n => ‖x‖) (Bornology.cobounded (Space n)) atTop :=
    tendsto_norm_cobounded_atTop
  have hh := (hrad.comp hnorm).const_mul (((4*Real.pi)^n)⁻¹)
  simp only [Real.rpow_natCast, mul_zero] at hh
  have heq : (fun x : Space n => ‖x‖^(Module.finrank ℝ (Space n)) * gaussianKernel 1 x) =
      fun x => ((4*Real.pi)^n)⁻¹ * (‖x‖^(Module.finrank ℝ (Space n)) * Real.exp (-(4:ℝ)⁻¹*‖x‖^2)) := by
    funext x
    have harg : -‖x‖^2/4 = -(4:ℝ)⁻¹*‖x‖^2 := by ring
    simp only [gaussianKernel, mul_one, harg]
    ring
  rw [heq]
  exact hh

/-- The actual Gaussian profile is a peak family for integrable initial
data continuous at the evaluation point. -/
theorem gaussianKernel_peak_approx_identity {n : ℕ} {g : Space n → ℝ}
    (hg : Integrable g) (hgc : ContinuousAt g 0) :
    Tendsto (fun c : ℝ => ∫ x : Space n,
      (c^(Module.finrank ℝ (Space n)) * gaussianKernel 1 (c • x)) * g x) atTop (𝓝 (g 0)) := by
  simpa only [smul_eq_mul] using tendsto_integral_comp_smul_smul_of_integrable
    (μ := (volume : Measure (Space n))) (φ := gaussianKernel 1)
    (fun x => (gaussianKernel_pos (by norm_num : (0 : ℝ) < 1) x).le)
    (gaussianKernel_integral (n := n) (by norm_num : (0 : ℝ) < 1))
    gaussianKernel_decay hg hgc

theorem gaussianKernel_inv_sq_scaling {n : ℕ} (c : ℝ) (x : Space n) :
    gaussianKernel ((c^2)⁻¹) x = c^(2*n)*gaussianKernel 1 (c • x) := by
  have hnorm : ‖c • x‖^2 = c^2*‖x‖^2 := by
    simp [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hcoeff : ((4*Real.pi*(c^2)⁻¹)^n)⁻¹ = c^(2*n)*((4*Real.pi)^n)⁻¹ := by
    rw [pow_mul]
    simp only [mul_pow, mul_inv_rev, inv_pow, inv_inv]
  have harg : -‖x‖^2/(4*(c^2)⁻¹) = -(c^2*‖x‖^2)/4 := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  simp only [gaussianKernel, mul_one, hcoeff, hnorm, harg]
  ring

theorem gaussianKernel_inv_sq_approx_identity {n : ℕ} {g : Space n → ℝ}
    (hg : Integrable g) (hgc : ContinuousAt g 0) :
    Tendsto (fun c : ℝ => ∫ x : Space n, gaussianKernel ((c^2)⁻¹) x * g x)
      atTop (𝓝 (g 0)) := by
  simpa only [space_finrank_real, ← gaussianKernel_inv_sq_scaling] using
    gaussianKernel_peak_approx_identity hg hgc

/-- The actual positive-time kernels converge to the initial value,
with an ordinary right-time limit rather than a selected sequence. -/
theorem gaussianKernel_approx_identity {n : ℕ} {g : Space n → ℝ}
    (hg : Integrable g) (hgc : ContinuousAt g 0) :
    Tendsto (fun t : ℝ => ∫ x : Space n, gaussianKernel t x * g x)
      (𝓝[>] 0) (𝓝 (g 0)) := by
  have hroot0 : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).mono_left nhdsWithin_le_nhds
  have hroot : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hroot0, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact Real.sqrt_pos.mpr ht
  have hi : Tendsto (fun t : ℝ => (Real.sqrt t)⁻¹) (𝓝[>] 0) atTop :=
    tendsto_inv_nhdsGT_zero.comp hroot
  have hh := (gaussianKernel_inv_sq_approx_identity hg hgc).comp hi
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : 0 < t := ht
  have heq : (((Real.sqrt t)⁻¹)^2)⁻¹ = t := by
    rw [inv_pow, inv_inv, Real.sq_sqrt ht'.le]
  simp only [Function.comp_def, heq]

theorem gaussianKernel_weight_integral_inv_sq_scaling {n : ℕ} (s : ℝ)
    {c : ℝ} (hc : 0 < c) :
    (∫ x : Space n, ‖x‖^s * gaussianKernel ((c^2)⁻¹) x) =
      (c^s)⁻¹ * (∫ x : Space n, ‖x‖^s * gaussianKernel 1 x) := by
  have hcs : c^s ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hc s)
  have hnorm : ∀ x : Space n, ‖c • x‖^s = c^s * ‖x‖^s := by
    intro x
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc, Real.mul_rpow hc.le (norm_nonneg x)]
  have hform : (fun x : Space n => ‖x‖^s * gaussianKernel ((c^2)⁻¹) x) =
      fun x => (c^(2*n)/(c^s)) * (‖c • x‖^s * gaussianKernel 1 (c • x)) := by
    funext x
    rw [gaussianKernel_inv_sq_scaling, hnorm]
    field_simp
  rw [hform, integral_const_mul]
  have hh := Measure.integral_comp_smul_of_nonneg (volume : Measure (Space n))
    (fun x : Space n => ‖x‖^s * gaussianKernel 1 x) c (hR := hc.le)
  simp only [smul_eq_mul, space_finrank_real] at hh
  rw [hh]
  field_simp

theorem gaussianKernel_weight_integral {n : ℕ} (s : ℝ) {t : ℝ} (ht : 0 < t) :
    (∫ x : Space n, ‖x‖^s * gaussianKernel t x) =
      t^(s/2) * (∫ x : Space n, ‖x‖^s * gaussianKernel 1 x) := by
  have hc : 0 < (Real.sqrt t)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr ht)
  have hh := gaussianKernel_weight_integral_inv_sq_scaling (n := n) s hc
  have htime : (((Real.sqrt t)⁻¹)^2)⁻¹ = t := by
    rw [inv_pow, inv_inv, Real.sq_sqrt ht.le]
  have hpower : (((Real.sqrt t)⁻¹)^s)⁻¹ = t^(s/2) := by
    rw [Real.inv_rpow (Real.sqrt_nonneg t), inv_inv, Real.sqrt_eq_rpow,
      ← Real.rpow_mul ht.le]
    congr 1
    ring
  rw [htime, hpower] at hh
  exact hh

/-- A fixed, finite Gaussian moment controls every positive time with
the correct parabolic power. Integrability is included explicitly. -/
theorem gaussianKernel_weight_integral_bound {n : ℕ} {s : ℝ} (hs : 0 ≤ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t →
      Integrable (fun x : Space n => ‖x‖^s * gaussianKernel t x) ∧
      (∫ x : Space n, ‖x‖^s * gaussianKernel t x) ≤ C*t^(s/2) := by
  let M : ℝ := ∫ x : Space n, ‖x‖^s * gaussianKernel 1 x
  refine ⟨|M|+1, by positivity, ?_⟩
  intro t ht
  refine ⟨gaussianKernel_weight_integrable hs ht, ?_⟩
  rw [gaussianKernel_weight_integral s ht]
  have hM : M ≤ |M|+1 := by linarith [le_abs_self M]
  simpa only [M, mul_comm] using
    mul_le_mul_of_nonneg_left hM (Real.rpow_nonneg ht.le (s/2))

theorem gaussianKernel_fderiv_norm {n : ℕ} {t : ℝ} (ht : 0 < t) (x : Space n) :
    ‖fderiv ℝ (gaussianKernel t) x‖ = gaussianKernel t x * ‖x‖/(2*t) := by
  have hκ : 0 < gaussianKernel t x := gaussianKernel_pos ht x
  rw [(gaussianKernel_hasFDerivAt ht x).fderiv, norm_smul, Real.norm_eq_abs,
    abs_div, abs_neg, abs_of_pos hκ, abs_of_pos (show 0 < 2*t by positivity), innerSL_apply_norm]
  ring

theorem gaussianKernel_secondFDeriv_norm_le {n : ℕ} {t : ℝ}
    (ht : 0 < t) (x : Space n) :
    ‖fderiv ℝ (fderiv ℝ (gaussianKernel t)) x‖ ≤
      gaussianKernel t x * (‖x‖^2/(4*t^2) + 1/(2*t)) := by
  let C : ℝ := gaussianKernel t x * (‖x‖^2/(4*t^2) + 1/(2*t))
  have hκ : 0 < gaussianKernel t x := gaussianKernel_pos ht x
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply (fderiv ℝ (fderiv ℝ (gaussianKernel t)) x).opNorm_le_bound hC
  intro v
  apply (fderiv ℝ (fderiv ℝ (gaussianKernel t)) x v).opNorm_le_bound
    (mul_nonneg hC (norm_nonneg v))
  intro w
  rw [Real.norm_eq_abs, gaussianKernel_secondFDeriv_apply ht, abs_mul, abs_of_pos hκ]
  have hA : |inner ℝ x v * inner ℝ x w/(4*t^2)| ≤
      ‖x‖^2/(4*t^2) * ‖v‖ * ‖w‖ := by
    rw [abs_div, abs_mul, abs_of_pos (show 0 < 4*t^2 by positivity)]
    have hprod := mul_le_mul (abs_real_inner_le_norm x v) (abs_real_inner_le_norm x w)
      (abs_nonneg (inner ℝ x w)) (mul_nonneg (norm_nonneg x) (norm_nonneg v))
    have hh := div_le_div_of_nonneg_right hprod (show 0 ≤ 4*t^2 by positivity)
    simpa only [div_eq_mul_inv, pow_two, mul_assoc, mul_comm, mul_left_comm] using hh
  have hB : |inner ℝ v w/(2*t)| ≤ (1/(2*t)) * ‖v‖ * ‖w‖ := by
    rw [abs_div, abs_of_pos (show 0 < 2*t by positivity)]
    have hh := div_le_div_of_nonneg_right (abs_real_inner_le_norm v w) (show 0 ≤ 2*t by positivity)
    simpa only [div_eq_mul_inv, one_mul, mul_assoc, mul_comm, mul_left_comm] using hh
  have habs := abs_sub (inner ℝ x v * inner ℝ x w/(4*t^2)) (inner ℝ v w/(2*t))
  have hsum := habs.trans (add_le_add hA hB)
  have hh := mul_le_mul_of_nonneg_left hsum hκ.le
  convert hh using 1
  dsimp [C]
  ring

theorem gaussianKernel_secondFDeriv_weight_integrable_bound {n : ℕ} {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 < t) :
    Integrable (fun x : Space n => ‖fderiv ℝ (fderiv ℝ (gaussianKernel t)) x‖ * ‖x‖^s) ∧
    (∫ x : Space n, ‖fderiv ℝ (fderiv ℝ (gaussianKernel t)) x‖ * ‖x‖^s) ≤
      (1/(4*t^2)) * (∫ x : Space n, ‖x‖^(s+2)*gaussianKernel t x) +
        (1/(2*t)) * (∫ x : Space n, ‖x‖^s*gaussianKernel t x) := by
  let g2 : Space n → ℝ := fun x => (1/(4*t^2)) * (‖x‖^(s+2)*gaussianKernel t x)
  let g0 : Space n → ℝ := fun x => (1/(2*t)) * (‖x‖^s*gaussianKernel t x)
  have h2 : Integrable g2 :=
    (gaussianKernel_weight_integrable (show 0 ≤ s+2 by linarith) ht).const_mul _
  have h0 : Integrable g0 := (gaussianKernel_weight_integrable hs ht).const_mul _
  have hpow : ∀ x : Space n, ‖x‖^(s+2) = ‖x‖^s * ‖x‖^2 := by
    intro x
    rw [Real.rpow_add_of_nonneg (norm_nonneg x) hs (by norm_num), Real.rpow_two]
  have hpoint : ∀ x : Space n,
      ‖fderiv ℝ (fderiv ℝ (gaussianKernel t)) x‖ * ‖x‖^s ≤ g2 x + g0 x := by
    intro x
    have hh := mul_le_mul_of_nonneg_right (gaussianKernel_secondFDeriv_norm_le ht x)
      (Real.rpow_nonneg (norm_nonneg x) s)
    convert hh using 1
    dsimp [g2, g0]
    rw [hpow]
    ring
  have hHcont : Continuous (fun x : Space n => fderiv ℝ (fderiv ℝ (gaussianKernel t)) x) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (((gaussianKernel_spatial_smooth t).contDiffAt.fderiv_right (m := 1) (by norm_num)).fderiv_right
      (m := 0) (by norm_num)).continuousAt
  have hnormMap : Continuous (fun A : Space n →L[ℝ] Space n →L[ℝ] ℝ => ‖A‖) :=
    continuous_norm (E := Space n →L[ℝ] Space n →L[ℝ] ℝ)
  have hnormH : Continuous (fun x : Space n => ‖fderiv ℝ (fderiv ℝ (gaussianKernel t)) x‖) :=
    hnormMap.comp hHcont
  have hnormPow : Continuous (fun x : Space n => ‖x‖^s) :=
    (Real.continuous_rpow_const hs).comp continuous_norm
  have hfcont : Continuous (fun x : Space n => ‖fderiv ℝ (fderiv ℝ (gaussianKernel t)) x‖ * ‖x‖^s) :=
    hnormH.mul hnormPow
  have hi : Integrable (fun x : Space n => ‖fderiv ℝ (fderiv ℝ (gaussianKernel t)) x‖ * ‖x‖^s) := by
    apply (h2.add h0).mono' hfcont.aestronglyMeasurable
    filter_upwards [] with x
    have hnonneg : 0 ≤ ‖fderiv ℝ (fderiv ℝ (gaussianKernel t)) x‖ * ‖x‖^s :=
      mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) (Real.rpow_nonneg (norm_nonneg x) s)
    rw [Real.norm_of_nonneg hnonneg]
    exact hpoint x
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x : Space n, g2 x + g0 x := integral_mono_ae hi (h2.add h0) (ae_of_all _ hpoint)
    _ = _ := by
      rw [integral_add h2 h0]
      simp only [g2, g0, integral_const_mul]

theorem gaussianKernel_secondFDeriv_weight_bound {n : ℕ} {s : ℝ} (hs : 0 ≤ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t →
      Integrable (fun x : Space n => ‖fderiv ℝ (fderiv ℝ (gaussianKernel t)) x‖ * ‖x‖^s) ∧
      (∫ x : Space n, ‖fderiv ℝ (fderiv ℝ (gaussianKernel t)) x‖ * ‖x‖^s) ≤ C*t^(s/2-1) := by
  let M2 : ℝ := ∫ x : Space n, ‖x‖^(s+2)*gaussianKernel 1 x
  let M0 : ℝ := ∫ x : Space n, ‖x‖^s*gaussianKernel 1 x
  let C : ℝ := |M2|+|M0|+1
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro t ht
  have hi := gaussianKernel_secondFDeriv_weight_integrable_bound (n := n) hs ht
  refine ⟨hi.1, ?_⟩
  have hbound := hi.2
  rw [gaussianKernel_weight_integral (s+2) ht, gaussianKernel_weight_integral s ht] at hbound
  have hpower : t^((s+2)/2) = t^(s/2)*t := by
    have heq : (s+2)/2 = s/2+1 := by ring
    rw [heq, Real.rpow_add ht, Real.rpow_one]
  have hRHS : (1/(4*t^2)) * (t^((s+2)/2)*M2) + (1/(2*t)) * (t^(s/2)*M0) =
      (M2/4+M0/2)*t^(s/2-1) := by
    rw [hpower, Real.rpow_sub_one ht.ne']
    field_simp
  rw [hRHS] at hbound
  have hcoeff : M2/4+M0/2 ≤ C := by
    dsimp [C]
    linarith [le_abs_self M2, le_abs_self M0, abs_nonneg M2, abs_nonneg M0]
  exact hbound.trans (mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg ht.le _))

def heatAverage {n : ℕ} (t : ℝ) (g : Space n → ℝ) : Space n → ℝ :=
  convolution (gaussianKernel t) g (ContinuousLinearMap.lsmul ℝ ℝ) volume
theorem heatAverage_def {n : ℕ} (t : ℝ) (g : Space n → ℝ) (x : Space n) :
    heatAverage t g x = ∫ y : Space n, gaussianKernel t y * g (x-y) := rfl
theorem heatAverage_integrable_of_bounded {n : ℕ} {t B : ℝ} {g : Space n → ℝ}
    (ht : 0 < t) (hg : Continuous g) (hB : ∀ y, |g y| ≤ B) (x : Space n) :
    Integrable (fun y : Space n => gaussianKernel t y * g (x-y)) := by
  have hshift : Continuous (fun y : Space n => g (x-y)) :=
    hg.comp (continuous_const.sub continuous_id)
  apply (gaussianKernel_integrable ht).mul_bdd hshift.aestronglyMeasurable
  filter_upwards [] with y
  simpa only [Real.norm_eq_abs] using hB (x-y)
theorem heatAverage_bound {n : ℕ} {t B : ℝ} {g : Space n → ℝ}
    (ht : 0 < t) (hg : Continuous g) (hB : ∀ y, |g y| ≤ B) (x : Space n) :
    |heatAverage t g x| ≤ B := by
  have hi := heatAverage_integrable_of_bounded ht hg hB x
  have hm := (gaussianKernel_integrable (n := n) ht).const_mul B
  have hpoint : ∀ y : Space n, ‖gaussianKernel t y * g (x-y)‖ ≤ B*gaussianKernel t y := by
    intro y
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (gaussianKernel_pos ht y)]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (hB (x-y)) (gaussianKernel_pos ht y).le
  rw [heatAverage_def]
  calc
    |∫ y : Space n, gaussianKernel t y * g (x-y)| =
        ‖∫ y : Space n, gaussianKernel t y * g (x-y)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ y : Space n, ‖gaussianKernel t y * g (x-y)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y : Space n, B*gaussianKernel t y := integral_mono_ae hi.norm hm (ae_of_all _ hpoint)
    _ = B := by rw [integral_const_mul, gaussianKernel_integral ht, mul_one]
theorem heatAverage_spatial_smooth {n : ℕ} {t : ℝ} {g : Space n → ℝ} (ht : 0 < t)
    (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) :
    ContDiff ℝ ∞ (heatAverage t g) := by
  exact hcg.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    (gaussianKernel_integrable ht).locallyIntegrable hg
theorem heatAverage_initial_limit {n : ℕ} {g : Space n → ℝ} (hg : Integrable g) {x : Space n}
    (hgc : ContinuousAt g x) :
    Tendsto (fun t : ℝ => heatAverage t g x) (𝓝[>] 0) (𝓝 (g x)) := by
  have hgi : Integrable (fun y : Space n => g (x-y)) := hg.comp_sub_left x
  have hcontsub : Continuous (fun y : Space n => x-y) := continuous_const.sub continuous_id
  have hsub : Tendsto (fun y : Space n => x-y) (𝓝 0) (𝓝 x) := by
    simpa only [sub_zero] using hcontsub.tendsto (0 : Space n)
  have hshift : ContinuousAt (fun y : Space n => g (x-y)) 0 := by
    have hh := (show Tendsto g (𝓝 x) (𝓝 (g x)) from hgc).comp hsub
    simpa only [ContinuousAt, Function.comp_def, sub_zero] using hh
  simpa only [heatAverage_def, sub_zero] using gaussianKernel_approx_identity hgi hshift

theorem heatAverage_fderiv_apply {n : ℕ} {t : ℝ} {g : Space n → ℝ}
    (ht : 0 < t) (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (x v : Space n) :
    fderiv ℝ (heatAverage t g) x v = heatAverage t (fun y => fderiv ℝ g y v) x := by
  have hd := hcg.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    (gaussianKernel_integrable ht).locallyIntegrable (hg.of_le (by simp)) x
  rw [show fderiv ℝ (heatAverage t g) x =
      convolution (gaussianKernel t) (fderiv ℝ g)
        ((ContinuousLinearMap.lsmul ℝ ℝ).precompR (Space n)) volume x from hd.fderiv]
  exact convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ)
    (gaussianKernel_integrable ht).locallyIntegrable (hcg.fderiv ℝ)
    (hg.continuous_fderiv (by simp)) x v

theorem heatAverage_secondFDeriv_apply {n : ℕ} {t : ℝ} {g : Space n → ℝ}
    (ht : 0 < t) (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (x v w : Space n) :
    fderiv ℝ (fderiv ℝ (heatAverage t g)) x v w =
      heatAverage t (fun y => fderiv ℝ (fderiv ℝ g) y v w) x := by
  have hgs : ContDiff ℝ ∞ (fderiv ℝ g) := hg.fderiv_right (by simp)
  have hHs : ContDiff ℝ ∞ (fderiv ℝ (heatAverage t g)) :=
    (heatAverage_spatial_smooth ht hg hcg).fderiv_right (by simp)
  have heq : (fun y => fderiv ℝ (heatAverage t g) y w) =
      heatAverage t (fun y => fderiv ℝ g y w) :=
    funext (fun y => heatAverage_fderiv_apply ht hg hcg y w)
  have hleft : fderiv ℝ (fun y => fderiv ℝ (heatAverage t g) y w) x v =
      fderiv ℝ (fderiv ℝ (heatAverage t g)) x v w := by
    rw [fderiv_clm_apply (hHs.differentiable (by simp)).differentiableAt
      (differentiableAt_const w)]
    simp
  have hright : (fun y => fderiv ℝ (fun z => fderiv ℝ g z w) y v) =
      (fun y => fderiv ℝ (fderiv ℝ g) y v w) := by
    funext y
    rw [fderiv_clm_apply (hgs.differentiable (by simp)).differentiableAt
      (differentiableAt_const w)]
    simp
  rw [← hleft, heq, heatAverage_fderiv_apply ht
    (hgs.clm_apply contDiff_const) (hcg.fderiv_apply ℝ w), hright]

theorem compact_smul_integrable {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : Space n → ℝ} {F : Space n → E}
    (hg : Continuous g) (hcg : HasCompactSupport g) (hF : Continuous F) :
    Integrable (fun y => g y • F y) := by
  exact (hg.smul hF).integrable_of_hasCompactSupport hcg.smul_right

theorem compact_integral_hasFDerivAt {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : Space n → Space n → E} {F' : Space n → Space n → Space n →L[ℝ] E}
    {g : Space n → ℝ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (hF : Continuous (Function.uncurry F)) (hF' : Continuous (Function.uncurry F'))
    (hd : ∀ x y, HasFDerivAt (fun z => F z y) (F' x y) x) (x : Space n) :
    HasFDerivAt (fun z => ∫ y : Space n, g y • F z y)
      (∫ y : Space n, g y • F' x y) x := by
  have hnorm : Continuous (fun A : Space n →L[ℝ] E => ‖A‖) :=
    continuous_norm (E := Space n →L[ℝ] E)
  obtain ⟨C,hC⟩ := ((isCompact_closedBall x 1).prod hcg).bddAbove_image
    (hnorm.comp hF').continuousOn
  have hFc (z : Space n) : Continuous (fun y => g y • F z y) :=
    hg.smul (hF.comp (continuous_const.prodMk continuous_id))
  have hF'c (z : Space n) : Continuous (fun y => g y • F' z y) :=
    hg.smul (hF'.comp (continuous_const.prodMk continuous_id))
  have hgi := hg.integrable_of_hasCompactSupport hcg (μ := volume)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Metric.ball x 1) (bound := fun y => C*|g y|)
    (Metric.ball_mem_nhds x (by norm_num))
    (Eventually.of_forall fun z => (hFc z).aestronglyMeasurable)
    ((hFc x).integrable_of_hasCompactSupport hcg.smul_right)
    (hF'c x).aestronglyMeasurable
    (ae_of_all _ fun y z hz => ?_)
    (hgi.abs.const_mul C)
    (ae_of_all _ fun y z _ => (hd z y).const_smul (g y))
  rw [norm_smul, Real.norm_eq_abs]
  by_cases hy : g y = 0
  · simp [hy]
  · have hyS : y ∈ tsupport g := subset_tsupport _ (by simpa [Function.mem_support] using hy)
    have hc := hC ⟨(z,y), ⟨Metric.ball_subset_closedBall hz,hyS⟩,rfl⟩
    simpa only [Function.comp_apply, Function.uncurry_apply_pair, mul_comm] using mul_le_mul_of_nonneg_left hc (abs_nonneg (g y))

theorem heatAverage_fderiv_kernel {n : ℕ} {t : ℝ} {g : Space n → ℝ}
    (hg : Continuous g) (hcg : HasCompactSupport g) (x : Space n) :
    fderiv ℝ (heatAverage t g) x =
      ∫ y : Space n, g y • fderiv ℝ (gaussianKernel t) (x-y) := by
  have hKs := gaussianKernel_spatial_smooth (n := n) t
  have hK' := hKs.continuous_fderiv (by simp)
  have hd : ∀ z y : Space n, HasFDerivAt (fun v => gaussianKernel t (v-y))
      (fderiv ℝ (gaussianKernel t) (z-y)) z := by
    intro z y
    simpa using! (hKs.differentiable (by simp) (z-y)).hasFDerivAt.comp z
      ((hasFDerivAt_id z).sub (hasFDerivAt_const y z))
  have hi := compact_integral_hasFDerivAt
    (F := fun z y : Space n => gaussianKernel t (z-y))
    (F' := fun z y : Space n => fderiv ℝ (gaussianKernel t) (z-y)) hg hcg
    (hKs.continuous.comp (continuous_fst.sub continuous_snd))
    (hK'.comp (continuous_fst.sub continuous_snd)) hd x
  have heq : (fun z : Space n => ∫ y : Space n, g y • gaussianKernel t (z-y)) =
      heatAverage t g := by
    funext z
    rw [heatAverage, convolution_eq_swap]
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, mul_comm]
  rw [heq] at hi
  exact hi.fderiv

theorem heatAverage_secondFDeriv_kernel {n : ℕ} {t : ℝ} {g : Space n → ℝ}
    (hg : Continuous g) (hcg : HasCompactSupport g) (x : Space n) :
    fderiv ℝ (fderiv ℝ (heatAverage t g)) x =
      ∫ y : Space n, g y • fderiv ℝ (fderiv ℝ (gaussianKernel t)) (x-y) := by
  have hKs := (gaussianKernel_spatial_smooth (n := n) t).fderiv_right (m := ∞) (by simp)
  have hK' := hKs.continuous_fderiv (by simp)
  have hd : ∀ z y : Space n, HasFDerivAt (fun v => fderiv ℝ (gaussianKernel t) (v-y))
      (fderiv ℝ (fderiv ℝ (gaussianKernel t)) (z-y)) z := by
    intro z y
    simpa using! (hKs.differentiable (by simp) (z-y)).hasFDerivAt.comp z
      ((hasFDerivAt_id z).sub (hasFDerivAt_const y z))
  have hi := compact_integral_hasFDerivAt
    (F := fun z y : Space n => fderiv ℝ (gaussianKernel t) (z-y))
    (F' := fun z y : Space n => fderiv ℝ (fderiv ℝ (gaussianKernel t)) (z-y)) hg hcg
    (hKs.continuous.comp (continuous_fst.sub continuous_snd))
    (hK'.comp (continuous_fst.sub continuous_snd)) hd x
  have heq : (fun z : Space n => ∫ y : Space n, g y • fderiv ℝ (gaussianKernel t) (z-y)) =
      fderiv ℝ (heatAverage t g) := by
    funext z
    exact (heatAverage_fderiv_kernel hg hcg z).symm
  rw [heq] at hi
  exact hi.fderiv

theorem heatAverage_hasDerivAt {n : ℕ} {t : ℝ} {g : Space n → ℝ}
    (ht : 0 < t) (hg : Continuous g) (hcg : HasCompactSupport g) (x : Space n) :
    HasDerivAt (fun s : ℝ => heatAverage s g x)
      (∫ y : Space n, (gaussianKernel t (x-y) *
        (‖x-y‖^2/(4*t^2) - (n:ℝ)/t))*g y) t := by
  let D : ℝ → Space n → ℝ := fun s y => gaussianKernel s (x-y) *
    (‖x-y‖^2/(4*s^2) - (n:ℝ)/s)
  have hDc (s : ℝ) : Continuous (D s) := by
    dsimp [D, gaussianKernel]
    fun_prop
  have hKc (s : ℝ) : Continuous (fun y : Space n => gaussianKernel s (x-y)) := by
    unfold gaussianKernel
    fun_prop
  have hDjoint : ContinuousOn (fun p : ℝ × Space n => |D p.1 p.2|)
      (Set.Icc (t/2) (2*t) ×ˢ tsupport g) := by
    intro p hp
    have hp0 : 0 < p.1 := lt_of_lt_of_le (half_pos ht) hp.1.1
    apply ContinuousAt.continuousWithinAt
    dsimp [D, gaussianKernel]
    fun_prop (disch := positivity)
  obtain ⟨C, hC⟩ := ((isCompact_Icc).prod hcg).bddAbove_image hDjoint
  have hgi : Integrable g := hg.integrable_of_hasCompactSupport hcg
  have hF_int : Integrable (fun y : Space n => gaussianKernel t (x-y)*g y) :=
    ((hKc t).mul hg).integrable_of_hasCompactSupport hcg.mul_left
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s (y : Space n) => gaussianKernel s (x-y)*g y)
    (F' := fun s y => D s y * g y)
    (bound := fun y => C*|g y|)
    (s := Set.Ioo (t/2) (2*t))
    (Ioo_mem_nhds (by linarith : t/2 < t) (by linarith : t < 2*t))
    (Eventually.of_forall fun s => ((hKc s).mul hg).aestronglyMeasurable)
    hF_int ((hDc t).mul hg).aestronglyMeasurable
    (ae_of_all _ fun y s hs => ?_)
    (hgi.abs.const_mul C)
    (ae_of_all _ fun y s hs => ?_)
  · convert hres.2 using 1
    funext s
    exact convolution_eq_swap (ContinuousLinearMap.lsmul ℝ ℝ)
  · rw [Real.norm_eq_abs, abs_mul]
    by_cases hy : g y = 0
    · simp [hy]
    · have hyS : y ∈ tsupport g := subset_tsupport _ (by simpa [Function.mem_support] using hy)
      exact mul_le_mul_of_nonneg_right
        (hC ⟨(s,y), ⟨⟨hs.1.le, hs.2.le⟩,hyS⟩, rfl⟩) (abs_nonneg _)
  · have hs0 : 0 < s := lt_trans (half_pos ht) hs.1
    exact (gaussianKernel_hasDerivAt hs0 (x-y)).mul_const (g y)

theorem heatAverage_time_eq_laplacian {n : ℕ} {t : ℝ} {g : Space n → ℝ}
    (ht : 0 < t) (hg : Continuous g) (hcg : HasCompactSupport g) (x : Space n) :
    deriv (fun s : ℝ => heatAverage s g x) t =
      ∑ i : Yau.RIdx n, fderiv ℝ (fderiv ℝ (heatAverage t g)) x
        (Yau.realVec i) (Yau.realVec i) := by
  have hKs := (gaussianKernel_spatial_smooth (n := n) t).fderiv_right (m := ∞) (by simp)
  have hK'' := hKs.continuous_fderiv (by simp)
  have hiH := compact_smul_integrable (E := Space n →L[ℝ] Space n →L[ℝ] ℝ)
    (F := fun y : Space n => fderiv ℝ (fderiv ℝ (gaussianKernel t)) (x-y))
    hg hcg (hK''.comp (continuous_const.sub continuous_id))
  have happ (v w : Space n) : fderiv ℝ (fderiv ℝ (heatAverage t g)) x v w =
      ∫ y : Space n, g y * fderiv ℝ (fderiv ℝ (gaussianKernel t)) (x-y) v w := by
    have hiv : Integrable (fun y : Space n =>
        (g y • fderiv ℝ (fderiv ℝ (gaussianKernel t)) (x-y)) v) := by
      change Integrable (fun y : Space n =>
        g y • fderiv ℝ (fderiv ℝ (gaussianKernel t)) (x-y) v)
      exact compact_smul_integrable
        (F := fun y : Space n => fderiv ℝ (fderiv ℝ (gaussianKernel t)) (x-y) v)
        hg hcg ((hK''.comp (continuous_const.sub continuous_id)).clm_apply continuous_const)
    rw [heatAverage_secondFDeriv_kernel hg hcg x,
      ContinuousLinearMap.integral_apply hiH v,
      ContinuousLinearMap.integral_apply hiv w]
    rfl
  have his (i : Yau.RIdx n) : Integrable (fun y : Space n => g y *
      fderiv ℝ (fderiv ℝ (gaussianKernel t)) (x-y) (Yau.realVec i) (Yau.realVec i)) := by
    have hc : Continuous (fun y : Space n => g y *
        fderiv ℝ (fderiv ℝ (gaussianKernel t)) (x-y) (Yau.realVec i) (Yau.realVec i)) :=
      hg.mul (((hK''.comp (continuous_const.sub continuous_id)).clm_apply
        continuous_const).clm_apply continuous_const)
    exact hc.integrable_of_hasCompactSupport hcg.mul_right
  rw [(heatAverage_hasDerivAt ht hg hcg x).deriv]
  simp_rw [happ]
  rw [← integral_finsetSum Finset.univ (fun i _ => his i)]
  apply integral_congr_ae
  filter_upwards [] with y
  have heq := gaussianKernel_time_eq_laplacian ht (x-y)
  rw [(gaussianKernel_hasDerivAt ht (x-y)).deriv] at heq
  rw [← Finset.mul_sum, ← heq]
  ring

theorem gaussianKernel_joint_smooth {n : ℕ} {t : ℝ} (ht : 0 < t) (x : Space n) :
    ContDiffAt ℝ ∞ (fun p : ℝ × Space n => gaussianKernel p.1 p.2) (t,x) := by
  have hn : ContDiffAt ℝ ∞ (fun p : ℝ × Space n => ‖p.2‖^2) (t,x) :=
    contDiffAt_snd.norm_sq ℝ
  unfold gaussianKernel
  fun_prop (disch := positivity)
theorem heatAverage_joint_smooth {n : ℕ} {g : Space n → ℝ}
    (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Space n => heatAverage p.1 g p.2)
      (Set.Ioi 0 ×ˢ Set.univ) := by
  let G : (ℝ × Space n) → Space n → ℝ := fun p y =>
    gaussianKernel p.1 (p.2+y)*g (-y)
  have hgs : ContDiffOn ℝ ∞ (Function.uncurry G)
      ((Set.Ioi 0 ×ˢ Set.univ) ×ˢ Set.univ) := by
    intro q hq
    have hk := gaussianKernel_joint_smooth hq.1.1 (q.1.2+q.2)
    have hm : ContDiffAt ℝ ∞ (fun q : (ℝ × Space n) × Space n =>
        (q.1.1,q.1.2+q.2)) q := by fun_prop
    have hgneg : ContDiffAt ℝ ∞ (fun q : (ℝ × Space n) × Space n => g (-q.2)) q :=
      hg.contDiffAt.comp q (by fun_prop)
    exact ((hk.comp q hm).mul hgneg).contDiffWithinAt
  have hcneg : HasCompactSupport (fun y : Space n => g (-y)) :=
    hcg.comp_homeomorph (Homeomorph.neg (Space n))
  have hz : ∀ p y, p ∈ (Set.Ioi 0 ×ˢ Set.univ) →
      y ∉ tsupport (fun y : Space n => g (-y)) → G p y = 0 := by
    intro p y _ hy
    dsimp [G]
    rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]
  have hh := contDiffOn_convolution_right_with_param_comp
    (ContinuousLinearMap.lsmul ℝ ℝ) (v := fun _ : ℝ × Space n => (0 : Space n))
    contDiffOn_const (isOpen_Ioi.prod isOpen_univ) hcneg hz
    (locallyIntegrable_const (μ := volume) (1 : ℝ)) hgs
  convert hh using 1
  funext p
  rw [heatAverage, convolution_eq_swap]
  dsimp [convolution, G]
  simp only [one_mul, sub_eq_add_neg, zero_add, neg_neg]

/-- The actual Euclidean spatial Laplacian used by the Cauchy parametrix. -/
def heatLaplacian {n : ℕ} (g : Space n → ℝ) (x : Space n) : ℝ :=
  ∑ i : Yau.RIdx n, fderiv ℝ (fderiv ℝ g) x (Yau.realVec i) (Yau.realVec i)

theorem heatLaplacian_smooth {n : ℕ} {g : Space n → ℝ}
    (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (heatLaplacian g) := by
  have hH : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ g)) :=
    (hg.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)
  exact ContDiff.sum (fun i _ => (hH.clm_apply contDiff_const).clm_apply contDiff_const)

set_option maxHeartbeats 800000 in
theorem heatLaplacian_compactSupport {n : ℕ} {g : Space n → ℝ}
    (hcg : HasCompactSupport g) : HasCompactSupport (heatLaplacian g) := by
  have hH : HasCompactSupport (fderiv ℝ (fderiv ℝ g)) :=
    (hcg.fderiv ℝ).fderiv ℝ
  have hi (i : Yau.RIdx n) : HasCompactSupport
      (fun x => fderiv ℝ (fderiv ℝ g) x (Yau.realVec i) (Yau.realVec i)) :=
    (hH.comp_left (g := fun A : Space n →L[ℝ] Space n →L[ℝ] ℝ =>
      A (Yau.realVec i) (Yau.realVec i)) (by simp))
  convert (HasCompactSupport.finset_sum (s := Finset.univ) (fun i _ => hi i)) using 1
  funext x
  simp only [heatLaplacian, Finset.sum_apply]

set_option maxHeartbeats 800000 in
theorem heatAverage_laplacian {n : ℕ} {t : ℝ} {g : Space n → ℝ}
    (ht : 0 < t) (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) (x : Space n) :
    heatAverage t (heatLaplacian g) x = heatLaplacian (heatAverage t g) x := by
  have hH : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ g)) :=
    (hg.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)
  have hHc : HasCompactSupport (fderiv ℝ (fderiv ℝ g)) :=
    (hcg.fderiv ℝ).fderiv ℝ
  have hi (i : Yau.RIdx n) : Integrable (fun y : Space n =>
      gaussianKernel t y * fderiv ℝ (fderiv ℝ g) (x-y)
        (Yau.realVec i) (Yau.realVec i)) := by
    have hc : Continuous (fun y : Space n => fderiv ℝ (fderiv ℝ g) y
        (Yau.realVec i) (Yau.realVec i)) :=
      ((hH.continuous.clm_apply continuous_const).clm_apply continuous_const)
    have hs : HasCompactSupport (fun y : Space n => fderiv ℝ (fderiv ℝ g) y
        (Yau.realVec i) (Yau.realVec i)) :=
      hHc.comp_left (g := fun A : Space n →L[ℝ] Space n →L[ℝ] ℝ =>
        A (Yau.realVec i) (Yau.realVec i)) (by simp)
    obtain ⟨B,hB⟩ := hc.bounded_above_of_compact_support hs
    apply heatAverage_integrable_of_bounded ht hc
    intro y
    simpa only [Real.norm_eq_abs] using hB y
  simp only [heatAverage_def, heatLaplacian, Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i hi
  exact (heatAverage_secondFDeriv_apply ht hg hcg x (Yau.realVec i) (Yau.realVec i)).symm

theorem heatAverage_hasDerivAt_laplacian {n : ℕ} {t : ℝ} {g : Space n → ℝ}
    (ht : 0 < t) (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) (x : Space n) :
    HasDerivAt (fun s : ℝ => heatAverage s g x)
      (heatAverage t (heatLaplacian g) x) t := by
  convert heatAverage_hasDerivAt ht hg.continuous hcg x using 1
  rw [← (heatAverage_hasDerivAt ht hg.continuous hcg x).deriv,
    heatAverage_time_eq_laplacian ht hg.continuous hcg x,
    heatAverage_laplacian ht hg hcg x]
  rfl

/-- The Gaussian evolution includes its actual initial value. Its right
 derivative at zero is proved below; no extension derivative is prescribed. -/
def heatEvolution {n : ℕ} (g : Space n → ℝ) (t : ℝ) (x : Space n) : ℝ :=
  if 0 < t then heatAverage t g x else g x

theorem heatEvolution_zero {n : ℕ} (g : Space n → ℝ) (x : Space n) :
    heatEvolution g 0 x = g x := by simp [heatEvolution]

theorem heatEvolution_hasDerivAt {n : ℕ} {t : ℝ} {g : Space n → ℝ}
    (ht : 0 < t) (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) (x : Space n) :
    HasDerivAt (fun s : ℝ => heatEvolution g s x)
      (heatAverage t (heatLaplacian g) x) t := by
  apply (heatAverage_hasDerivAt_laplacian ht hg hcg x).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
  simp only [heatEvolution, if_pos (show 0 < s from hs)]

theorem heatEvolution_hasDerivWithinAt_zero {n : ℕ} {g : Space n → ℝ}
    (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) (x : Space n) :
    HasDerivWithinAt (fun t : ℝ => heatEvolution g t x)
      (heatLaplacian g x) (Set.Ici 0) 0 := by
  have hlim : Tendsto (fun t : ℝ => heatEvolution g t x)
      (𝓝[>] 0) (𝓝 (g x)) := by
    apply (heatAverage_initial_limit
      (hg.continuous.integrable_of_hasCompactSupport hcg) hg.continuous.continuousAt).congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [heatEvolution, if_pos (show 0 < t from ht)]
  apply hasDerivWithinAt_Ici_of_tendsto_deriv
    (s := Set.Ioi 0)
    (fun t ht => (heatEvolution_hasDerivAt ht hg hcg x).differentiableAt.differentiableWithinAt)
    (by simpa only [ContinuousWithinAt, heatEvolution_zero] using hlim)
    self_mem_nhdsWithin
  have hΔ := heatLaplacian_smooth hg
  have hcΔ := heatLaplacian_compactSupport hcg
  apply (heatAverage_initial_limit
    (hΔ.continuous.integrable_of_hasCompactSupport hcΔ) hΔ.continuous.continuousAt).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (heatEvolution_hasDerivAt ht hg hcg x).deriv.symm

theorem heatEvolution_hasDerivWithinAt {n : ℕ} {t : ℝ} {g : Space n → ℝ}
    (ht : 0 ≤ t) (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) (x : Space n) :
    HasDerivWithinAt (fun s : ℝ => heatEvolution g s x)
      (heatEvolution (heatLaplacian g) t x) (Set.Ici 0) t := by
  rcases ht.eq_or_lt with ht | ht
  · subst t
    simpa only [heatEvolution_zero] using heatEvolution_hasDerivWithinAt_zero hg hcg x
  · simpa only [heatEvolution, if_pos ht] using
      (heatEvolution_hasDerivAt ht hg hcg x).hasDerivWithinAt

theorem heatEvolution_derivWithin {n : ℕ} {t : ℝ} {g : Space n → ℝ}
    (ht : 0 ≤ t) (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) (x : Space n) :
    derivWithin (fun s : ℝ => heatEvolution g s x) (Set.Ici 0) t =
      heatEvolution (heatLaplacian g) t x :=
  (heatEvolution_hasDerivWithinAt ht hg hcg x).derivWithin (uniqueDiffOn_Ici 0 t ht)

/-- Every temporal derivative of the actual Gaussian evolution extends
 continuously to the initial face, by iterating the spatial generator. -/
theorem heatEvolution_time_smooth {n : ℕ} {g : Space n → ℝ}
    (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) (x : Space n) :
    ContDiffOn ℝ ∞ (fun t : ℝ => heatEvolution g t x) (Set.Ici 0) := by
  apply contDiffOn_infty.mpr
  intro k
  induction k generalizing g with
  | zero =>
    apply contDiffOn_zero.mpr
    intro t ht
    exact (heatEvolution_hasDerivWithinAt ht hg hcg x).continuousWithinAt
  | succ k ih =>
    rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Ici 0)]
    refine ⟨fun t ht => (heatEvolution_hasDerivWithinAt ht hg hcg x).differentiableWithinAt,
      by simp, ?_⟩
    apply (ih (heatLaplacian_smooth hg) (heatLaplacian_compactSupport hcg)).congr
    intro t ht
    exact heatEvolution_derivWithin ht hg hcg x

/-- The generator identity integrated from the genuine initial value.
 This is the nonsingular Duhamel identity at the initial time. -/
theorem heatEvolution_integral_laplacian {n : ℕ} {t : ℝ} {g : Space n → ℝ}
    (ht : 0 ≤ t) (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) (x : Space n) :
    (∫ s in (0 : ℝ)..t, heatEvolution (heatLaplacian g) s x) =
      heatEvolution g t x - g x := by
  have hc : ContinuousOn (fun s : ℝ => heatEvolution g s x) (Set.Icc 0 t) :=
    (heatEvolution_time_smooth hg hcg x).continuousOn.mono Set.Icc_subset_Ici_self
  have hcΔ : ContinuousOn (fun s : ℝ => heatEvolution (heatLaplacian g) s x)
      (Set.Icc 0 t) :=
    (heatEvolution_time_smooth (heatLaplacian_smooth hg)
      (heatLaplacian_compactSupport hcg) x).continuousOn.mono Set.Icc_subset_Ici_self
  have hi : IntervalIntegrable (fun s : ℝ => heatEvolution (heatLaplacian g) s x)
      volume 0 t := hcΔ.intervalIntegrable_of_Icc ht
  have hh := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht hc
    (f' := fun s : ℝ => heatEvolution (heatLaplacian g) s x)
    (fun s hs => by
      simpa only [heatEvolution, if_pos hs.1] using
        (heatEvolution_hasDerivAt hs.1 hg hcg x).hasDerivWithinAt)
    hi
  simpa only [heatEvolution_zero] using hh

theorem gaussianKernel_fderiv_integrable {n : ℕ} {t : ℝ} (ht : 0 < t) :
    Integrable (fderiv ℝ (gaussianKernel (n := n) t)) := by
  have hc := (gaussianKernel_spatial_smooth (n := n) t).continuous_fderiv (by simp)
  apply (integrable_norm_iff hc.aestronglyMeasurable).mp
  convert (gaussianKernel_weight_integrable (n := n) (s := 1) (by norm_num) ht).div_const
    (2*t) using 1
  funext y
  rw [gaussianKernel_fderiv_norm ht y, Real.rpow_one]
  ring

/-- Cancellation of the actual first derivative, as a Bochner integral
 in the space of real continuous linear maps. -/
theorem gaussianKernel_fderiv_integral_zero {n : ℕ} {t : ℝ} (ht : 0 < t) :
    (∫ y : Space n, fderiv ℝ (gaussianKernel t) y) = 0 := by
  have hodd (y : Space n) : fderiv ℝ (gaussianKernel t) (-y) =
      -fderiv ℝ (gaussianKernel t) y := by
    ext v
    simp only [gaussianKernel_fderiv_apply ht, gaussianKernel, norm_neg, inner_neg_left,
      ContinuousLinearMap.neg_apply]
    ring
  have hh := integral_neg_eq_self (fderiv ℝ (gaussianKernel (n := n) t)) volume
  simp_rw [hodd, integral_neg] at hh
  have htwo : (2 : ℝ) • (∫ y : Space n, fderiv ℝ (gaussianKernel t) y) = 0 := by
    rw [two_smul]
    exact add_eq_zero_iff_eq_neg.mpr hh.symm
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- One integrable Gaussian dominates every unit spatial translate.
 This estimate supplies a genuine dominating function for cancellation. -/
theorem gaussianKernel_shift_le {n : ℕ} {t : ℝ} (ht : 0 < t)
    (y z : Space n) (hz : ‖z‖ ≤ 1) :
    gaussianKernel t (y+z) ≤
      ((2 : ℝ)^n * Real.exp (1/(4*t))) * gaussianKernel (2*t) y := by
  have htri : ‖y‖ ≤ ‖y+z‖+1 := by
    calc
      ‖y‖ = ‖(y+z)-z‖ := by congr 1; abel
      _ ≤ ‖y+z‖+‖z‖ := norm_sub_le _ _
      _ ≤ ‖y+z‖+1 := add_le_add le_rfl hz
  have hsq : ‖y‖^2 ≤ 2*‖y+z‖^2+2 := by
    have hh := mul_self_le_mul_self (norm_nonneg y) htri
    nlinarith [sq_nonneg (‖y+z‖-1)]
  have hexp : -‖y+z‖^2/(4*t) ≤ 1/(4*t) + -‖y‖^2/(4*(2*t)) := by
    have heq : 1/(4*t) + -‖y‖^2/(4*(2*t)) = (1-‖y‖^2/2)/(4*t) := by
      field_simp
      <;> ring
    rw [heq]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [hsq]
  have hpref : ((4*Real.pi*t)^n)⁻¹ = (2 : ℝ)^n * ((4*Real.pi*(2*t))^n)⁻¹ := by
    rw [show 4*Real.pi*(2*t) = 2*(4*Real.pi*t) by ring, mul_pow, mul_inv_rev]
    have htwo : (2 : ℝ)^n ≠ 0 := by positivity
    field_simp
    simp only [mul_pow]
    ring
  calc
    gaussianKernel t (y+z) ≤ ((4*Real.pi*t)^n)⁻¹ *
        Real.exp (1/(4*t) + -‖y‖^2/(4*(2*t))) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)
    _ = _ := by rw [Real.exp_add, hpref]; unfold gaussianKernel; ring

theorem gaussianKernel_secondFDeriv_shift_domination {n : ℕ} {t : ℝ} (ht : 0 < t) :
    ∃ B : Space n → ℝ, Integrable B ∧ ∀ y z : Space n, ‖z‖ ≤ 1 →
      ‖fderiv ℝ (fderiv ℝ (gaussianKernel t)) (y+z)‖ ≤ B y := by
  let C : ℝ := (2 : ℝ)^n * Real.exp (1/(4*t))
  let B : Space n → ℝ := fun y => C * gaussianKernel (2*t) y *
    ((‖y‖^2+1)/(2*t^2)+1/(2*t))
  have ht2 : 0 < 2*t := by positivity
  have h2 : Integrable (fun y : Space n => ‖y‖^2 * gaussianKernel (2*t) y) := by
    simpa only [Real.rpow_two] using
      gaussianKernel_weight_integrable (n := n) (s := 2) (by norm_num) ht2
  have h0 := gaussianKernel_integrable (n := n) ht2
  have hB : Integrable B := by
    convert ((((h2.add h0).div_const (2*t^2)).add (h0.div_const (2*t))).const_mul C) using 1
    funext y
    dsimp [B]
    ring
  refine ⟨B, hB, ?_⟩
  intro y z hz
  have htri : ‖y+z‖ ≤ ‖y‖+1 := (norm_add_le y z).trans (add_le_add le_rfl hz)
  have hsq : ‖y+z‖^2 ≤ 2*‖y‖^2+2 := by
    have hh := mul_self_le_mul_self (norm_nonneg (y+z)) htri
    nlinarith [sq_nonneg (‖y‖-1)]
  have hpoly : ‖y+z‖^2/(4*t^2) ≤ (‖y‖^2+1)/(2*t^2) := by
    calc
      _ ≤ (2*‖y‖^2+2)/(4*t^2) := div_le_div_of_nonneg_right hsq (by positivity)
      _ = _ := by field_simp; ring
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    _ ≤ gaussianKernel t (y+z) * (‖y+z‖^2/(4*t^2)+1/(2*t)) :=
      gaussianKernel_secondFDeriv_norm_le ht (y+z)
    _ ≤ (C*gaussianKernel (2*t) y) * ((‖y‖^2+1)/(2*t^2)+1/(2*t)) :=
      mul_le_mul (gaussianKernel_shift_le ht y z hz) (add_le_add hpoly le_rfl)
        (by positivity) (mul_nonneg hC (gaussianKernel_pos ht2 y).le)
    _ = B y := rfl

/-- The Hessian kernel has zero Bochner integral. Translation invariance
 makes the integrated gradient identically zero; Gaussian domination
 justifies differentiating that identity on the whole spatial space. -/
theorem gaussianKernel_secondFDeriv_integral_zero {n : ℕ} {t : ℝ} (ht : 0 < t) :
    (∫ y : Space n, fderiv ℝ (fderiv ℝ (gaussianKernel t)) y) = 0 := by
  have hs := (gaussianKernel_spatial_smooth (n := n) t).fderiv_right (m := ∞) (by simp)
  have hHc := hs.continuous_fderiv (by simp)
  obtain ⟨B,hB,hbound⟩ := gaussianKernel_secondFDeriv_shift_domination (n := n) ht
  have hF (z : Space n) : Continuous (fun y => fderiv ℝ (gaussianKernel t) (y+z)) :=
    hs.continuous.comp (continuous_id.add continuous_const)
  have hd (y z : Space n) : HasFDerivAt
      (fun w : Space n => fderiv ℝ (gaussianKernel t) (y+w))
      (fderiv ℝ (fderiv ℝ (gaussianKernel t)) (y+z)) z := by
    simpa using! (hs.differentiable (by simp) (y+z)).hasFDerivAt.comp z
      ((hasFDerivAt_const y z).add (hasFDerivAt_id z))
  have hh := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun z y : Space n => fderiv ℝ (gaussianKernel t) (y+z))
    (F' := fun z y : Space n => fderiv ℝ (fderiv ℝ (gaussianKernel t)) (y+z))
    (s := Metric.ball (0 : Space n) 1) (bound := B)
    (Metric.ball_mem_nhds (0 : Space n) (by norm_num))
    (Eventually.of_forall fun z => (hF z).aestronglyMeasurable)
    (by simpa only [add_zero] using gaussianKernel_fderiv_integrable (n := n) ht)
    (by simpa only [add_zero] using hHc.aestronglyMeasurable)
    (ae_of_all _ fun y z hz => hbound y z (by
      have hz' : ‖z‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
      exact hz'.le))
    hB (ae_of_all _ fun y z _ => hd y z)
  have heq : (fun z : Space n => ∫ y : Space n, fderiv ℝ (gaussianKernel t) (y+z)) =
      fun _ => 0 := by
    funext z
    rw [integral_add_right_eq_self]
    exact gaussianKernel_fderiv_integral_zero ht
  rw [heq] at hh
  simpa only [add_zero, fderiv_const_apply] using hh.fderiv.symm

theorem gaussianKernel_fderiv_shift_domination {n : ℕ} {t : ℝ} (ht : 0 < t) :
    ∃ B : Space n → ℝ, Integrable B ∧ ∀ y z : Space n, ‖z‖ ≤ 1 →
      ‖fderiv ℝ (gaussianKernel t) (y+z)‖ ≤ B y := by
  let C : ℝ := (2 : ℝ)^n * Real.exp (1/(4*t))
  let B : Space n → ℝ := fun y => C * gaussianKernel (2*t) y * (‖y‖+1)/(2*t)
  have ht2 : 0 < 2*t := by positivity
  have h1 : Integrable (fun y : Space n => ‖y‖ * gaussianKernel (2*t) y) := by
    simpa only [Real.rpow_one] using
      gaussianKernel_weight_integrable (n := n) (s := 1) (by norm_num) ht2
  have h0 := gaussianKernel_integrable (n := n) ht2
  have hB : Integrable B := by
    convert (((h1.add h0).const_mul C).div_const (2*t)) using 1
    funext y
    dsimp [B]
    ring
  refine ⟨B, hB, ?_⟩
  intro y z hz
  have htri : ‖y+z‖ ≤ ‖y‖+1 := (norm_add_le y z).trans (add_le_add le_rfl hz)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  rw [gaussianKernel_fderiv_norm ht]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul (gaussianKernel_shift_le ht y z hz) htri (norm_nonneg _)
    (mul_nonneg hC (gaussianKernel_pos ht2 y).le)

/-- Spatial differentiation of the Gaussian convolution for arbitrary
 bounded continuous sources, with no compact support requirement. -/
theorem heatAverage_hasFDerivAt_kernel_of_bounded {n : ℕ} {t M : ℝ} {g : Space n → ℝ}
    (ht : 0 < t) (hg : Continuous g) (hM : ∀ y, |g y| ≤ M) (x : Space n) :
    HasFDerivAt (heatAverage t g)
      (∫ y : Space n, g y • fderiv ℝ (gaussianKernel t) (x-y)) x := by
  have hM0 : 0 ≤ M := (abs_nonneg (g 0)).trans (hM 0)
  have hs := gaussianKernel_spatial_smooth (n := n) t
  have hDc := hs.continuous_fderiv (by simp)
  obtain ⟨B,hB,hbound⟩ := gaussianKernel_fderiv_shift_domination (n := n) ht
  have hi : Integrable (fun y : Space n => g y • gaussianKernel t (x-y)) :=
    ((gaussianKernel_integrable ht).comp_sub_left x).bdd_mul hg.aestronglyMeasurable
      (ae_of_all _ fun y => by simpa only [Real.norm_eq_abs] using hM y)
  have hd (z y : Space n) : HasFDerivAt (fun w : Space n => gaussianKernel t (w-y))
      (fderiv ℝ (gaussianKernel t) (z-y)) z := by
    simpa using! (hs.differentiable (by simp) (z-y)).hasFDerivAt.comp z
      ((hasFDerivAt_id z).sub (hasFDerivAt_const y z))
  have hh := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun z y : Space n => g y • gaussianKernel t (z-y))
    (F' := fun z y : Space n => g y • fderiv ℝ (gaussianKernel t) (z-y))
    (s := Metric.ball x 1) (bound := fun y => M * B (x-y))
    (Metric.ball_mem_nhds x (by norm_num))
    (Eventually.of_forall fun z =>
      (hg.smul (hs.continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable)
    hi (hg.smul (hDc.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
    (ae_of_all _ fun y z hz => ?_)
    ((hB.comp_sub_left x).const_mul M)
    (ae_of_all _ fun y z _ => (hd z y).const_smul (g y))
  · have heq : (fun z : Space n => ∫ y : Space n, g y • gaussianKernel t (z-y)) =
        heatAverage t g := by
      funext z
      rw [heatAverage, convolution_eq_swap]
      simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, mul_comm]
    rw [heq] at hh
    exact hh
  · have hz' : ‖z-x‖ ≤ 1 := by
      have hz0 : ‖z-x‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hz
      exact hz0.le
    have heq : z-y = (x-y)+(z-x) := by abel
    rw [norm_smul, Real.norm_eq_abs, heq]
    exact mul_le_mul (hM y) (hbound (x-y) (z-x) hz') (norm_nonneg _) hM0

theorem heatAverage_secondFDeriv_kernel_of_bounded {n : ℕ} {t M : ℝ} {g : Space n → ℝ}
    (ht : 0 < t) (hg : Continuous g) (hM : ∀ y, |g y| ≤ M) (x : Space n) :
    fderiv ℝ (fderiv ℝ (heatAverage t g)) x =
      ∫ y : Space n, g y • fderiv ℝ (fderiv ℝ (gaussianKernel t)) (x-y) := by
  have hM0 : 0 ≤ M := (abs_nonneg (g 0)).trans (hM 0)
  have hs := (gaussianKernel_spatial_smooth (n := n) t).fderiv_right (m := ∞) (by simp)
  have hHc := hs.continuous_fderiv (by simp)
  obtain ⟨B,hB,hbound⟩ := gaussianKernel_secondFDeriv_shift_domination (n := n) ht
  have hi := ((gaussianKernel_fderiv_integrable ht).comp_sub_left x).bdd_smul M
    hg.aestronglyMeasurable (ae_of_all _ fun y => by
      simpa only [Real.norm_eq_abs] using hM y)
  have hd (z y : Space n) : HasFDerivAt
      (fun w : Space n => fderiv ℝ (gaussianKernel t) (w-y))
      (fderiv ℝ (fderiv ℝ (gaussianKernel t)) (z-y)) z := by
    simpa using! (hs.differentiable (by simp) (z-y)).hasFDerivAt.comp z
      ((hasFDerivAt_id z).sub (hasFDerivAt_const y z))
  have hh := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun z y : Space n => g y • fderiv ℝ (gaussianKernel t) (z-y))
    (F' := fun z y : Space n => g y • fderiv ℝ (fderiv ℝ (gaussianKernel t)) (z-y))
    (s := Metric.ball x 1) (bound := fun y => M * B (x-y))
    (Metric.ball_mem_nhds x (by norm_num))
    (Eventually.of_forall fun z =>
      (hg.smul (hs.continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable)
    hi (hg.smul (hHc.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
    (ae_of_all _ fun y z hz => ?_)
    ((hB.comp_sub_left x).const_mul M)
    (ae_of_all _ fun y z _ => (hd z y).const_smul (g y))
  · have heq : (fun z : Space n => ∫ y : Space n,
        g y • fderiv ℝ (gaussianKernel t) (z-y)) = fderiv ℝ (heatAverage t g) := by
      funext z
      exact (heatAverage_hasFDerivAt_kernel_of_bounded ht hg hM z).fderiv.symm
    rw [heq] at hh
    exact hh.fderiv
  · have hz' : ‖z-x‖ ≤ 1 := by
      have hz0 : ‖z-x‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hz
      exact hz0.le
    have heq : z-y = (x-y)+(z-x) := by abel
    rw [norm_smul, Real.norm_eq_abs, heq]
    exact mul_le_mul (hM y) (hbound (x-y) (z-x) hz') (norm_nonneg _) hM0

/-- The cancellation algebra is performed in an arbitrary real normed
 codomain, so it applies to the genuine Hessian-valued kernel. -/
theorem integral_smul_sub_const_of_zero_integral {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Space n → E}
    (hKc : Continuous K) (hKi : Integrable (fun y => ‖K y‖))
    (hK0 : (∫ y : Space n, K y) = 0) {g : Space n → ℝ} {M : ℝ}
    (hg : Continuous g) (hM : ∀ y, |g y| ≤ M) (c : ℝ) :
    (∫ y : Space n, g y • K y) = ∫ y : Space n, (g y-c) • K y := by
  have hiK : Integrable K := (integrable_norm_iff hKc.aestronglyMeasurable).mp hKi
  have hi : Integrable (fun y : Space n => g y • K y) := by
    convert hiK.bdd_smul M hg.aestronglyMeasurable
      (ae_of_all _ fun y => by simpa only [Real.norm_eq_abs] using hM y) using 1
  have hic : Integrable (fun y : Space n => c • K y) := by
    convert hiK.smul c using 1
  calc
    _ = (∫ y : Space n, g y • K y) - c • (∫ y : Space n, K y) := by
      rw [hK0, smul_zero, sub_zero]
    _ = ∫ y : Space n, g y • K y - c • K y := by
      rw [integral_sub hi hic, integral_smul]
    _ = _ := by congr 1; funext y; exact (sub_smul (g y) c (K y)).symm

/-- The Hessian of the convolution uses the spatial source difference,
 including bounded sources with no spatial compact support. -/
theorem heatAverage_secondFDeriv_cancelled {n : ℕ} {t M : ℝ} {g : Space n → ℝ}
    (ht : 0 < t) (hg : Continuous g) (hM : ∀ y, |g y| ≤ M) (x : Space n) :
    fderiv ℝ (fderiv ℝ (heatAverage t g)) x =
      ∫ y : Space n, (g (x-y)-g x) • fderiv ℝ (fderiv ℝ (gaussianKernel t)) y := by
  rw [heatAverage_secondFDeriv_kernel_of_bounded ht hg hM x]
  have hsub := integral_sub_left_eq_self
    (fun y : Space n => g y • fderiv ℝ (fderiv ℝ (gaussianKernel t)) (x-y)) x
    (μ := volume)
  simp only [sub_sub_cancel] at hsub
  rw [← hsub]
  have hs := (gaussianKernel_spatial_smooth (n := n) t).fderiv_right (m := ∞) (by simp)
  apply integral_smul_sub_const_of_zero_integral (hs.continuous_fderiv (by simp))
    (by simpa only [Real.rpow_zero, mul_one] using
      (gaussianKernel_secondFDeriv_weight_integrable_bound (n := n) (s := 0)
        (by norm_num) ht).1)
    (gaussianKernel_secondFDeriv_integral_zero ht)
    (hg.comp (continuous_const.sub continuous_id))
    (fun y => hM (x-y)) (g x)

/-- The integrable-in-time Hessian estimate needed for the zero-initial
 Cauchy operator. The constant precedes the source and its bounds. -/
theorem heatAverage_secondFDeriv_holder_bound {n : ℕ} {α : ℝ} (hα : 0 ≤ α) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ∀ (g : Space n → ℝ) (M H : ℝ),
      Continuous g → (∀ y, |g y| ≤ M) → 0 ≤ H →
      (∀ x y, |g x-g y| ≤ H * ‖x-y‖^α) → ∀ x : Space n,
        ‖fderiv ℝ (fderiv ℝ (heatAverage t g)) x‖ ≤ C*H*t^(α/2-1) := by
  obtain ⟨C,hC,hbound⟩ := gaussianKernel_secondFDeriv_weight_bound (n := n) hα
  refine ⟨C,hC,?_⟩
  intro t ht g M H hg hM hH0 hH x
  rw [heatAverage_secondFDeriv_cancelled ht hg hM x]
  have hi := hbound t ht
  calc
    _ ≤ ∫ y : Space n, H *
        (‖fderiv ℝ (fderiv ℝ (gaussianKernel t)) y‖ * ‖y‖^α) := by
      apply norm_integral_le_of_norm_le (hi.1.const_mul H)
      filter_upwards [] with y
      have hh := hH (x-y) x
      have heq : (x-y)-x = -y := by abel
      rw [heq, norm_neg] at hh
      calc
        _ ≤ ‖g (x-y)-g x‖ * ‖fderiv ℝ (fderiv ℝ (gaussianKernel t)) y‖ :=
          ContinuousLinearMap.opNorm_smul_le _ _
        _ = |g (x-y)-g x| * ‖fderiv ℝ (fderiv ℝ (gaussianKernel t)) y‖ := by
          rw [Real.norm_eq_abs]
        _ ≤ (H*‖y‖^α) * ‖fderiv ℝ (fderiv ℝ (gaussianKernel t)) y‖ :=
          mul_le_mul_of_nonneg_right hh
            (fderiv ℝ (fderiv ℝ (gaussianKernel t)) y).opNorm_nonneg
        _ = _ := by ring
    _ = H * (∫ y : Space n,
        ‖fderiv ℝ (fderiv ℝ (gaussianKernel t)) y‖ * ‖y‖^α) := integral_const_mul _ _
    _ ≤ H * (C*t^(α/2-1)) := mul_le_mul_of_nonneg_left hi.2 hH0
    _ = C*H*t^(α/2-1) := by ring

set_option backward.isDefEq.respectTransparency.types false in
theorem gaussianKernel_thirdFDeriv_apply {n : ℕ} {t : ℝ}
    (ht : 0 < t) (x u v w : Space n) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ (gaussianKernel t))) x u v w =
      gaussianKernel t x *
        ((-inner ℝ x u/(2*t)) *
          (inner ℝ x v * inner ℝ x w/(4*t^2) - inner ℝ v w/(2*t)) +
          (inner ℝ u v * inner ℝ x w + inner ℝ x v * inner ℝ u w)/(4*t^2)) := by
  have hH : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ (gaussianKernel t))) x :=
    (((gaussianKernel_spatial_smooth t).fderiv_right (m := ∞) (by simp)).fderiv_right
      (m := ∞) (by simp)).differentiable (by simp) x
  have hHv : DifferentiableAt ℝ
      (fun y : Space n => fderiv ℝ (fderiv ℝ (gaussianKernel t)) y v) x :=
    hH.clm_apply (differentiableAt_const v)
  have hleft : fderiv ℝ
      (fun y : Space n => fderiv ℝ (fderiv ℝ (gaussianKernel t)) y v w) x u =
      fderiv ℝ (fderiv ℝ (fderiv ℝ (gaussianKernel t))) x u v w := by
    rw [fderiv_clm_apply hHv (differentiableAt_const w),
      fderiv_clm_apply hH (differentiableAt_const v)]
    simp
  have hv : HasFDerivAt (fun y : Space n => inner ℝ y v) (innerSLFlip ℝ v) x :=
    (innerSLFlip ℝ v).hasFDerivAt
  have hw : HasFDerivAt (fun y : Space n => inner ℝ y w) (innerSLFlip ℝ w) x :=
    (innerSLFlip ℝ w).hasFDerivAt
  have hP := ((hv.fun_mul hw).const_mul ((4*t^2)⁻¹)).sub_const (inner ℝ v w/(2*t))
  have hd := (gaussianKernel_hasFDerivAt ht x).fun_mul hP
  have heq : (fun y : Space n => fderiv ℝ (fderiv ℝ (gaussianKernel t)) y v w) =
      (fun y => gaussianKernel t y *
        ((4*t^2)⁻¹ * (inner ℝ y v * inner ℝ y w) - inner ℝ v w/(2*t))) := by
    funext y
    rw [gaussianKernel_secondFDeriv_apply ht]
    ring
  rw [← hleft, heq, hd.fderiv]
  simp +instances only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, innerSL_apply_apply]
  have hwu : ((innerSLFlip ℝ) w) u = inner ℝ u w := innerSLFlip_apply_apply ℝ w u
  have hvu : ((innerSLFlip ℝ) v) u = inner ℝ u v := innerSLFlip_apply_apply ℝ v u
  rw [hwu, hvu]
  ring

local instance {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) :=
  inferInstance
local instance {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

set_option backward.isDefEq.respectTransparency.types false in
theorem gaussianKernel_thirdFDeriv_norm_le {n : ℕ} {t : ℝ}
    (ht : 0 < t) (x : Space n) :
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (gaussianKernel t))) x‖ ≤
      gaussianKernel t x * (‖x‖^3/(8*t^3) + 3*‖x‖/(4*t^2)) := by
  let C : ℝ := gaussianKernel t x * (‖x‖^3/(8*t^3) + 3*‖x‖/(4*t^2))
  have hK : 0 < gaussianKernel t x := gaussianKernel_pos ht x
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply (fderiv ℝ (fderiv ℝ (fderiv ℝ (gaussianKernel t))) x).opNorm_le_bound hC
  intro u
  apply (fderiv ℝ (fderiv ℝ (fderiv ℝ (gaussianKernel t))) x u).opNorm_le_bound
    (mul_nonneg hC (norm_nonneg u))
  intro v
  apply (fderiv ℝ (fderiv ℝ (fderiv ℝ (gaussianKernel t))) x u v).opNorm_le_bound
    (mul_nonneg (mul_nonneg hC (norm_nonneg u)) (norm_nonneg v))
  intro w
  rw [Real.norm_eq_abs, gaussianKernel_thirdFDeriv_apply ht,
    abs_mul, abs_of_pos hK]
  have hA : |inner ℝ x v * inner ℝ x w/(4*t^2)| ≤
      ‖x‖^2/(4*t^2) * ‖v‖ * ‖w‖ := by
    rw [abs_div, abs_mul, abs_of_pos (show 0 < 4*t^2 by positivity)]
    have hprod := mul_le_mul (abs_real_inner_le_norm x v) (abs_real_inner_le_norm x w)
      (abs_nonneg (inner ℝ x w)) (mul_nonneg (norm_nonneg x) (norm_nonneg v))
    have hh := div_le_div_of_nonneg_right hprod (show 0 ≤ 4*t^2 by positivity)
    simpa only [div_eq_mul_inv, pow_two, mul_assoc, mul_comm, mul_left_comm] using hh
  have hB : |inner ℝ v w/(2*t)| ≤ (1/(2*t)) * ‖v‖ * ‖w‖ := by
    rw [abs_div, abs_of_pos (show 0 < 2*t by positivity)]
    have hh := div_le_div_of_nonneg_right (abs_real_inner_le_norm v w)
      (show 0 ≤ 2*t by positivity)
    simpa only [div_eq_mul_inv, one_mul, mul_assoc, mul_comm, mul_left_comm] using hh
  have hP : |inner ℝ x v * inner ℝ x w/(4*t^2) - inner ℝ v w/(2*t)| ≤
      (‖x‖^2/(4*t^2)+1/(2*t))*‖v‖*‖w‖ := by
    convert (abs_sub _ _).trans (add_le_add hA hB) using 1
    ring
  have hfirst : |-inner ℝ x u/(2*t)| ≤ (‖x‖/(2*t))*‖u‖ := by
    rw [abs_div, abs_neg, abs_of_pos (show 0 < 2*t by positivity)]
    have hh := div_le_div_of_nonneg_right (abs_real_inner_le_norm x u)
      (show 0 ≤ 2*t by positivity)
    simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hh
  have hQ : |(inner ℝ u v * inner ℝ x w + inner ℝ x v * inner ℝ u w)/(4*t^2)| ≤
      (2*‖x‖/(4*t^2))*‖u‖*‖v‖*‖w‖ := by
    rw [abs_div, abs_of_pos (show 0 < 4*t^2 by positivity)]
    have hprod1 := mul_le_mul (abs_real_inner_le_norm u v) (abs_real_inner_le_norm x w)
      (abs_nonneg (inner ℝ x w)) (mul_nonneg (norm_nonneg u) (norm_nonneg v))
    have hprod2 := mul_le_mul (abs_real_inner_le_norm x v) (abs_real_inner_le_norm u w)
      (abs_nonneg (inner ℝ u w)) (mul_nonneg (norm_nonneg x) (norm_nonneg v))
    have hh := div_le_div_of_nonneg_right
      ((abs_add_le (inner ℝ u v * inner ℝ x w)
        (inner ℝ x v * inner ℝ u w)).trans (add_le_add
        (by simpa only [abs_mul] using hprod1) (by simpa only [abs_mul] using hprod2)))
      (show 0 ≤ 4*t^2 by positivity)
    convert hh using 1 <;> ring
  have hT := mul_le_mul hfirst hP
    (abs_nonneg (inner ℝ x v * inner ℝ x w/(4*t^2) - inner ℝ v w/(2*t)))
    (mul_nonneg (div_nonneg (norm_nonneg x) (by positivity)) (norm_nonneg u))
  rw [← abs_mul] at hT
  have hsum := (abs_add_le _ _).trans (add_le_add hT hQ)
  have hh := mul_le_mul_of_nonneg_left hsum hK.le
  convert hh using 1
  dsimp [C]
  field_simp
  ring


/-- The third spatial derivative has the precise weighted time power
 needed on the far portion of the spatial Hölder integral. -/
theorem gaussianKernel_thirdFDeriv_weight_bound {n : ℕ} {s : ℝ} (hs : 0 ≤ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t →
      Integrable (fun x : Space n =>
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (gaussianKernel t))) x‖ * ‖x‖^s) ∧
      (∫ x : Space n,
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (gaussianKernel t))) x‖ * ‖x‖^s) ≤
          C*t^(s/2-3/2) := by
  obtain ⟨C3,hC3,hM3⟩ := gaussianKernel_weight_integral_bound (n := n)
    (s := s+3) (by linarith)
  obtain ⟨C1,hC1,hM1⟩ := gaussianKernel_weight_integral_bound (n := n)
    (s := s+1) (by linarith)
  refine ⟨C3+C1, by positivity, ?_⟩
  intro t ht
  let g3 : Space n → ℝ := fun x => (1/(8*t^3)) * (‖x‖^(s+3)*gaussianKernel t x)
  let g1 : Space n → ℝ := fun x => (3/(4*t^2)) * (‖x‖^(s+1)*gaussianKernel t x)
  have hi3 : Integrable g3 := (hM3 t ht).1.const_mul _
  have hi1 : Integrable g1 := (hM1 t ht).1.const_mul _
  have hp3 (x : Space n) : ‖x‖^(s+3) = ‖x‖^s*‖x‖^3 := by
    rw [Real.rpow_add_of_nonneg (norm_nonneg x) hs (by norm_num)]
    norm_num
  have hp1 (x : Space n) : ‖x‖^(s+1) = ‖x‖^s*‖x‖ := by
    rw [Real.rpow_add_of_nonneg (norm_nonneg x) hs (by norm_num), Real.rpow_one]
  have hpoint (x : Space n) :
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (gaussianKernel t))) x‖ * ‖x‖^s ≤ g3 x + g1 x := by
    have hh := mul_le_mul_of_nonneg_right (gaussianKernel_thirdFDeriv_norm_le ht x)
      (Real.rpow_nonneg (norm_nonneg x) s)
    convert hh using 1
    dsimp [g3,g1]
    rw [hp3,hp1]
    ring
  have h3s : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ (fderiv ℝ (gaussianKernel (n := n) t)))) :=
    (((gaussianKernel_spatial_smooth t).fderiv_right (m := ∞) (by simp)).fderiv_right
      (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)
  have hnormMap : Continuous (fun A : Space n →L[ℝ] Space n →L[ℝ] Space n →L[ℝ] ℝ => ‖A‖) :=
    continuous_norm (E := Space n →L[ℝ] Space n →L[ℝ] Space n →L[ℝ] ℝ)
  have hc : Continuous (fun x : Space n =>
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (gaussianKernel t))) x‖ * ‖x‖^s) :=
    (hnormMap.comp h3s.continuous).mul ((Real.continuous_rpow_const hs).comp continuous_norm)
  have hi : Integrable (fun x : Space n =>
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (gaussianKernel t))) x‖ * ‖x‖^s) := by
    apply (hi3.add hi1).mono' hc.aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (mul_nonneg
      (fderiv ℝ (fderiv ℝ (fderiv ℝ (gaussianKernel t))) x).opNorm_nonneg
      (Real.rpow_nonneg (norm_nonneg x) s))]
    exact hpoint x
  refine ⟨hi, ?_⟩
  have htp3 : t^((s+3)/2) = t^(s/2-3/2)*t^3 := by
    rw [show (s+3)/2 = (s/2-3/2)+3 by ring, Real.rpow_add ht]
    norm_num
  have htp1 : t^((s+1)/2) = t^(s/2-3/2)*t^2 := by
    rw [show (s+1)/2 = (s/2-3/2)+2 by ring, Real.rpow_add ht]
    norm_num
  calc
    _ ≤ ∫ x : Space n, g3 x + g1 x :=
      integral_mono_ae hi (hi3.add hi1) (ae_of_all _ hpoint)
    _ = (1/(8*t^3)) * (∫ x : Space n, ‖x‖^(s+3)*gaussianKernel t x) +
        (3/(4*t^2)) * (∫ x : Space n, ‖x‖^(s+1)*gaussianKernel t x) := by
      rw [integral_add hi3 hi1]
      simp only [g3,g1,integral_const_mul]
    _ ≤ (1/(8*t^3)) * (C3*t^((s+3)/2)) + (3/(4*t^2)) * (C1*t^((s+1)/2)) :=
      add_le_add (mul_le_mul_of_nonneg_left (hM3 t ht).2 (by positivity))
        (mul_le_mul_of_nonneg_left (hM1 t ht).2 (by positivity))
    _ = (C3/8+3*C1/4)*t^(s/2-3/2) := by
      rw [htp3,htp1]
      field_simp
    _ ≤ (C3+C1)*t^(s/2-3/2) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ht.le _)
      linarith

theorem schauder_time_weight_integrable {α : ℝ} (hα : 0 < α) (t : ℝ) :
    IntervalIntegrable (fun s : ℝ => (t-s)^(α/2-1)) volume 0 t := by
  have hi : IntervalIntegrable (fun s : ℝ => s^(α/2-1)) volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  simpa only [sub_zero, sub_self] using (hi.comp_sub_left t).symm

theorem schauder_time_weight_integral {α : ℝ} (hα : 0 < α) (t : ℝ) :
    (∫ s in (0 : ℝ)..t, (t-s)^(α/2-1)) = (2/α)*t^(α/2) := by
  rw [intervalIntegral.integral_comp_sub_left (fun r : ℝ => r^(α/2-1)) t]
  simp only [sub_self, sub_zero]
  rw [integral_rpow (Or.inl (by linarith : -1 < α/2-1)),
    show α/2-1+1 = α/2 by ring, Real.zero_rpow (by linarith : α/2 ≠ 0), sub_zero]
  field_simp

def realInnerBilinear {n : ℕ} : Space n →L[ℝ] Space n →L[ℝ] ℝ :=
  (innerSL ℝ (E := Space n) : Space n →L[ℝ] Space n →L[ℝ] ℝ).restrictScalars ℝ

theorem realInnerBilinear_apply {n : ℕ} (v w : Space n) :
    realInnerBilinear v w = inner ℝ v w := rfl

theorem gaussianKernel_secondFDeriv_hasDerivAt {n : ℕ} {t : ℝ}
    (ht : 0 < t) (x : Space n) :
    HasDerivAt (fun s : ℝ => fderiv ℝ (fderiv ℝ (gaussianKernel s)) x)
      ((gaussianKernel t x * (‖x‖^2/(4*t^2)-(n:ℝ)/t)) •
        ((1/(4*t^2)) • (innerSL ℝ x).smulRight (innerSL ℝ x) -
          (1/(2*t)) • (realInnerBilinear (n := n))) +
        gaussianKernel t x •
          ((-1/(2*t^3)) • (innerSL ℝ x).smulRight (innerSL ℝ x) +
            (1/(2*t^2)) • (realInnerBilinear (n := n)))) t := by
  let A : Space n →L[ℝ] Space n →L[ℝ] ℝ := (innerSL ℝ x).smulRight (innerSL ℝ x)
  let J : Space n →L[ℝ] Space n →L[ℝ] ℝ := realInnerBilinear
  change HasDerivAt (fun s : ℝ => fderiv ℝ (fderiv ℝ (gaussianKernel s)) x)
    ((gaussianKernel t x * (‖x‖^2/(4*t^2)-(n:ℝ)/t)) •
      ((1/(4*t^2)) • A - (1/(2*t)) • J) +
      gaussianKernel t x • ((-1/(2*t^3)) • A + (1/(2*t^2)) • J)) t
  have h4 : HasDerivAt (fun s : ℝ => 1/(4*s^2)) (-1/(2*t^3)) t := by
    convert ((((hasDerivAt_id t).pow 2).const_mul 4).inv
      (by positivity : 4*t^2 ≠ 0)) using 1 <;> simp [one_div] <;> field_simp <;> ring
    funext r
    simp [Pi.inv_apply, mul_inv_rev, inv_pow]
    <;> ring
  have h2 : HasDerivAt (fun s : ℝ => 1/(2*s)) (-1/(2*t^2)) t := by
    convert (((hasDerivAt_id t).const_mul 2).inv
      (by positivity : 2*t ≠ 0)) using 1 <;> simp [one_div] <;> field_simp <;> ring
    funext r
    simp [Pi.inv_apply, mul_inv_rev, inv_pow]
    <;> ring
  have hP := (h4.smul_const A).fun_sub (h2.smul_const J)
  have hwhole := (gaussianKernel_hasDerivAt ht x).fun_smul hP
  have hh : HasDerivAt (fun s : ℝ => fderiv ℝ (fderiv ℝ (gaussianKernel s)) x)
      (gaussianKernel t x • ((-1/(2*t^3)) • A - (-1/(2*t^2)) • J) +
        (gaussianKernel t x * (‖x‖^2/(4*t^2)-(n:ℝ)/t)) •
          ((1/(4*t^2)) • A - (1/(2*t)) • J)) t := by
    apply hwhole.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    ext v w
    rw [gaussianKernel_secondFDeriv_apply (show 0 < s from hs)]
    simp only [A,J,ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, realInnerBilinear_apply, smul_eq_mul]
    have hvw : ((innerSL ℝ) v) w = inner ℝ v w := innerSL_apply_apply ℝ v w
    try rw [hvw]
    ring
  apply hh.congr_deriv
  ext v w
  simp only [A,J,ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, realInnerBilinear_apply, smul_eq_mul]
  have hvw : ((innerSL ℝ) v) w = inner ℝ v w := innerSL_apply_apply ℝ v w
  try rw [hvw]
  ring

theorem gaussianKernel_secondFDeriv_time_norm_le {n : ℕ} {t : ℝ}
    (ht : 0 < t) (x : Space n) :
    ‖deriv (fun s : ℝ => fderiv ℝ (fderiv ℝ (gaussianKernel s)) x) t‖ ≤
      gaussianKernel t x * (‖x‖^4/(16*t^4) +
        (2*(n:ℝ)+5)*‖x‖^2/(8*t^3) + ((n:ℝ)+1)/(2*t^2)) := by
  let A : Space n →L[ℝ] Space n →L[ℝ] ℝ := (innerSL ℝ x).smulRight (innerSL ℝ x)
  let J : Space n →L[ℝ] Space n →L[ℝ] ℝ := realInnerBilinear
  let P : Space n →L[ℝ] Space n →L[ℝ] ℝ := (1/(4*t^2)) • A - (1/(2*t)) • J
  let V : Space n →L[ℝ] Space n →L[ℝ] ℝ := (-1/(2*t^3)) • A + (1/(2*t^2)) • J
  let d : ℝ := ‖x‖^2/(4*t^2)-(n:ℝ)/t
  have hK : 0 < gaussianKernel t x := gaussianKernel_pos ht x
  have hA : ‖A‖ = ‖x‖^2 := by
    dsimp [A]
    rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
    ring
  have hJ : ‖J‖ ≤ 1 := by
    simpa only [J,realInnerBilinear,ContinuousLinearMap.norm_restrictScalars] using
      (norm_innerSL_le ℝ (E := Space n))
  have hP : ‖P‖ ≤ ‖x‖^2/(4*t^2)+1/(2*t) := by
    calc
      _ ≤ ‖(1/(4*t^2)) • A‖ + ‖(1/(2*t)) • J‖ := norm_sub_le _ _
      _ = (1/(4*t^2))*‖A‖ + (1/(2*t))*‖J‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos (by positivity : 0 < 1/(4*t^2)),
          abs_of_pos (by positivity : 0 < 1/(2*t))]
      _ ≤ _ := by
        rw [hA]
        have hh := add_le_add (le_rfl : (1/(4*t^2))*‖x‖^2 ≤ (1/(4*t^2))*‖x‖^2)
          (mul_le_mul_of_nonneg_left hJ (by positivity : 0 ≤ 1/(2*t)))
        convert hh using 1 <;> ring
  have hV : ‖V‖ ≤ ‖x‖^2/(2*t^3)+1/(2*t^2) := by
    calc
      _ ≤ ‖(-1/(2*t^3)) • A‖ + ‖(1/(2*t^2)) • J‖ := norm_add_le _ _
      _ = (1/(2*t^3))*‖A‖ + (1/(2*t^2))*‖J‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_div, abs_neg, abs_one, abs_of_pos (by positivity : 0 < 2*t^3),
          abs_of_pos (by positivity : 0 < 1/(2*t^2))]
      _ ≤ _ := by
        rw [hA]
        have hh := add_le_add (le_rfl : (1/(2*t^3))*‖x‖^2 ≤ (1/(2*t^3))*‖x‖^2)
          (mul_le_mul_of_nonneg_left hJ (by positivity : 0 ≤ 1/(2*t^2)))
        convert hh using 1 <;> ring
  have hd : |d| ≤ ‖x‖^2/(4*t^2)+(n:ℝ)/t := by
    dsimp [d]
    convert abs_sub (‖x‖^2/(4*t^2)) ((n:ℝ)/t) using 1
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  rw [(gaussianKernel_secondFDeriv_hasDerivAt ht x).deriv]
  change ‖(gaussianKernel t x*d) • P + gaussianKernel t x • V‖ ≤ _
  calc
    _ ≤ ‖(gaussianKernel t x*d) • P‖ + ‖gaussianKernel t x • V‖ := norm_add_le _ _
    _ = gaussianKernel t x * |d| * ‖P‖ + gaussianKernel t x * ‖V‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_mul, abs_of_pos hK]
    _ ≤ gaussianKernel t x * (‖x‖^2/(4*t^2)+(n:ℝ)/t) *
        (‖x‖^2/(4*t^2)+1/(2*t)) +
        gaussianKernel t x * (‖x‖^2/(2*t^3)+1/(2*t^2)) :=
      add_le_add
        (mul_le_mul (mul_le_mul_of_nonneg_left hd hK.le) hP P.opNorm_nonneg (by positivity))
        (mul_le_mul_of_nonneg_left hV hK.le)
    _ = _ := by field_simp; ring

theorem gaussianKernel_secondFDeriv_time_continuous {n : ℕ} {t : ℝ} (ht : 0 < t) :
    Continuous (fun x : Space n =>
      deriv (fun s : ℝ => fderiv ℝ (fderiv ℝ (gaussianKernel s)) x) t) := by
  let A : Space n → Space n →L[ℝ] Space n →L[ℝ] ℝ :=
    fun x => (innerSL ℝ x).smulRight (innerSL ℝ x)
  have hAc : Continuous A := by
    have hh := (((ContinuousLinearMap.smulRightL ℝ (Space n) (Space n →L[ℝ] ℝ)).continuous.comp
      (innerSL ℝ).continuous).clm_apply (innerSL ℝ).continuous)
    convert hh using 1
    funext x
    ext v w
    simp [A, ContinuousLinearMap.smulRightL_apply_apply]
  have heq : (fun x : Space n =>
      deriv (fun s : ℝ => fderiv ℝ (fderiv ℝ (gaussianKernel s)) x) t) =
      fun x => (gaussianKernel t x * (‖x‖^2/(4*t^2)-(n:ℝ)/t)) •
        ((1/(4*t^2)) • A x - (1/(2*t)) •
          (realInnerBilinear (n := n))) +
        gaussianKernel t x • ((-1/(2*t^3)) • A x +
          (1/(2*t^2)) • (realInnerBilinear (n := n))) := by
    funext x
    exact (gaussianKernel_secondFDeriv_hasDerivAt ht x).deriv
  rw [heq]
  have hK := (gaussianKernel_spatial_smooth (n := n) t).continuous
  fun_prop

theorem gaussianKernel_secondFDeriv_time_weight_bound {n : ℕ} {s : ℝ} (hs : 0 ≤ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t →
      Integrable (fun x : Space n =>
        ‖deriv (fun r : ℝ => fderiv ℝ (fderiv ℝ (gaussianKernel r)) x) t‖ * ‖x‖^s) ∧
      (∫ x : Space n,
        ‖deriv (fun r : ℝ => fderiv ℝ (fderiv ℝ (gaussianKernel r)) x) t‖ * ‖x‖^s) ≤
          C*t^(s/2-2) := by
  obtain ⟨C4,hC4,hM4⟩ := gaussianKernel_weight_integral_bound (n := n)
    (s := s+4) (by linarith)
  obtain ⟨C2,hC2,hM2⟩ := gaussianKernel_weight_integral_bound (n := n)
    (s := s+2) (by linarith)
  obtain ⟨C0,hC0,hM0⟩ := gaussianKernel_weight_integral_bound (n := n) hs
  let C : ℝ := C4 + ((n:ℝ)+3)*C2 + ((n:ℝ)+1)*C0
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro t ht
  let g4 : Space n → ℝ := fun x => (1/(16*t^4)) * (‖x‖^(s+4)*gaussianKernel t x)
  let g2 : Space n → ℝ := fun x => ((2*(n:ℝ)+5)/(8*t^3)) * (‖x‖^(s+2)*gaussianKernel t x)
  let g0 : Space n → ℝ := fun x => (((n:ℝ)+1)/(2*t^2)) * (‖x‖^s*gaussianKernel t x)
  have hi4 : Integrable g4 := (hM4 t ht).1.const_mul _
  have hi2 : Integrable g2 := (hM2 t ht).1.const_mul _
  have hi0 : Integrable g0 := (hM0 t ht).1.const_mul _
  have hp4 (x : Space n) : ‖x‖^(s+4) = ‖x‖^s*‖x‖^4 := by
    rw [Real.rpow_add_of_nonneg (norm_nonneg x) hs (by norm_num)]
    norm_num
  have hp2 (x : Space n) : ‖x‖^(s+2) = ‖x‖^s*‖x‖^2 := by
    rw [Real.rpow_add_of_nonneg (norm_nonneg x) hs (by norm_num), Real.rpow_two]
  have hpoint (x : Space n) :
      ‖deriv (fun r : ℝ => fderiv ℝ (fderiv ℝ (gaussianKernel r)) x) t‖ * ‖x‖^s ≤
        g4 x + g2 x + g0 x := by
    have hh := mul_le_mul_of_nonneg_right (gaussianKernel_secondFDeriv_time_norm_le ht x)
      (Real.rpow_nonneg (norm_nonneg x) s)
    convert hh using 1
    dsimp [g4,g2,g0]
    rw [hp4,hp2]
    ring
  have hnormMap : Continuous (fun A : Space n →L[ℝ] Space n →L[ℝ] ℝ => ‖A‖) :=
    continuous_norm (E := Space n →L[ℝ] Space n →L[ℝ] ℝ)
  have hc : Continuous (fun x : Space n =>
      ‖deriv (fun r : ℝ => fderiv ℝ (fderiv ℝ (gaussianKernel r)) x) t‖ * ‖x‖^s) :=
    (hnormMap.comp (gaussianKernel_secondFDeriv_time_continuous ht)).mul
      ((Real.continuous_rpow_const hs).comp continuous_norm)
  have hi : Integrable (fun x : Space n =>
      ‖deriv (fun r : ℝ => fderiv ℝ (fderiv ℝ (gaussianKernel r)) x) t‖ * ‖x‖^s) := by
    apply ((hi4.add hi2).add hi0).mono' hc.aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (mul_nonneg
      (deriv (fun r : ℝ => fderiv ℝ (fderiv ℝ (gaussianKernel r)) x) t).opNorm_nonneg
      (Real.rpow_nonneg (norm_nonneg x) s))]
    exact hpoint x
  refine ⟨hi, ?_⟩
  have htp4 : t^((s+4)/2) = t^(s/2-2)*t^4 := by
    rw [show (s+4)/2 = (s/2-2)+4 by ring, Real.rpow_add ht]
    norm_num
  have htp2 : t^((s+2)/2) = t^(s/2-2)*t^3 := by
    rw [show (s+2)/2 = (s/2-2)+3 by ring, Real.rpow_add ht]
    norm_num
  have htp0 : t^(s/2) = t^(s/2-2)*t^2 := by
    rw [show s/2 = (s/2-2)+2 by ring, Real.rpow_add ht]
    norm_num
  calc
    _ ≤ ∫ x : Space n, g4 x + g2 x + g0 x :=
      integral_mono_ae hi ((hi4.add hi2).add hi0) (ae_of_all _ hpoint)
    _ = (1/(16*t^4)) * (∫ x : Space n, ‖x‖^(s+4)*gaussianKernel t x) +
        ((2*(n:ℝ)+5)/(8*t^3)) * (∫ x : Space n, ‖x‖^(s+2)*gaussianKernel t x) +
        (((n:ℝ)+1)/(2*t^2)) * (∫ x : Space n, ‖x‖^s*gaussianKernel t x) := by
      have hisum : Integrable (fun x : Space n => g4 x+g2 x) := by
        convert hi4.add hi2 using 1
      rw [integral_add hisum hi0, integral_add hi4 hi2]
      simp only [g4,g2,g0,integral_const_mul]
    _ ≤ (1/(16*t^4)) * (C4*t^((s+4)/2)) +
        ((2*(n:ℝ)+5)/(8*t^3)) * (C2*t^((s+2)/2)) +
        (((n:ℝ)+1)/(2*t^2)) * (C0*t^(s/2)) := by
      apply add_le_add
      · exact add_le_add (mul_le_mul_of_nonneg_left (hM4 t ht).2 (by positivity))
          (mul_le_mul_of_nonneg_left (hM2 t ht).2 (by positivity))
      · exact mul_le_mul_of_nonneg_left (hM0 t ht).2 (by positivity)
    _ = (C4/16+((2*(n:ℝ)+5)/8)*C2+(((n:ℝ)+1)/2)*C0)*t^(s/2-2) := by
      rw [htp4,htp2,htp0]
      field_simp
    _ ≤ C*t^(s/2-2) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ht.le _)
      have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
      have h2 := mul_le_mul_of_nonneg_right
        (by linarith : (2*(n:ℝ)+5)/8 ≤ (n:ℝ)+3) hC2.le
      have h0 := mul_le_mul_of_nonneg_right
        (by linarith : ((n:ℝ)+1)/2 ≤ (n:ℝ)+1) hC0.le
      dsimp [C]
      linarith


theorem gaussianKernel_thirdFDeriv_shift_weight_bound {n : ℕ} {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ∀ z : Space n, ‖z‖ ≤ Real.sqrt t →
      Integrable (fun y : Space n =>
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (gaussianKernel t))) (y+z)‖ * ‖y‖^α) ∧
      (∫ y : Space n,
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (gaussianKernel t))) (y+z)‖ * ‖y‖^α) ≤
          C*t^(α/2-3/2) := by
  obtain ⟨Cα,hCα,hboundα⟩ := gaussianKernel_thirdFDeriv_weight_bound (n := n) hα
  obtain ⟨C0,hC0,hbound0⟩ := gaussianKernel_thirdFDeriv_weight_bound (n := n)
    (s := 0) (by norm_num)
  refine ⟨Cα+C0, by positivity, ?_⟩
  intro t ht z hz
  have hiα := (hboundα t ht).1.comp_add_right z
  have hi0 : Integrable (fun y : Space n =>
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (gaussianKernel t))) (y+z)‖) := by
    simpa only [Real.rpow_zero,mul_one] using (hbound0 t ht).1.comp_add_right z
  have hpow (y : Space n) : ‖y‖^α ≤ ‖y+z‖^α+‖z‖^α := by
    have htri : ‖y‖ ≤ ‖y+z‖+‖z‖ := by
      calc
        ‖y‖ = ‖(y+z)-z‖ := by congr 1; abel
        _ ≤ ‖y+z‖+‖z‖ := norm_sub_le _ _
    exact (Real.rpow_le_rpow (norm_nonneg y) htri hα).trans
      (Real.rpow_add_le_add_rpow (norm_nonneg (y+z)) (norm_nonneg z) hα hα1)
  have hpoint (y : Space n) :
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (gaussianKernel t))) (y+z)‖ * ‖y‖^α ≤
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (gaussianKernel t))) (y+z)‖ * ‖y+z‖^α +
          ‖z‖^α * ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (gaussianKernel t))) (y+z)‖ := by
    convert mul_le_mul_of_nonneg_left (hpow y)
      (fderiv ℝ (fderiv ℝ (fderiv ℝ (gaussianKernel t))) (y+z)).opNorm_nonneg using 1
    ring
  have h3s := (((gaussianKernel_spatial_smooth (n := n) t).fderiv_right (m := ∞)
    (by simp)).fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)
  have hn : Continuous (fun A : Space n →L[ℝ] Space n →L[ℝ] Space n →L[ℝ] ℝ => ‖A‖) :=
    continuous_norm (E := Space n →L[ℝ] Space n →L[ℝ] Space n →L[ℝ] ℝ)
  have hc : Continuous (fun y : Space n =>
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (gaussianKernel t))) (y+z)‖ * ‖y‖^α) :=
    ((hn.comp h3s.continuous).comp (continuous_id.add continuous_const)).mul
      ((Real.continuous_rpow_const hα).comp continuous_norm)
  have hi : Integrable (fun y : Space n =>
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (gaussianKernel t))) (y+z)‖ * ‖y‖^α) := by
    apply (hiα.add (hi0.const_mul (‖z‖^α))).mono' hc.aestronglyMeasurable
    filter_upwards [] with y
    rw [Real.norm_of_nonneg (mul_nonneg
      (fderiv ℝ (fderiv ℝ (fderiv ℝ (gaussianKernel t))) (y+z)).opNorm_nonneg
      (Real.rpow_nonneg (norm_nonneg y) α))]
    exact hpoint y
  refine ⟨hi,?_⟩
  have hzpow : ‖z‖^α ≤ t^(α/2) := by
    apply (Real.rpow_le_rpow (norm_nonneg z) hz hα).trans_eq
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le]
    congr 1
    ring
  have h0 : (∫ y : Space n,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (gaussianKernel t))) y‖) ≤ C0*t^(-(3/2:ℝ)) := by
    simpa only [Real.rpow_zero,mul_one,zero_div,zero_sub] using (hbound0 t ht).2
  calc
    _ ≤ ∫ y : Space n,
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (gaussianKernel t))) (y+z)‖ * ‖y+z‖^α +
          ‖z‖^α * ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (gaussianKernel t))) (y+z)‖ :=
      integral_mono_ae hi (hiα.add (hi0.const_mul (‖z‖^α))) (ae_of_all _ hpoint)
    _ = (∫ y : Space n,
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (gaussianKernel t))) y‖ * ‖y‖^α) +
          ‖z‖^α * ∫ y : Space n,
            ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (gaussianKernel t))) y‖ := by
      rw [integral_add hiα (hi0.const_mul (‖z‖^α)), integral_const_mul]
      rw [integral_add_right_eq_self
        (fun y : Space n => ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (gaussianKernel t))) y‖ * ‖y‖^α) z,
        integral_add_right_eq_self
          (fun y : Space n => ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (gaussianKernel t))) y‖) z]
    _ ≤ Cα*t^(α/2-3/2) + ‖z‖^α*(C0*t^(-(3/2:ℝ))) :=
      add_le_add (hboundα t ht).2
        (mul_le_mul_of_nonneg_left h0 (Real.rpow_nonneg (norm_nonneg z) α))
    _ ≤ Cα*t^(α/2-3/2) + t^(α/2)*(C0*t^(-(3/2:ℝ))) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hzpow (by positivity))
    _ = (Cα+C0)*t^(α/2-3/2) := by
      rw [show α/2-3/2 = α/2+(-(3/2:ℝ)) by ring, Real.rpow_add ht]
      ring

theorem gaussianKernel_secondFDeriv_spatial_increment_le {n : ℕ}
    (t : ℝ) (y h : Space n) :
    ‖fderiv ℝ (fderiv ℝ (gaussianKernel t)) (y+h) -
      fderiv ℝ (fderiv ℝ (gaussianKernel t)) y‖ ≤
      ‖h‖ * ∫ r in (0 : ℝ)..1,
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (gaussianKernel t))) (y+r • h)‖ := by
  have hH : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ (gaussianKernel (n := n) t))) :=
    ((gaussianKernel_spatial_smooth t).fderiv_right (m := ∞) (by simp)).fderiv_right
      (m := ∞) (by simp)
  have hD3 := hH.fderiv_right (m := ∞) (by simp)
  have hn : Continuous (fun A : Space n →L[ℝ] Space n →L[ℝ] Space n →L[ℝ] ℝ => ‖A‖) :=
    continuous_norm (E := Space n →L[ℝ] Space n →L[ℝ] Space n →L[ℝ] ℝ)
  have hl : Continuous (fun r : ℝ => y+r • h) := by fun_prop
  have hLinec : Continuous (fun r : ℝ =>
      fderiv ℝ (fderiv ℝ (gaussianKernel t)) (y+r • h)) := hH.continuous.comp hl
  have hLined (r : ℝ) : HasDerivAt
      (fun s : ℝ => fderiv ℝ (fderiv ℝ (gaussianKernel t)) (y+s • h))
      (fderiv ℝ (fderiv ℝ (fderiv ℝ (gaussianKernel t))) (y+r • h) h) r := by
    simpa using! (hH.differentiable (by simp) (y+r • h)).hasFDerivAt.comp_hasDerivAt r
      ((hasDerivAt_const r y).add ((hasDerivAt_id r).smul_const h))
  have hBd (r : ℝ) :
      ‖deriv (fun s : ℝ => fderiv ℝ (fderiv ℝ (gaussianKernel t)) (y+s • h)) r‖ ≤
        ‖h‖ * ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (gaussianKernel t))) (y+r • h)‖ := by
    rw [(hLined r).deriv]
    simpa only [mul_comm] using
      (fderiv ℝ (fderiv ℝ (fderiv ℝ (gaussianKernel t))) (y+r • h)).le_opNorm h
  have hBc : Continuous (fun r : ℝ =>
      ‖h‖ * ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (gaussianKernel t))) (y+r • h)‖) :=
    continuous_const.mul ((hn.comp hD3.continuous).comp hl)
  have hb := norm_sub_le_integral_of_norm_deriv_le_of_le
    (f := fun r : ℝ => fderiv ℝ (fderiv ℝ (gaussianKernel t)) (y+r • h))
    (B := fun r : ℝ =>
      ‖h‖ * ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (gaussianKernel t))) (y+r • h)‖)
    (by norm_num : (0 : ℝ) ≤ 1) hLinec.continuousOn
    (fun r _ => (hLined r).differentiableAt.differentiableWithinAt)
    (ae_of_all _ fun r _ => hBd r) (hBc.intervalIntegrable 0 1)
  simpa only [one_smul,zero_smul,add_zero,intervalIntegral.integral_const_mul] using hb

theorem gaussianKernel_secondFDeriv_shift_weight_bound {n : ℕ} {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ∀ h : Space n, ‖h‖ ≤ Real.sqrt t →
      Integrable (fun y : Space n =>
        ‖fderiv ℝ (fderiv ℝ (gaussianKernel t)) (y+h) -
          fderiv ℝ (fderiv ℝ (gaussianKernel t)) y‖ * ‖y‖^α) ∧
      (∫ y : Space n,
        ‖fderiv ℝ (fderiv ℝ (gaussianKernel t)) (y+h) -
          fderiv ℝ (fderiv ℝ (gaussianKernel t)) y‖ * ‖y‖^α) ≤
          C*‖h‖*t^(α/2-3/2) := by
  obtain ⟨C,hC,hshift⟩ := gaussianKernel_thirdFDeriv_shift_weight_bound (n := n) hα hα1
  refine ⟨C,hC,?_⟩
  intro t ht h hh
  let ν : Measure ℝ := volume.restrict (Set.Ioc 0 1)
  letI : IsFiniteMeasure ν := ⟨by simp [ν,Real.volume_Ioc]⟩
  let F : ℝ → Space n → ℝ := fun r y =>
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (gaussianKernel t))) (y+r • h)‖ * ‖y‖^α
  have hFpos (r : ℝ) (y : Space n) : 0 ≤ F r y := mul_nonneg
    (fderiv ℝ (fderiv ℝ (fderiv ℝ (gaussianKernel t))) (y+r • h)).opNorm_nonneg
    (Real.rpow_nonneg (norm_nonneg y) α)
  have hscaled (r : ℝ) (hr : r ∈ Set.Ioc 0 1) : ‖r • h‖ ≤ Real.sqrt t := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr.1]
    have hm : r*‖h‖ ≤ ‖h‖ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hr.2 (norm_nonneg h)
    exact hm.trans hh
  have hFI (r : ℝ) (hr : r ∈ Set.Ioc 0 1) : Integrable (F r) :=
    (hshift t ht (r • h) (hscaled r hr)).1
  have hFB (r : ℝ) (hr : r ∈ Set.Ioc 0 1) :
      (∫ y : Space n, F r y) ≤ C*t^(α/2-3/2) :=
    (hshift t ht (r • h) (hscaled r hr)).2
  have hH := ((gaussianKernel_spatial_smooth (n := n) t).fderiv_right (m := ∞)
    (by simp)).fderiv_right (m := ∞) (by simp)
  have hD3 := hH.fderiv_right (m := ∞) (by simp)
  have hn3 : Continuous (fun A : Space n →L[ℝ] Space n →L[ℝ] Space n →L[ℝ] ℝ => ‖A‖) :=
    continuous_norm (E := Space n →L[ℝ] Space n →L[ℝ] Space n →L[ℝ] ℝ)
  have hFc : Continuous (Function.uncurry F) :=
    (((hn3.comp hD3.continuous).comp
      (continuous_snd.add (continuous_fst.smul continuous_const))).mul
      (((Real.continuous_rpow_const hα).comp continuous_norm).comp continuous_snd))
  have hFm : AEStronglyMeasurable (Function.uncurry F) (ν.prod volume) :=
    hFc.aestronglyMeasurable
  have hFnI : Integrable (fun r : ℝ => ∫ y : Space n, ‖F r y‖) ν := by
    apply (integrable_const (C*t^(α/2-3/2))).mono' hFm.norm.integral_prod_right'
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have heq : (fun y : Space n => ‖F r y‖) = F r := by
      funext y
      exact Real.norm_of_nonneg (hFpos r y)
    change ‖∫ y : Space n, ‖F r y‖‖ ≤ C*t^(α/2-3/2)
    rw [heq,Real.norm_of_nonneg (integral_nonneg (hFpos r))]
    exact hFB r hr
  have hprod : Integrable (Function.uncurry F) (ν.prod volume) := by
    apply (integrable_prod_iff hFm).mpr
    refine ⟨?_,hFnI⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact hFI r hr
  have hQi := hprod.integral_prod_right.const_mul ‖h‖
  have hpoint (y : Space n) :
      ‖fderiv ℝ (fderiv ℝ (gaussianKernel t)) (y+h) -
        fderiv ℝ (fderiv ℝ (gaussianKernel t)) y‖ * ‖y‖^α ≤
          ‖h‖ * ∫ r, F r y ∂ν := by
    have hb := mul_le_mul_of_nonneg_right
      (gaussianKernel_secondFDeriv_spatial_increment_le t y h)
      (Real.rpow_nonneg (norm_nonneg y) α)
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hb
    convert hb using 1
    dsimp [ν,F]
    rw [integral_mul_const]
    ring
  have hn2 : Continuous (fun A : Space n →L[ℝ] Space n →L[ℝ] ℝ => ‖A‖) :=
    continuous_norm (E := Space n →L[ℝ] Space n →L[ℝ] ℝ)
  have hc : Continuous (fun y : Space n =>
      ‖fderiv ℝ (fderiv ℝ (gaussianKernel t)) (y+h) -
        fderiv ℝ (fderiv ℝ (gaussianKernel t)) y‖ * ‖y‖^α) :=
    (hn2.comp ((hH.continuous.comp (continuous_id.add continuous_const)).sub hH.continuous)).mul
      ((Real.continuous_rpow_const hα).comp continuous_norm)
  have hi : Integrable (fun y : Space n =>
      ‖fderiv ℝ (fderiv ℝ (gaussianKernel t)) (y+h) -
        fderiv ℝ (fderiv ℝ (gaussianKernel t)) y‖ * ‖y‖^α) := by
    apply hQi.mono' hc.aestronglyMeasurable
    filter_upwards [] with y
    rw [Real.norm_of_nonneg (mul_nonneg
      (fderiv ℝ (fderiv ℝ (gaussianKernel t)) (y+h) -
        fderiv ℝ (fderiv ℝ (gaussianKernel t)) y).opNorm_nonneg
      (Real.rpow_nonneg (norm_nonneg y) α))]
    exact hpoint y
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ y : Space n, ‖h‖ * ∫ r, F r y ∂ν :=
      integral_mono_ae hi hQi (ae_of_all _ hpoint)
    _ = ‖h‖ * ∫ y : Space n, ∫ r, F r y ∂ν := integral_const_mul _ _
    _ = ‖h‖ * ∫ r, (∫ y : Space n, F r y) ∂ν := by
      congr 1
      exact (integral_integral_swap hprod).symm
    _ ≤ ‖h‖ * ∫ _r, C*t^(α/2-3/2) ∂ν := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg h)
      apply integral_mono_ae hprod.integral_prod_left (integrable_const _)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact hFB r hr
    _ = C*‖h‖*t^(α/2-3/2) := by
      simp only [integral_const]
      simp [ν,Measure.real,Real.volume_Ioc] <;> ring


theorem holderBound_continuousOn {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    {α C : ℝ} {Q : Set (Point n)} {f : Point n → V}
    (hα : 0 < α) (hf : HolderBound α Q f C) : ContinuousOn f Q := by
  intro p hp
  rw [ContinuousWithinAt,tendsto_iff_norm_sub_tendsto_zero]
  have hW : Continuous (fun q : Point n => C * holderWeight α q p) := by
    unfold holderWeight
    apply continuous_const.mul
    exact (((Real.continuous_rpow_const hα.le).comp
      (continuous_norm.comp (continuous_fst.sub continuous_const))).add
      ((Real.continuous_rpow_const (by positivity : 0 ≤ α/2)).comp
        (continuous_snd.sub continuous_const).abs))
  have hlim : Tendsto (fun q : Point n => C * holderWeight α q p)
      (𝓝[Q] p) (𝓝 0) := by
    simpa [holderWeight,Real.zero_rpow hα.ne',
      Real.zero_rpow (by positivity : α/2 ≠ 0)] using
      (hW.tendsto p).mono_left nhdsWithin_le_nhds
  exact squeeze_zero' (Eventually.of_forall fun q => norm_nonneg (f q-f p))
    (by filter_upwards [self_mem_nhdsWithin] with q hq; exact hf.2.2 q hq p hp) hlim

theorem holderBound_timeClamp {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    {α C T : ℝ} {f : Point n → V} (hα : 0 ≤ α) (hT : 0 ≤ T)
    (hf : HolderBound α (cylinder Set.univ 0 T) f C) :
    HolderBound α Set.univ (fun p : Point n => f (p.1,max 0 (min p.2 T))) C := by
  have hmem (p : Point n) : (p.1,max 0 (min p.2 T)) ∈ cylinder Set.univ 0 T :=
    ⟨Set.mem_univ _, le_max_left _ _, max_le hT (min_le_right _ _)⟩
  refine ⟨hf.1,fun p _ => hf.2.1 _ (hmem p),?_⟩
  intro p _ q _
  apply (hf.2.2 _ (hmem p) _ (hmem q)).trans
  apply mul_le_mul_of_nonneg_left _ hf.1
  simp only [holderWeight]
  apply add_le_add le_rfl
  apply Real.rpow_le_rpow (abs_nonneg _) _ (div_nonneg hα (by norm_num))
  have hm : |min p.2 T-min q.2 T| ≤ |p.2-q.2| := by
    simpa using abs_min_sub_min_le_max p.2 T q.2 T
  have hx : |max 0 (min p.2 T)-max 0 (min q.2 T)| ≤ |min p.2 T-min q.2 T| := by
    simpa using abs_max_sub_max_le_max 0 (min p.2 T) 0 (min q.2 T)
  exact hx.trans hm

theorem timeClamp_eqOn {n : ℕ} {V : Type*} (T : ℝ) (f : Point n → V) :
    Set.EqOn (fun p : Point n => f (p.1,max 0 (min p.2 T))) f
      (cylinder Set.univ 0 T) := by
  intro p hp
  simp only [min_eq_left hp.2.2,max_eq_right hp.2.1,Prod.eta]

theorem gaussianKernel_joint_measurable {n : ℕ} :
    Measurable (fun p : ℝ × Space n => gaussianKernel p.1 p.2) := by
  unfold gaussianKernel
  fun_prop

def heatDuhamel {n : ℕ} (f : Point n → ℝ) (t : ℝ) (x : Space n) : ℝ :=
  ∫ s in (0 : ℝ)..t, heatAverage (t-s) (fun y => f (y,s)) x

theorem heatDuhamel_zero {n : ℕ} (f : Point n → ℝ) (x : Space n) :
    heatDuhamel f 0 x = 0 := by simp [heatDuhamel]

theorem heatDuhamel_integrable_and_bound {n : ℕ} {f : Point n → ℝ} {M t : ℝ}
    (hf : Continuous f) (hM : ∀ p, |f p| ≤ M) (ht : 0 ≤ t) (x : Space n) :
    IntervalIntegrable (fun s : ℝ => heatAverage (t-s) (fun y => f (y,s)) x) volume 0 t ∧
      |heatDuhamel f t x| ≤ t*M := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc 0 t)
  letI : IsFiniteMeasure μ := ⟨by simp [μ,Real.volume_Ioc]⟩
  have hF : Measurable (fun p : ℝ × Space n =>
      gaussianKernel (t-p.1) p.2 * f (x-p.2,p.1)) := by
    have hK : Measurable (fun p : ℝ × Space n => gaussianKernel (t-p.1) p.2) :=
      (gaussianKernel_joint_measurable (n := n)).comp
        (show Measurable (fun p : ℝ × Space n => (t-p.1,p.2)) from by fun_prop)
    have hg : Measurable (fun p : ℝ × Space n => f (x-p.2,p.1)) :=
      hf.measurable.comp (show Measurable (fun p : ℝ × Space n => (x-p.2,p.1)) from by fun_prop)
    exact hK.fun_mul hg
  have hm : AEStronglyMeasurable
      (fun s : ℝ => heatAverage (t-s) (fun y => f (y,s)) x) μ := by
    simpa only [heatAverage_def,Function.uncurry_apply_pair] using
      (hF.aestronglyMeasurable (μ := μ.prod volume)).integral_prod_right'
  have hb : ∀ᵐ s ∂μ, |heatAverage (t-s) (fun y => f (y,s)) x| ≤ M := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,μ.ae_ne t] with s hs hst
    apply heatAverage_bound (sub_pos.mpr (lt_of_le_of_ne hs.2 hst))
      (hf.comp (continuous_id.prodMk continuous_const))
    intro y
    exact hM (y,s)
  have hi : Integrable (fun s : ℝ => heatAverage (t-s) (fun y => f (y,s)) x) μ := by
    apply (integrable_const M).mono' hm
    filter_upwards [hb] with s hs
    simpa only [Real.norm_eq_abs] using hs
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mpr hi,?_⟩
  have hvol : μ.real Set.univ = t := by
    simp [μ,Measure.real,Real.volume_Ioc,ENNReal.toReal_ofReal ht]
  have hn := norm_integral_le_of_norm_le_const
    (μ := μ) (f := fun s : ℝ => heatAverage (t-s) (fun y => f (y,s)) x)
    (by filter_upwards [hb] with s hs; simpa only [Real.norm_eq_abs] using hs)
  rw [heatDuhamel,intervalIntegral.integral_of_le ht]
  change |∫ s, heatAverage (t-s) (fun y => f (y,s)) x ∂μ| ≤ t*M
  simpa only [Real.norm_eq_abs,hvol,mul_comm] using hn

theorem heatDuhamel_timeClamp {n : ℕ} {T t : ℝ} (f : Point n → ℝ)
    (ht : t ∈ Set.Icc 0 T) (x : Space n) :
    heatDuhamel (fun p => f (p.1,max 0 (min p.2 T))) t x = heatDuhamel f t x := by
  simp only [heatDuhamel,intervalIntegral.integral_of_le ht.1]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  congr 1
  funext y
  exact timeClamp_eqOn T f (show (y,s) ∈ cylinder Set.univ 0 T from
    ⟨Set.mem_univ _,hs.1.le,hs.2.trans ht.2⟩)

theorem heatDuhamel_bound_of_holder {n : ℕ} {α F T t : ℝ} {f : Point n → ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (hf : HolderBound α (cylinder Set.univ 0 T) f F)
    (ht : t ∈ Set.Icc 0 T) (x : Space n) : |heatDuhamel f t x| ≤ t*F := by
  have hhat := holderBound_timeClamp hα.le hT hf
  have hc : Continuous (fun p : Point n => f (p.1,max 0 (min p.2 T))) :=
    continuousOn_univ.mp (holderBound_continuousOn hα hhat)
  have hb (p : Point n) : |f (p.1,max 0 (min p.2 T))| ≤ F := by
    simpa only [Real.norm_eq_abs] using hhat.2.1 p (Set.mem_univ _)
  rw [← heatDuhamel_timeClamp f ht x]
  exact (heatDuhamel_integrable_and_bound hc hb ht.1 x).2


theorem heatAverage_fderiv_bound_of_bounded {n : ℕ} :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ∀ (g : Space n → ℝ) (M : ℝ),
      Continuous g → (∀ y, |g y| ≤ M) → ∀ x : Space n,
        ‖fderiv ℝ (heatAverage t g) x‖ ≤ C*M*t^(-(1/2:ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := gaussianKernel_weight_integral_bound (n := n) (s := 1) (by norm_num)
  refine ⟨C,hC,?_⟩
  intro t ht g M hg hM x
  have hM0 : 0 ≤ M := (abs_nonneg (g 0)).trans (hM 0)
  have hiD := (gaussianKernel_fderiv_integrable (n := n) ht).norm
  have hmoment : (∫ y : Space n, ‖y‖*gaussianKernel t y) ≤ C*t^(1/2:ℝ) := by
    simpa only [Real.rpow_one] using (hbound t ht).2
  have hIntD : (∫ y : Space n, ‖fderiv ℝ (gaussianKernel t) y‖) =
      (∫ y : Space n, ‖y‖*gaussianKernel t y)/(2*t) := by
    have heq : (fun y : Space n => ‖fderiv ℝ (gaussianKernel t) y‖) =
        fun y => (‖y‖*gaussianKernel t y)/(2*t) := by
      funext y
      rw [gaussianKernel_fderiv_norm ht]
      ring
    rw [heq,integral_div]
  have htp : t^(1/2:ℝ) = t^(-(1/2:ℝ))*t := by
    have hh := Real.rpow_add ht (-(1/2:ℝ)) 1
    simpa only [show -(1/2:ℝ)+1 = (1/2:ℝ) by ring,Real.rpow_one] using hh
  rw [(heatAverage_hasFDerivAt_kernel_of_bounded ht hg hM x).fderiv]
  calc
    _ ≤ ∫ y : Space n, M*‖fderiv ℝ (gaussianKernel t) (x-y)‖ := by
      apply norm_integral_le_of_norm_le ((hiD.comp_sub_left x).const_mul M)
      filter_upwards [] with y
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hM y)
        (fderiv ℝ (gaussianKernel t) (x-y)).opNorm_nonneg
    _ = M*(∫ y : Space n, ‖fderiv ℝ (gaussianKernel t) y‖) := by
      rw [integral_const_mul,integral_sub_left_eq_self
        (fun y : Space n => ‖fderiv ℝ (gaussianKernel t) y‖) volume x]
    _ ≤ M*((C*t^(1/2:ℝ))/(2*t)) := by
      rw [hIntD]
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hmoment (by positivity)) hM0
    _ = (C/2)*M*t^(-(1/2:ℝ)) := by rw [htp]; field_simp
    _ ≤ C*M*t^(-(1/2:ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ht.le _)
      exact mul_le_mul_of_nonneg_right (by linarith : C/2 ≤ C) hM0

theorem gaussianKernel_fderiv_joint_smooth {n : ℕ} {t : ℝ} (ht : 0 < t) (x : Space n) :
    ContDiffAt ℝ ∞ (fun p : ℝ × Space n => fderiv ℝ (gaussianKernel p.1) p.2) (t,x) := by
  have hF : ContDiffAt ℝ ∞ (fun q : (ℝ × Space n) × Space n =>
      gaussianKernel q.1.1 q.2) ((t,x),x) :=
    ContDiffAt.comp (𝕜 := ℝ) (n := ∞)
      (g := fun p : ℝ × Space n => gaussianKernel p.1 p.2)
      (f := fun q : (ℝ × Space n) × Space n => (q.1.1,q.2))
      ((t,x),x) (gaussianKernel_joint_smooth ht x) (by fun_prop)
  exact ContDiffAt.fderiv (f := fun p : ℝ × Space n => gaussianKernel p.1)
    (g := Prod.snd) hF contDiffAt_snd (by simp)

theorem gaussianKernel_secondFDeriv_joint_smooth {n : ℕ} {t : ℝ} (ht : 0 < t) (x : Space n) :
    ContDiffAt ℝ ∞ (fun p : ℝ × Space n => fderiv ℝ (fderiv ℝ (gaussianKernel p.1)) p.2)
      (t,x) := by
  have hF : ContDiffAt ℝ ∞ (fun q : (ℝ × Space n) × Space n =>
      fderiv ℝ (gaussianKernel q.1.1) q.2) ((t,x),x) :=
    ContDiffAt.comp (𝕜 := ℝ) (n := ∞)
      (g := fun p : ℝ × Space n => fderiv ℝ (gaussianKernel p.1) p.2)
      (f := fun q : (ℝ × Space n) × Space n => (q.1.1,q.2))
      ((t,x),x) (gaussianKernel_fderiv_joint_smooth ht x) (by fun_prop)
  exact ContDiffAt.fderiv (f := fun p : ℝ × Space n => fderiv ℝ (gaussianKernel p.1))
    (g := Prod.snd) hF contDiffAt_snd (by simp)

theorem heatAverage_fderiv_hasFDerivAt_kernel_of_bounded {n : ℕ} {t M : ℝ} {g : Space n → ℝ}
    (ht : 0 < t) (hg : Continuous g) (hM : ∀ y, |g y| ≤ M) (x : Space n) :
    HasFDerivAt (fderiv ℝ (heatAverage t g))
      (∫ y : Space n, g y • fderiv ℝ (fderiv ℝ (gaussianKernel t)) (x-y)) x := by
  have hM0 : 0 ≤ M := (abs_nonneg (g 0)).trans (hM 0)
  have hs := (gaussianKernel_spatial_smooth (n := n) t).fderiv_right (m := ∞) (by simp)
  have hHc := hs.continuous_fderiv (by simp)
  obtain ⟨B,hB,hbound⟩ := gaussianKernel_secondFDeriv_shift_domination (n := n) ht
  have hi := ((gaussianKernel_fderiv_integrable ht).comp_sub_left x).bdd_smul M
    hg.aestronglyMeasurable (ae_of_all _ fun y => by
      simpa only [Real.norm_eq_abs] using hM y)
  have hd (z y : Space n) : HasFDerivAt
      (fun w : Space n => fderiv ℝ (gaussianKernel t) (w-y))
      (fderiv ℝ (fderiv ℝ (gaussianKernel t)) (z-y)) z := by
    simpa using! (hs.differentiable (by simp) (z-y)).hasFDerivAt.comp z
      ((hasFDerivAt_id z).sub (hasFDerivAt_const y z))
  have hh := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun z y : Space n => g y • fderiv ℝ (gaussianKernel t) (z-y))
    (F' := fun z y : Space n => g y • fderiv ℝ (fderiv ℝ (gaussianKernel t)) (z-y))
    (s := Metric.ball x 1) (bound := fun y => M * B (x-y))
    (Metric.ball_mem_nhds x (by norm_num))
    (Eventually.of_forall fun z =>
      (hg.smul (hs.continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable)
    hi (hg.smul (hHc.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
    (ae_of_all _ fun y z hz => ?_)
    ((hB.comp_sub_left x).const_mul M)
    (ae_of_all _ fun y z _ => (hd z y).const_smul (g y))
  · have heq : (fun z : Space n => ∫ y : Space n,
        g y • fderiv ℝ (gaussianKernel t) (z-y)) = fderiv ℝ (heatAverage t g) := by
      funext z
      exact (heatAverage_hasFDerivAt_kernel_of_bounded ht hg hM z).fderiv.symm
    rw [heq] at hh
    exact hh
  · have hz' : ‖z-x‖ ≤ 1 := by
      have hz0 : ‖z-x‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hz
      exact hz0.le
    have heq : z-y = (x-y)+(z-x) := by abel
    rw [norm_smul, Real.norm_eq_abs, heq]
    exact mul_le_mul (hM y) (hbound (x-y) (z-x) hz') (norm_nonneg _) hM0


theorem heatDuhamel_hasFDerivAt {n : ℕ} {f : Point n → ℝ} {M t : ℝ}
    (hf : Continuous f) (hM : ∀ p, |f p| ≤ M) (ht : 0 < t) (x : Space n) :
    HasFDerivAt (heatDuhamel f t)
      (∫ s in (0 : ℝ)..t, fderiv ℝ (heatAverage (t-s) (fun y => f (y,s))) x) x := by
  obtain ⟨C,hC,hGrad⟩ := heatAverage_fderiv_bound_of_bounded (n := n)
  let μ : Measure ℝ := volume.restrict (Set.Ioo 0 t)
  letI : IsFiniteMeasure μ := ⟨by simp [μ,Real.volume_Ioo]⟩
  have hfc (s : ℝ) : Continuous (fun y : Space n => f (y,s)) :=
    hf.comp (continuous_id.prodMk continuous_const)
  have hMs (s : ℝ) (y : Space n) : |f (y,s)| ≤ M := hM (y,s)
  have hAvgI (z : Space n) :
      Integrable (fun s : ℝ => heatAverage (t-s) (fun y => f (y,s)) z) μ :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp
      (heatDuhamel_integrable_and_bound hf hM ht.le z).1
  let J : ℝ × Space n → Space n →L[ℝ] ℝ := fun p =>
    f (p.2,p.1) • fderiv ℝ (gaussianKernel (t-p.1)) (x-p.2)
  have hJC : ContinuousOn J (Set.Ioo 0 t ×ˢ Set.univ) := by
    intro p hp
    have hKC : ContinuousAt (fun q : ℝ × Space n =>
        fderiv ℝ (gaussianKernel (t-q.1)) (x-q.2)) p :=
      ContinuousAt.comp
        (f := fun q : ℝ × Space n => (t-q.1,x-q.2))
        (g := fun q : ℝ × Space n => fderiv ℝ (gaussianKernel q.1) q.2)
        (gaussianKernel_fderiv_joint_smooth (sub_pos.mpr hp.1.2) (x-p.2)).continuousAt
        (by fun_prop)
    have hsc : Continuous (fun q : ℝ × Space n => f (q.2,q.1)) :=
      hf.comp (show Continuous (fun q : ℝ × Space n => (q.2,q.1)) from by fun_prop)
    exact (hsc.continuousAt.smul hKC).continuousWithinAt
  have hProd : μ.prod (volume : Measure (Space n)) =
      ((volume : Measure ℝ).prod (volume : Measure (Space n))).restrict
        (Set.Ioo 0 t ×ˢ (Set.univ : Set (Space n))) := by
    simpa only [μ,Measure.restrict_univ] using
      (Measure.prod_restrict (μ := (volume : Measure ℝ))
        (ν := (volume : Measure (Space n))) (Set.Ioo 0 t) Set.univ)
  have hJm : AEStronglyMeasurable J (μ.prod volume) := by
    rw [hProd]
    exact hJC.aestronglyMeasurable (measurableSet_Ioo.prod MeasurableSet.univ)
  have hGm : AEStronglyMeasurable
      (fun s : ℝ => fderiv ℝ (heatAverage (t-s) (fun y => f (y,s))) x) μ := by
    apply hJm.integral_prod_right'.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact (heatAverage_hasFDerivAt_kernel_of_bounded (sub_pos.mpr hs.2)
      (hfc s) (hMs s) x).fderiv.symm
  have hPow : IntervalIntegrable (fun s : ℝ => (t-s)^(-(1/2:ℝ))) volume 0 t := by
    simpa only [show (1:ℝ)/2-1 = -(1/2:ℝ) by ring] using
      schauder_time_weight_integrable (α := 1) (by norm_num) t
  have hBI : Integrable (fun s : ℝ => C*M*(t-s)^(-(1/2:ℝ))) μ :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp (hPow.const_mul (C*M))
  have hh := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := μ) (F := fun z (s : ℝ) => heatAverage (t-s) (fun y => f (y,s)) z)
    (F' := fun z s => fderiv ℝ (heatAverage (t-s) (fun y => f (y,s))) z)
    (s := Metric.ball x 1) (bound := fun s => C*M*(t-s)^(-(1/2:ℝ)))
    (Metric.ball_mem_nhds x (by norm_num))
    (Eventually.of_forall fun z => (hAvgI z).aestronglyMeasurable)
    (hAvgI x) hGm
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      intro z _
      exact hGrad (t-s) (sub_pos.mpr hs.2) (fun y => f (y,s)) M (hfc s) (hMs s) z)
    hBI
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      intro z _
      exact (heatAverage_hasFDerivAt_kernel_of_bounded (sub_pos.mpr hs.2)
        (hfc s) (hMs s) z).differentiableAt.hasFDerivAt)
  have heq : (fun z : Space n =>
      ∫ s, heatAverage (t-s) (fun y => f (y,s)) z ∂μ) = heatDuhamel f t := by
    funext z
    rw [heatDuhamel,intervalIntegral.integral_of_le ht.le,integral_Ioc_eq_integral_Ioo]
  rw [heq] at hh
  convert hh using 1
  rw [intervalIntegral.integral_of_le ht.le,integral_Ioc_eq_integral_Ioo]

theorem heatDuhamel_fderiv_bound {n : ℕ} :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : Point n → ℝ) (M : ℝ),
      Continuous f → (∀ p, |f p| ≤ M) → ∀ t : ℝ, 0 ≤ t → ∀ x : Space n,
        ‖fderiv ℝ (heatDuhamel f t) x‖ ≤ C*M*t^(1/2:ℝ) := by
  obtain ⟨C,hC,hGrad⟩ := heatAverage_fderiv_bound_of_bounded (n := n)
  refine ⟨2*C,by positivity,?_⟩
  intro f M hf hM t ht x
  have hM0 : 0 ≤ M := (abs_nonneg (f (0,0))).trans (hM (0,0))
  rcases ht.eq_or_lt with rfl | ht
  · have hz : heatDuhamel f 0 = fun _ : Space n => (0 : ℝ) := funext (heatDuhamel_zero f)
    simp only [hz, fderiv_const_apply, norm_zero]
    positivity
  have hPow : IntervalIntegrable (fun s : ℝ => (t-s)^(-(1/2:ℝ))) volume 0 t := by
    simpa only [show (1:ℝ)/2-1 = -(1/2:ℝ) by ring] using
      schauder_time_weight_integrable (α := 1) (by norm_num) t
  have hBI : IntegrableOn (fun s : ℝ => C*M*(t-s)^(-(1/2:ℝ))) (Set.Ioo 0 t) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp (hPow.const_mul (C*M))
  have hInt : (∫ s in Set.Ioo (0 : ℝ) t, (t-s)^(-(1/2:ℝ))) = 2*t^(1/2:ℝ) := by
    rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le ht.le]
    simpa only [show (1:ℝ)/2-1 = -(1/2:ℝ) by ring,div_one] using
      schauder_time_weight_integral (α := 1) (by norm_num) t
  rw [(heatDuhamel_hasFDerivAt hf hM ht x).fderiv,
    intervalIntegral.integral_of_le ht.le,integral_Ioc_eq_integral_Ioo]
  calc
    _ ≤ ∫ s in Set.Ioo (0 : ℝ) t, C*M*(t-s)^(-(1/2:ℝ)) := by
      apply norm_integral_le_of_norm_le hBI
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact hGrad (t-s) (sub_pos.mpr hs.2) (fun y => f (y,s)) M
        (hf.comp (continuous_id.prodMk continuous_const)) (fun y => hM (y,s)) x
    _ = (2*C)*M*t^(1/2:ℝ) := by rw [integral_const_mul,hInt]; ring


theorem heatDuhamel_fderiv_hasFDerivAt {n : ℕ} {α M H t : ℝ} {f : Point n → ℝ}
    (hα : 0 < α) (hf : Continuous f) (hM : ∀ p, |f p| ≤ M) (hH0 : 0 ≤ H)
    (hH : ∀ s x y, |f (x,s)-f (y,s)| ≤ H*‖x-y‖^α)
    (ht : 0 < t) (x : Space n) :
    HasFDerivAt (fderiv ℝ (heatDuhamel f t))
      (∫ s in (0 : ℝ)..t,
        fderiv ℝ (fderiv ℝ (heatAverage (t-s) (fun y => f (y,s)))) x) x := by
  obtain ⟨C1,hC1,hGrad⟩ := heatAverage_fderiv_bound_of_bounded (n := n)
  obtain ⟨C2,hC2,hHess⟩ := heatAverage_secondFDeriv_holder_bound (n := n) hα.le
  let μ : Measure ℝ := volume.restrict (Set.Ioo 0 t)
  letI : IsFiniteMeasure μ := ⟨by simp [μ,Real.volume_Ioo]⟩
  have hfc (s : ℝ) : Continuous (fun y : Space n => f (y,s)) :=
    hf.comp (continuous_id.prodMk continuous_const)
  have hMs (s : ℝ) (y : Space n) : |f (y,s)| ≤ M := hM (y,s)
  have hProd : μ.prod (volume : Measure (Space n)) =
      ((volume : Measure ℝ).prod (volume : Measure (Space n))).restrict
        (Set.Ioo 0 t ×ˢ (Set.univ : Set (Space n))) := by
    simpa only [μ,Measure.restrict_univ] using
      (Measure.prod_restrict (μ := (volume : Measure ℝ))
        (ν := (volume : Measure (Space n))) (Set.Ioo 0 t) Set.univ)
  have hGm (z : Space n) : AEStronglyMeasurable
      (fun s : ℝ => fderiv ℝ (heatAverage (t-s) (fun y => f (y,s))) z) μ := by
    let J : ℝ × Space n → Space n →L[ℝ] ℝ := fun p =>
      f (p.2,p.1) • fderiv ℝ (gaussianKernel (t-p.1)) (z-p.2)
    have hJC : ContinuousOn J (Set.Ioo 0 t ×ˢ Set.univ) := by
      intro p hp
      have hKC : ContinuousAt (fun q : ℝ × Space n =>
          fderiv ℝ (gaussianKernel (t-q.1)) (z-q.2)) p :=
        ContinuousAt.comp
          (f := fun q : ℝ × Space n => (t-q.1,z-q.2))
          (g := fun q : ℝ × Space n => fderiv ℝ (gaussianKernel q.1) q.2)
          (gaussianKernel_fderiv_joint_smooth (sub_pos.mpr hp.1.2) (z-p.2)).continuousAt
          (by fun_prop)
      have hsc : Continuous (fun q : ℝ × Space n => f (q.2,q.1)) :=
        hf.comp (show Continuous (fun q : ℝ × Space n => (q.2,q.1)) from by fun_prop)
      exact (hsc.continuousAt.smul hKC).continuousWithinAt
    have hJm : AEStronglyMeasurable J (μ.prod volume) := by
      rw [hProd]
      exact hJC.aestronglyMeasurable (measurableSet_Ioo.prod MeasurableSet.univ)
    apply hJm.integral_prod_right'.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact (heatAverage_hasFDerivAt_kernel_of_bounded (sub_pos.mpr hs.2)
      (hfc s) (hMs s) z).fderiv.symm
  have hHm : AEStronglyMeasurable
      (fun s : ℝ => fderiv ℝ (fderiv ℝ (heatAverage (t-s) (fun y => f (y,s)))) x) μ := by
    let J : ℝ × Space n → Space n →L[ℝ] Space n →L[ℝ] ℝ := fun p =>
      f (p.2,p.1) • fderiv ℝ (fderiv ℝ (gaussianKernel (t-p.1))) (x-p.2)
    have hJC : ContinuousOn J (Set.Ioo 0 t ×ˢ Set.univ) := by
      intro p hp
      have hKC : ContinuousAt (fun q : ℝ × Space n =>
          fderiv ℝ (fderiv ℝ (gaussianKernel (t-q.1))) (x-q.2)) p :=
        ContinuousAt.comp
          (f := fun q : ℝ × Space n => (t-q.1,x-q.2))
          (g := fun q : ℝ × Space n => fderiv ℝ (fderiv ℝ (gaussianKernel q.1)) q.2)
          (gaussianKernel_secondFDeriv_joint_smooth (sub_pos.mpr hp.1.2) (x-p.2)).continuousAt
          (by fun_prop)
      have hsc : Continuous (fun q : ℝ × Space n => f (q.2,q.1)) :=
        hf.comp (show Continuous (fun q : ℝ × Space n => (q.2,q.1)) from by fun_prop)
      exact (hsc.continuousAt.smul hKC).continuousWithinAt
    have hJm : AEStronglyMeasurable J (μ.prod volume) := by
      rw [hProd]
      exact hJC.aestronglyMeasurable (measurableSet_Ioo.prod MeasurableSet.univ)
    apply hJm.integral_prod_right'.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact (heatAverage_secondFDeriv_kernel_of_bounded (sub_pos.mpr hs.2)
      (hfc s) (hMs s) x).symm
  have hPow1 : IntervalIntegrable (fun s : ℝ => (t-s)^(-(1/2:ℝ))) volume 0 t := by
    simpa only [show (1:ℝ)/2-1 = -(1/2:ℝ) by ring] using
      schauder_time_weight_integrable (α := 1) (by norm_num) t
  have hBI1 : Integrable (fun s : ℝ => C1*M*(t-s)^(-(1/2:ℝ))) μ :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp (hPow1.const_mul (C1*M))
  have hGI (z : Space n) : Integrable
      (fun s : ℝ => fderiv ℝ (heatAverage (t-s) (fun y => f (y,s))) z) μ := by
    apply hBI1.mono' (hGm z)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact hGrad (t-s) (sub_pos.mpr hs.2) (fun y => f (y,s)) M (hfc s) (hMs s) z
  have hBI2 : Integrable (fun s : ℝ => C2*H*(t-s)^(α/2-1)) μ :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp
      ((schauder_time_weight_integrable hα t).const_mul (C2*H))
  have hh := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := μ)
    (F := fun z (s : ℝ) => fderiv ℝ (heatAverage (t-s) (fun y => f (y,s))) z)
    (F' := fun z s => fderiv ℝ (fderiv ℝ (heatAverage (t-s) (fun y => f (y,s)))) z)
    (s := Metric.ball x 1) (bound := fun s => C2*H*(t-s)^(α/2-1))
    (Metric.ball_mem_nhds x (by norm_num))
    (Eventually.of_forall fun z => hGm z)
    (hGI x) hHm
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      intro z _
      exact hHess (t-s) (sub_pos.mpr hs.2) (fun y => f (y,s)) M H
        (hfc s) (hMs s) hH0 (hH s) z)
    hBI2
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      intro z _
      exact (heatAverage_fderiv_hasFDerivAt_kernel_of_bounded (sub_pos.mpr hs.2)
        (hfc s) (hMs s) z).differentiableAt.hasFDerivAt)
  have heq : (fun z : Space n =>
      ∫ s, fderiv ℝ (heatAverage (t-s) (fun y => f (y,s))) z ∂μ) =
        fderiv ℝ (heatDuhamel f t) := by
    funext z
    rw [(heatDuhamel_hasFDerivAt hf hM ht z).fderiv,
      intervalIntegral.integral_of_le ht.le,integral_Ioc_eq_integral_Ioo]
  rw [heq] at hh
  convert hh using 1
  rw [intervalIntegral.integral_of_le ht.le,integral_Ioc_eq_integral_Ioo]

theorem heatDuhamel_secondFDeriv_bound {n : ℕ} {α : ℝ} (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : Point n → ℝ) (M H : ℝ),
      Continuous f → (∀ p, |f p| ≤ M) → 0 ≤ H →
      (∀ s x y, |f (x,s)-f (y,s)| ≤ H*‖x-y‖^α) →
      ∀ t : ℝ, 0 ≤ t → ∀ x : Space n,
        ‖fderiv ℝ (fderiv ℝ (heatDuhamel f t)) x‖ ≤ C*H*t^(α/2) := by
  obtain ⟨C,hC,hHess⟩ := heatAverage_secondFDeriv_holder_bound (n := n) hα.le
  refine ⟨C*(2/α),by positivity,?_⟩
  intro f M H hf hM hH0 hH t ht x
  rcases ht.eq_or_lt with rfl | ht
  · have hz : heatDuhamel f 0 = fun _ : Space n => (0 : ℝ) := funext (heatDuhamel_zero f)
    have hdz : fderiv ℝ (heatDuhamel f 0) =
        fun _ : Space n => (0 : Space n →L[ℝ] ℝ) := by
      rw [hz,fderiv_fun_const]
      rfl
    rw [hdz,fderiv_const_apply,norm_zero]
    positivity
  have hBI : IntegrableOn (fun s : ℝ => C*H*(t-s)^(α/2-1)) (Set.Ioo 0 t) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp
      ((schauder_time_weight_integrable hα t).const_mul (C*H))
  have hInt : (∫ s in Set.Ioo (0 : ℝ) t, (t-s)^(α/2-1)) = (2/α)*t^(α/2) := by
    rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le ht.le]
    exact schauder_time_weight_integral hα t
  rw [(heatDuhamel_fderiv_hasFDerivAt hα hf hM hH0 hH ht x).fderiv,
    intervalIntegral.integral_of_le ht.le,integral_Ioc_eq_integral_Ioo]
  calc
    _ ≤ ∫ s in Set.Ioo (0 : ℝ) t, C*H*(t-s)^(α/2-1) := by
      apply norm_integral_le_of_norm_le hBI
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact hHess (t-s) (sub_pos.mpr hs.2) (fun y => f (y,s)) M H
        (hf.comp (continuous_id.prodMk continuous_const)) (fun y => hM (y,s)) hH0 (hH s) x
    _ = (C*(2/α))*H*t^(α/2) := by rw [integral_const_mul,hInt]; ring

theorem heatDuhamel_derivative_bounds_of_holder {n : ℕ} {α : ℝ} (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ T F : ℝ, 0 ≤ T → ∀ f : Point n → ℝ,
      HolderBound α (cylinder Set.univ 0 T) f F →
      ∀ t ∈ Set.Icc 0 T, ∀ x : Space n,
        ‖fderiv ℝ (heatDuhamel f t) x‖ ≤ C*F*t^(1/2:ℝ) ∧
        ‖fderiv ℝ (fderiv ℝ (heatDuhamel f t)) x‖ ≤ C*F*t^(α/2) := by
  obtain ⟨C1,hC1,hGrad⟩ := heatDuhamel_fderiv_bound (n := n)
  obtain ⟨C2,hC2,hHess⟩ := heatDuhamel_secondFDeriv_bound (n := n) hα
  refine ⟨C1+C2,by positivity,?_⟩
  intro T F hT f hf t ht x
  let g : Point n → ℝ := fun p => f (p.1,max 0 (min p.2 T))
  have hhat : HolderBound α Set.univ g F := holderBound_timeClamp hα.le hT hf
  have hc : Continuous g := continuousOn_univ.mp (holderBound_continuousOn hα hhat)
  have hb (p : Point n) : |g p| ≤ F := by
    simpa only [Real.norm_eq_abs] using hhat.2.1 p (Set.mem_univ _)
  have hh (s : ℝ) (x y : Space n) : |g (x,s)-g (y,s)| ≤ F*‖x-y‖^α := by
    simpa only [holderWeight,sub_self,abs_zero,
      Real.zero_rpow (by positivity : α/2 ≠ 0),add_zero,Real.norm_eq_abs] using
      hhat.2.2 (x,s) (Set.mem_univ _) (y,s) (Set.mem_univ _)
  have heq : heatDuhamel g t = heatDuhamel f t := funext (heatDuhamel_timeClamp f ht)
  rw [← heq]
  constructor
  · exact (hGrad g F hc hb t ht.1 x).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : C1 ≤ C1+C2) hf.1)
        (Real.rpow_nonneg ht.1 _))
  · exact (hHess g F F hc hb hf.1 hh t ht.1 x).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : C2 ≤ C1+C2) hf.1)
        (Real.rpow_nonneg ht.1 _))


theorem heatAverage_sub_initial_holder_bound {n : ℕ} {α : ℝ} (hα : 0 ≤ α) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ∀ (g : Space n → ℝ) (M H : ℝ),
      Continuous g → (∀ y, |g y| ≤ M) → 0 ≤ H →
      (∀ x y, |g x-g y| ≤ H*‖x-y‖^α) → ∀ x : Space n,
        |heatAverage t g x-g x| ≤ C*H*t^(α/2) := by
  obtain ⟨C,hC,hMom⟩ := gaussianKernel_weight_integral_bound (n := n) hα
  refine ⟨C,hC,?_⟩
  intro t ht g M H hg hM hH0 hH x
  have hKi := gaussianKernel_integrable (n := n) ht
  have hi : Integrable (fun y : Space n => gaussianKernel t y*g (x-y)) :=
    hKi.mul_bdd (hg.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (ae_of_all _ fun y => by simpa only [Real.norm_eq_abs] using hM (x-y))
  have hic : Integrable (fun y : Space n => gaussianKernel t y*g x) := hKi.mul_const _
  have heq : heatAverage t g x-g x =
      ∫ y : Space n, gaussianKernel t y*(g (x-y)-g x) := by
    calc
      _ = (∫ y : Space n, gaussianKernel t y*g (x-y)) -
          ∫ y : Space n, gaussianKernel t y*g x := by
        rw [integral_mul_const,gaussianKernel_integral ht,one_mul]
        rfl
      _ = ∫ y : Space n, gaussianKernel t y*g (x-y)-gaussianKernel t y*g x :=
        (integral_sub hi hic).symm
      _ = _ := by congr 1; funext y; ring
  rw [heq,← Real.norm_eq_abs]
  calc
    _ ≤ ∫ y : Space n, H*(‖y‖^α*gaussianKernel t y) := by
      apply norm_integral_le_of_norm_le ((hMom t ht).1.const_mul H)
      filter_upwards [] with y
      have hh := hH (x-y) x
      have hy : (x-y)-x = -y := by abel
      rw [hy,norm_neg] at hh
      rw [Real.norm_eq_abs,abs_mul,abs_of_pos (gaussianKernel_pos ht y)]
      calc
        _ ≤ gaussianKernel t y*(H*‖y‖^α) :=
          mul_le_mul_of_nonneg_left hh (gaussianKernel_pos ht y).le
        _ = _ := by ring
    _ = H*(∫ y : Space n, ‖y‖^α*gaussianKernel t y) := integral_const_mul _ _
    _ ≤ H*(C*t^(α/2)) := mul_le_mul_of_nonneg_left (hMom t ht).2 hH0
    _ = C*H*t^(α/2) := by ring

theorem heatAverage_tendsto_initial_of_holder {n : ℕ} {α M H : ℝ} {g : Space n → ℝ}
    (hα : 0 < α) (hg : Continuous g) (hM : ∀ y, |g y| ≤ M) (hH0 : 0 ≤ H)
    (hH : ∀ x y, |g x-g y| ≤ H*‖x-y‖^α) (x : Space n) :
    Tendsto (fun t : ℝ => heatAverage t g x) (𝓝[>] 0) (𝓝 (g x)) := by
  obtain ⟨C,hC,hbound⟩ := heatAverage_sub_initial_holder_bound (n := n) hα.le
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hW : Continuous (fun t : ℝ => C*H*t^(α/2)) :=
    continuous_const.mul (Real.continuous_rpow_const (by positivity))
  have hlim : Tendsto (fun t : ℝ => C*H*t^(α/2)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.zero_rpow (by positivity : α/2 ≠ 0),mul_zero] using
      (hW.tendsto 0).mono_left nhdsWithin_le_nhds
  apply squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) _ hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  simpa only [Real.norm_eq_abs] using hbound t ht g M H hg hM hH0 hH x


theorem heatDuhamel_initial_spatial_jets_continuousWithinAt {n : ℕ} {α F T : ℝ}
    {f : Point n → ℝ} (hα : 0 < α) (hT : 0 ≤ T)
    (hf : HolderBound α (cylinder Set.univ 0 T) f F) (x : Space n) :
    ContinuousWithinAt (fun p : Point n => heatDuhamel f p.2 p.1)
        (cylinder Set.univ 0 T) (x,0) ∧
      ContinuousWithinAt (fun p : Point n => fderiv ℝ (heatDuhamel f p.2) p.1)
        (cylinder Set.univ 0 T) (x,0) ∧
      ContinuousWithinAt (fun p : Point n => fderiv ℝ (fderiv ℝ (heatDuhamel f p.2)) p.1)
        (cylinder Set.univ 0 T) (x,0) := by
  obtain ⟨C,hC,hbound⟩ := heatDuhamel_derivative_bounds_of_holder (n := n) hα
  have hc {E : Type} [NormedAddCommGroup E] (u : Point n → E) (K β : ℝ)
      (hβ : 0 < β) (hu : u (x,0) = 0)
      (hb : ∀ p ∈ cylinder Set.univ 0 T, ‖u p‖ ≤ K*p.2^β) :
      ContinuousWithinAt u (cylinder Set.univ 0 T) (x,0) := by
    rw [ContinuousWithinAt,hu]
    apply squeeze_zero_norm'
    · filter_upwards [self_mem_nhdsWithin] with p hp
      exact hb p hp
    · have hW : Continuous (fun p : Point n => K*p.2^β) :=
        continuous_const.mul ((Real.continuous_rpow_const hβ.le).comp continuous_snd)
      simpa only [Real.zero_rpow hβ.ne',mul_zero] using
        (hW.tendsto (x,0)).mono_left nhdsWithin_le_nhds
  have hz : heatDuhamel f 0 = fun _ : Space n => (0 : ℝ) := funext (heatDuhamel_zero f)
  have hdz : fderiv ℝ (heatDuhamel f 0) =
      fun _ : Space n => (0 : Space n →L[ℝ] ℝ) := by
    rw [hz,fderiv_fun_const]
    rfl
  refine ⟨hc _ F 1 (by norm_num) (heatDuhamel_zero f x) ?_,
    hc _ (C*F) (1/2) (by norm_num) ?_ ?_,
    hc _ (C*F) (α/2) (by positivity) ?_ ?_⟩
  · intro p hp
    simpa only [Real.norm_eq_abs,Real.rpow_one,mul_comm] using
      heatDuhamel_bound_of_holder hα hT hf hp.2 p.1
  · simp only [hz,fderiv_const_apply]
  · intro p hp
    exact (hbound T F hT f hf p.2 hp.2 p.1).1
  · simp only [hdz,fderiv_const_apply]
  · intro p hp
    exact (hbound T F hT f hf p.2 hp.2 p.1).2


theorem heatDuhamel_initial_quotient_bound {n : ℕ} {α : ℝ} (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : Point n → ℝ) (F : ℝ),
      HolderBound α Set.univ f F → ∀ t : ℝ, 0 < t → ∀ x : Space n,
        |heatDuhamel f t x/t-f (x,0)| ≤ C*F*t^(α/2) := by
  obtain ⟨C,hC,hAvg⟩ := heatAverage_sub_initial_holder_bound (n := n) hα.le
  refine ⟨C+1,by positivity,?_⟩
  intro f F hf t ht x
  have hc : Continuous f := continuousOn_univ.mp (holderBound_continuousOn hα hf)
  have hb (p : Point n) : |f p| ≤ F := by
    simpa only [Real.norm_eq_abs] using hf.2.1 p (Set.mem_univ _)
  have hsHolder (s : ℝ) (y z : Space n) : |f (y,s)-f (z,s)| ≤ F*‖y-z‖^α := by
    simpa only [holderWeight,sub_self,abs_zero,
      Real.zero_rpow (by positivity : α/2 ≠ 0),add_zero,Real.norm_eq_abs] using
      hf.2.2 (y,s) (Set.mem_univ _) (z,s) (Set.mem_univ _)
  have hti := (heatDuhamel_integrable_and_bound hc hb ht.le x).1
  have hpoint (s : ℝ) (hs : s ∈ Set.Ioo 0 t) :
      ‖heatAverage (t-s) (fun y => f (y,s)) x-f (x,0)‖ ≤ (C+1)*F*t^(α/2) := by
    have hspace := hAvg (t-s) (sub_pos.mpr hs.2) (fun y => f (y,s)) F F
      (hc.comp (continuous_id.prodMk continuous_const)) (fun y => hb (y,s))
      hf.1 (hsHolder s) x
    have htime : |f (x,s)-f (x,0)| ≤ F*s^(α/2) := by
      simpa only [holderWeight,sub_self,norm_zero,Real.zero_rpow hα.ne',zero_add,
        sub_zero,abs_of_pos hs.1,Real.norm_eq_abs] using
        hf.2.2 (x,s) (Set.mem_univ _) (x,0) (Set.mem_univ _)
    rw [Real.norm_eq_abs]
    calc
      _ ≤ |heatAverage (t-s) (fun y => f (y,s)) x-f (x,s)| + |f (x,s)-f (x,0)| :=
        abs_sub_le _ _ _
      _ ≤ C*F*(t-s)^(α/2)+F*s^(α/2) := add_le_add hspace htime
      _ ≤ C*F*t^(α/2)+F*t^(α/2) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (sub_pos.mpr hs.2).le (by linarith [hs.1]) (by positivity))
            (mul_nonneg hC.le hf.1)
        · exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow hs.1.le hs.2.le (by positivity)) hf.1
      _ = _ := by ring
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const_ae
    (a := (0 : ℝ)) (b := t)
    (f := fun s : ℝ => heatAverage (t-s) (fun y => f (y,s)) x-f (x,0))
    (C := (C+1)*F*t^(α/2)) (by
      filter_upwards [(volume : Measure ℝ).ae_ne t] with s hst
      intro hs
      have hs' : s ∈ Set.Ioc 0 t := by simpa only [Set.uIoc_of_le ht.le] using hs
      exact hpoint s ⟨hs'.1,lt_of_le_of_ne hs'.2 hst⟩)
  rw [intervalIntegral.integral_sub hti (intervalIntegrable_const),
    intervalIntegral.integral_const,sub_zero,smul_eq_mul,abs_of_pos ht,
    ← heatDuhamel] at hn
  have heq : heatDuhamel f t x/t-f (x,0) =
      (heatDuhamel f t x-t*f (x,0))/t := by field_simp
  rw [heq,abs_div,abs_of_pos ht]
  exact (div_le_iff₀ ht).mpr hn

theorem heatDuhamel_hasDerivWithinAt_zero_of_global_holder {n : ℕ} {α F : ℝ}
    {f : Point n → ℝ} (hα : 0 < α) (hf : HolderBound α Set.univ f F) (x : Space n) :
    HasDerivWithinAt (fun t : ℝ => heatDuhamel f t x) (f (x,0)) (Set.Ici 0) 0 := by
  obtain ⟨C,hC,hbound⟩ := heatDuhamel_initial_quotient_bound (n := n) hα
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hset : Set.Ici (0 : ℝ) \ {0} = Set.Ioi 0 := by
    ext t
    simp only [Set.mem_sdiff,Set.mem_Ici,Set.mem_singleton_iff,Set.mem_Ioi]
    constructor
    · intro h
      exact lt_of_le_of_ne h.1 (fun h0 => h.2 h0.symm)
    · intro h
      exact ⟨h.le,h.ne'⟩
  rw [hset]
  have hslope : slope (fun t : ℝ => heatDuhamel f t x) 0 =
      fun t : ℝ => heatDuhamel f t x/t := by
    funext t
    simp only [slope_def_field,heatDuhamel_zero,sub_zero]
  rw [hslope]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hW : Continuous (fun t : ℝ => C*F*t^(α/2)) :=
    continuous_const.mul (Real.continuous_rpow_const (by positivity))
  have hlim : Tendsto (fun t : ℝ => C*F*t^(α/2)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.zero_rpow (by positivity : α/2 ≠ 0),mul_zero] using
      (hW.tendsto 0).mono_left nhdsWithin_le_nhds
  apply squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) _ hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  simpa only [Real.norm_eq_abs] using hbound f F hf t ht x

theorem heatDuhamel_hasDerivWithinAt_zero_of_holder {n : ℕ} {α F T : ℝ}
    {f : Point n → ℝ} (hα : 0 < α) (hT : 0 ≤ T)
    (hf : HolderBound α (cylinder Set.univ 0 T) f F) (x : Space n) :
    HasDerivWithinAt (fun t : ℝ => heatDuhamel f t x) (f (x,0)) (Set.Icc 0 T) 0 := by
  let g : Point n → ℝ := fun p => f (p.1,max 0 (min p.2 T))
  have hhat : HolderBound α Set.univ g F := holderBound_timeClamp hα.le hT hf
  have hh := heatDuhamel_hasDerivWithinAt_zero_of_global_holder hα hhat x
  have hg0 : g (x,0) = f (x,0) := by simp [g,min_eq_left hT]
  rw [hg0] at hh
  exact hh.congr_mono (fun t ht => (heatDuhamel_timeClamp f ht x).symm)
    (by simp only [heatDuhamel_zero]) (fun t ht => ht.1)

theorem heatDuhamel_derivWithin_zero_of_holder {n : ℕ} {α F T : ℝ}
    {f : Point n → ℝ} (hα : 0 < α) (hT : 0 < T)
    (hf : HolderBound α (cylinder Set.univ 0 T) f F) (x : Space n) :
    derivWithin (fun t : ℝ => heatDuhamel f t x) (Set.Icc 0 T) 0 = f (x,0) :=
  (heatDuhamel_hasDerivWithinAt_zero_of_holder hα hT.le hf x).derivWithin
    (uniqueDiffOn_Icc hT 0 ⟨le_rfl,hT.le⟩)


theorem heatAverage_secondFDeriv_time_integrable {n : ℕ} {α M H t : ℝ} {f : Point n → ℝ}
    (hα : 0 < α) (hf : Continuous f) (hM : ∀ p, |f p| ≤ M) (hH0 : 0 ≤ H)
    (hH : ∀ s x y, |f (x,s)-f (y,s)| ≤ H*‖x-y‖^α)
    (ht : 0 < t) (x : Space n) :
    IntervalIntegrable (fun s : ℝ =>
      fderiv ℝ (fderiv ℝ (heatAverage (t-s) (fun y => f (y,s)))) x) volume 0 t := by
  obtain ⟨C,hC,hHess⟩ := heatAverage_secondFDeriv_holder_bound (n := n) hα.le
  let μ : Measure ℝ := volume.restrict (Set.Ioo 0 t)
  have hfc (s : ℝ) : Continuous (fun y : Space n => f (y,s)) :=
    hf.comp (continuous_id.prodMk continuous_const)
  have hMs (s : ℝ) (y : Space n) : |f (y,s)| ≤ M := hM (y,s)
  have hProd : μ.prod (volume : Measure (Space n)) =
      ((volume : Measure ℝ).prod (volume : Measure (Space n))).restrict
        (Set.Ioo 0 t ×ˢ (Set.univ : Set (Space n))) := by
    simpa only [μ,Measure.restrict_univ] using
      (Measure.prod_restrict (μ := (volume : Measure ℝ))
        (ν := (volume : Measure (Space n))) (Set.Ioo 0 t) Set.univ)
  have hHm : AEStronglyMeasurable
      (fun s : ℝ => fderiv ℝ (fderiv ℝ (heatAverage (t-s) (fun y => f (y,s)))) x) μ := by
    let J : ℝ × Space n → Space n →L[ℝ] Space n →L[ℝ] ℝ := fun p =>
      f (p.2,p.1) • fderiv ℝ (fderiv ℝ (gaussianKernel (t-p.1))) (x-p.2)
    have hJC : ContinuousOn J (Set.Ioo 0 t ×ˢ Set.univ) := by
      intro p hp
      have hKC : ContinuousAt (fun q : ℝ × Space n =>
          fderiv ℝ (fderiv ℝ (gaussianKernel (t-q.1))) (x-q.2)) p :=
        ContinuousAt.comp
          (f := fun q : ℝ × Space n => (t-q.1,x-q.2))
          (g := fun q : ℝ × Space n => fderiv ℝ (fderiv ℝ (gaussianKernel q.1)) q.2)
          (gaussianKernel_secondFDeriv_joint_smooth (sub_pos.mpr hp.1.2) (x-p.2)).continuousAt
          (by fun_prop)
      have hsc : Continuous (fun q : ℝ × Space n => f (q.2,q.1)) :=
        hf.comp (show Continuous (fun q : ℝ × Space n => (q.2,q.1)) from by fun_prop)
      exact (hsc.continuousAt.smul hKC).continuousWithinAt
    have hJm : AEStronglyMeasurable J (μ.prod volume) := by
      rw [hProd]
      exact hJC.aestronglyMeasurable (measurableSet_Ioo.prod MeasurableSet.univ)
    apply hJm.integral_prod_right'.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact (heatAverage_secondFDeriv_kernel_of_bounded (sub_pos.mpr hs.2)
      (hfc s) (hMs s) x).symm
  have hBI : Integrable (fun s : ℝ => C*H*(t-s)^(α/2-1)) μ :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp
      ((schauder_time_weight_integrable hα t).const_mul (C*H))
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mpr
  apply hBI.mono' hHm
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  exact hHess (t-s) (sub_pos.mpr hs.2) (fun y => f (y,s)) M H
    (hfc s) (hMs s) hH0 (hH s) x


theorem heatAverage_secondFDeriv_spatial_increment_bound {n : ℕ} {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ∀ (g : Space n → ℝ) (M H : ℝ),
      Continuous g → (∀ y, |g y| ≤ M) → 0 ≤ H →
      (∀ x y, |g x-g y| ≤ H*‖x-y‖^α) →
      ∀ x h : Space n, ‖h‖ ≤ Real.sqrt t →
        ‖fderiv ℝ (fderiv ℝ (heatAverage t g)) (x+h) -
          fderiv ℝ (fderiv ℝ (heatAverage t g)) x‖ ≤ C*H*‖h‖*t^(α/2-3/2) := by
  obtain ⟨C,hC,hbound⟩ := gaussianKernel_secondFDeriv_shift_weight_bound (n := n) hα hα1
  refine ⟨C,hC,?_⟩
  intro t ht g M H hg hM hH0 hH x h hh
  let D : Space n → Space n →L[ℝ] Space n →L[ℝ] ℝ :=
    fderiv ℝ (fderiv ℝ (gaussianKernel t))
  let K : Space n → Space n →L[ℝ] Space n →L[ℝ] ℝ := fun y => D (y+h)-D y
  have hDc : Continuous D :=
    (((gaussianKernel_spatial_smooth (n := n) t).fderiv_right (m := ∞)
      (by simp)).continuous_fderiv (by simp))
  have hDi : Integrable D := by
    apply (integrable_norm_iff hDc.aestronglyMeasurable).mp
    simpa only [D,Real.rpow_zero,mul_one] using
      (gaussianKernel_secondFDeriv_weight_integrable_bound (n := n) (s := 0)
        (by norm_num) ht).1
  have hKc : Continuous K := (hDc.comp (continuous_id.add continuous_const)).sub hDc
  have hKi : Integrable K := (hDi.comp_add_right h).sub hDi
  have hK0 : (∫ y : Space n, K y) = 0 := by
    dsimp [K]
    rw [integral_sub (hDi.comp_add_right h) hDi,integral_add_right_eq_self,sub_self]
  have hi (z : Space n) : Integrable (fun y : Space n => g y • D (z-y)) := by
    convert (hDi.comp_sub_left z).bdd_smul M hg.aestronglyMeasurable
      (ae_of_all _ fun y => by simpa only [Real.norm_eq_abs] using hM y) using 1
  have heq : fderiv ℝ (fderiv ℝ (heatAverage t g)) (x+h) -
        fderiv ℝ (fderiv ℝ (heatAverage t g)) x =
      ∫ y : Space n, (g (x-y)-g x) • K y := by
    rw [heatAverage_secondFDeriv_kernel_of_bounded ht hg hM (x+h),
      heatAverage_secondFDeriv_kernel_of_bounded ht hg hM x]
    calc
      _ = ∫ y : Space n, g y • D (x+h-y)-g y • D (x-y) :=
        (integral_sub (hi (x+h)) (hi x)).symm
      _ = ∫ y : Space n, g (x-y) • D (x+h-(x-y))-g (x-y) • D (x-(x-y)) :=
        (integral_sub_left_eq_self
          (fun y : Space n => g y • D (x+h-y)-g y • D (x-y)) volume x).symm
      _ = ∫ y : Space n, g (x-y) • K y := by
        congr 1
        funext y
        have h1 : x+h-(x-y) = y+h := by abel
        rw [h1,sub_sub_cancel,← smul_sub]
      _ = _ := integral_smul_sub_const_of_zero_integral hKc hKi.norm hK0
        (hg.comp (continuous_const.sub continuous_id)) (fun y => hM (x-y)) (g x)
  rw [heq]
  calc
    _ ≤ ∫ y : Space n, H*(‖K y‖*‖y‖^α) := by
      apply norm_integral_le_of_norm_le ((hbound t ht h hh).1.const_mul H)
      filter_upwards [] with y
      have hy := hH (x-y) x
      have he : (x-y)-x = -y := by abel
      rw [he,norm_neg] at hy
      calc
        _ ≤ ‖g (x-y)-g x‖*‖K y‖ := ContinuousLinearMap.opNorm_smul_le _ _
        _ = |g (x-y)-g x| *‖K y‖ := by rw [Real.norm_eq_abs]
        _ ≤ (H*‖y‖^α)*‖K y‖ := mul_le_mul_of_nonneg_right hy (K y).opNorm_nonneg
        _ = _ := by ring
    _ = H*(∫ y : Space n, ‖K y‖*‖y‖^α) := integral_const_mul _ _
    _ ≤ H*(C*‖h‖*t^(α/2-3/2)) := mul_le_mul_of_nonneg_left (hbound t ht h hh).2 hH0
    _ = C*H*‖h‖*t^(α/2-3/2) := by ring


theorem schauder_spatial_near_weight_integral {α d : ℝ} (hα : 0 < α) (hd : 0 < d) :
    (∫ r in (0 : ℝ)..d^2, r^(α/2-1)) = (2/α)*d^α := by
  rw [integral_rpow (Or.inl (by linarith : -1 < α/2-1)),
    show α/2-1+1 = α/2 by ring,
    Real.zero_rpow (by positivity : α/2 ≠ 0),sub_zero]
  have hp : (d^2)^(α/2) = d^α := by
    rw [← Real.rpow_natCast_mul hd.le 2]
    congr 1
    ring
  rw [hp]
  field_simp [hα.ne']

theorem schauder_spatial_tail_weight_bound {α d t : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hd : 0 < d) (hdt : d^2 ≤ t) :
    IntervalIntegrable (fun r : ℝ => r^(α/2-3/2)) volume (d^2) t ∧
      (∫ r in d^2..t, r^(α/2-3/2)) ≤ (2/(1-α))*d^(α-1) := by
  have hd2 : 0 < d^2 := sq_pos_of_pos hd
  have ht : 0 < t := hd2.trans_le hdt
  have hnot : (0 : ℝ) ∉ Set.uIcc (d^2) t := by
    rw [Set.uIcc_of_le hdt]
    intro h
    exact (not_le_of_gt hd2) h.1
  refine ⟨intervalIntegral.intervalIntegrable_rpow (Or.inr hnot),?_⟩
  rw [integral_rpow (Or.inr ⟨(by linarith : α/2-3/2 ≠ -1),hnot⟩)]
  have hp : (d^2)^(α/2-3/2+1) = d^(α-1) := by
    rw [← Real.rpow_natCast_mul hd.le 2]
    congr 1
    ring
  rw [hp]
  have hden : 1-α ≠ 0 := by linarith
  have heq : (t^(α/2-3/2+1)-d^(α-1))/(α/2-3/2+1) =
      (d^(α-1)-t^(α/2-3/2+1))/((1-α)/2) := by
    rw [show α/2-3/2+1 = -((1-α)/2) by ring,div_neg,← neg_div,neg_sub]
  rw [heq]
  calc
    _ ≤ d^(α-1)/((1-α)/2) :=
      div_le_div_of_nonneg_right (by linarith [Real.rpow_nonneg ht.le (α/2-3/2+1)])
        (by linarith)
    _ = (2/(1-α))*d^(α-1) := by field_simp [hden]

theorem schauder_spatial_near_far_integral_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {α A B d t : ℝ} {F : ℝ → E}
    (hα : 0 < α) (hα1 : α < 1) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hd : 0 < d) (ht : 0 < t) (hFi : IntervalIntegrable F volume 0 t)
    (hnear : ∀ r ∈ Set.Ioc 0 t, ‖F r‖ ≤ A*r^(α/2-1))
    (hfar : ∀ r ∈ Set.Ioc (d^2) t, ‖F r‖ ≤ B*d*r^(α/2-3/2)) :
    ‖∫ r in (0 : ℝ)..t, F r‖ ≤ (2*A/α+2*B/(1-α))*d^α := by
  have hdα : 0 ≤ d^α := Real.rpow_nonneg hd.le _
  have hC : 0 ≤ 2*B/(1-α) := div_nonneg (by positivity) (by linarith)
  have hpowI : IntervalIntegrable (fun r : ℝ => r^(α/2-1)) volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hpowEq : (∫ r in (0 : ℝ)..t, r^(α/2-1)) = (2/α)*t^(α/2) := by
    rw [integral_rpow (Or.inl (by linarith : -1 < α/2-1)),
      show α/2-1+1 = α/2 by ring,
      Real.zero_rpow (by positivity : α/2 ≠ 0),sub_zero]
    field_simp [hα.ne']
  by_cases htd : t ≤ d^2
  · have hn := intervalIntegral.norm_integral_le_of_norm_le ht.le
      (ae_of_all _ fun r hr => hnear r hr) (hpowI.const_mul A)
    rw [intervalIntegral.integral_const_mul,hpowEq] at hn
    have htp : t^(α/2) ≤ d^α := by
      apply (Real.rpow_le_rpow ht.le htd (by positivity)).trans_eq
      rw [← Real.rpow_natCast_mul hd.le 2]
      congr 1
      ring
    calc
      _ ≤ A*((2/α)*t^(α/2)) := hn
      _ ≤ (2*A/α)*d^α := by
        have hh := mul_le_mul_of_nonneg_left htp
          (show 0 ≤ A*(2/α) by positivity)
        convert hh using 1 <;> ring
      _ ≤ _ := by nlinarith [mul_nonneg hC hdα]
  · have hdt : d^2 < t := lt_of_not_ge htd
    have hd2 : 0 < d^2 := sq_pos_of_pos hd
    have hFnear : IntervalIntegrable F volume 0 (d^2) := hFi.mono_set (by
      rw [Set.uIcc_of_le hd2.le,Set.uIcc_of_le ht.le]
      exact Set.Icc_subset_Icc le_rfl hdt.le)
    have hFfar : IntervalIntegrable F volume (d^2) t := hFi.mono_set (by
      rw [Set.uIcc_of_le hdt.le,Set.uIcc_of_le ht.le]
      exact Set.Icc_subset_Icc hd2.le le_rfl)
    have hNI : IntervalIntegrable (fun r : ℝ => r^(α/2-1)) volume 0 (d^2) :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    have hn := intervalIntegral.norm_integral_le_of_norm_le hd2.le
      (ae_of_all _ fun r hr => hnear r ⟨hr.1,hr.2.trans hdt.le⟩) (hNI.const_mul A)
    rw [intervalIntegral.integral_const_mul,schauder_spatial_near_weight_integral hα hd] at hn
    obtain ⟨hTI,hTB⟩ := schauder_spatial_tail_weight_bound hα hα1 hd hdt.le
    have hb := intervalIntegral.norm_integral_le_of_norm_le hdt.le
      (ae_of_all _ fun r hr => hfar r hr) (hTI.const_mul (B*d))
    rw [intervalIntegral.integral_const_mul] at hb
    have hdp : d*d^(α-1) = d^α := by
      have hh := Real.rpow_add hd 1 (α-1)
      simpa only [Real.rpow_one,show (1:ℝ)+(α-1) = α by ring] using hh.symm
    have hb' : ‖∫ r in d^2..t, F r‖ ≤ (2*B/(1-α))*d^α := by
      calc
        _ ≤ (B*d)*(∫ r in d^2..t, r^(α/2-3/2)) := hb
        _ ≤ (B*d)*((2/(1-α))*d^(α-1)) :=
          mul_le_mul_of_nonneg_left hTB (by positivity)
        _ = (2*B/(1-α))*(d*d^(α-1)) := by ring
        _ = _ := by rw [hdp]
    rw [← intervalIntegral.integral_add_adjacent_intervals hFnear hFfar]
    calc
      _ ≤ ‖∫ r in (0 : ℝ)..d^2, F r‖+‖∫ r in d^2..t, F r‖ := norm_add_le _ _
      _ ≤ A*((2/α)*d^α)+(2*B/(1-α))*d^α := add_le_add hn hb'
      _ = _ := by ring


theorem heatDuhamel_secondFDeriv_spatial_holder_bound {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : Point n → ℝ) (M H : ℝ),
      Continuous f → (∀ p, |f p| ≤ M) → 0 ≤ H →
      (∀ s x y, |f (x,s)-f (y,s)| ≤ H*‖x-y‖^α) →
      ∀ t : ℝ, 0 ≤ t → ∀ x h : Space n,
        ‖fderiv ℝ (fderiv ℝ (heatDuhamel f t)) (x+h) -
          fderiv ℝ (fderiv ℝ (heatDuhamel f t)) x‖ ≤ C*H*‖h‖^α := by
  obtain ⟨C2,hC2,hHess⟩ := heatAverage_secondFDeriv_holder_bound (n := n) hα.le
  obtain ⟨C3,hC3,hInc⟩ := heatAverage_secondFDeriv_spatial_increment_bound
    (n := n) hα.le hα1.le
  let C : ℝ := 4*C2/α+2*C3/(1-α)
  have hOne : 0 < 1-α := sub_pos.mpr hα1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro f M H hf hM hH0 hH t ht x h
  rcases ht.eq_or_lt with rfl | ht
  · have hz : heatDuhamel f 0 = fun _ : Space n => (0 : ℝ) := funext (heatDuhamel_zero f)
    have hdz : fderiv ℝ (heatDuhamel f 0) =
        fun _ : Space n => (0 : Space n →L[ℝ] ℝ) := by
      rw [hz,fderiv_fun_const]
      rfl
    simp only [hdz,fderiv_const_apply,sub_self,norm_zero]
    positivity
  by_cases hh : h = 0
  · subst h
    simp only [add_zero,sub_self,norm_zero,Real.zero_rpow hα.ne',mul_zero,le_refl]
  have hd : 0 < ‖h‖ := norm_pos_iff.mpr hh
  have hfc (s : ℝ) : Continuous (fun y : Space n => f (y,s)) :=
    hf.comp (continuous_id.prodMk continuous_const)
  have hMs (s : ℝ) (y : Space n) : |f (y,s)| ≤ M := hM (y,s)
  let A : ℝ → Space n →L[ℝ] Space n →L[ℝ] ℝ := fun s =>
    fderiv ℝ (fderiv ℝ (heatAverage (t-s) (fun y => f (y,s)))) (x+h) -
      fderiv ℝ (fderiv ℝ (heatAverage (t-s) (fun y => f (y,s)))) x
  let F : ℝ → Space n →L[ℝ] Space n →L[ℝ] ℝ := fun r =>
    fderiv ℝ (fderiv ℝ (heatAverage r (fun y => f (y,t-r)))) (x+h) -
      fderiv ℝ (fderiv ℝ (heatAverage r (fun y => f (y,t-r)))) x
  have hIplus := heatAverage_secondFDeriv_time_integrable hα hf hM hH0 hH ht (x+h)
  have hIx := heatAverage_secondFDeriv_time_integrable hα hf hM hH0 hH ht x
  have hAi : IntervalIntegrable A volume 0 t := hIplus.sub hIx
  have hFi : IntervalIntegrable F volume 0 t := by
    simpa only [F,A,sub_self,sub_zero,sub_sub_cancel] using (hAi.comp_sub_left t).symm
  have heq : fderiv ℝ (fderiv ℝ (heatDuhamel f t)) (x+h) -
        fderiv ℝ (fderiv ℝ (heatDuhamel f t)) x = ∫ r in (0 : ℝ)..t, F r := by
    rw [(heatDuhamel_fderiv_hasFDerivAt hα hf hM hH0 hH ht (x+h)).fderiv,
      (heatDuhamel_fderiv_hasFDerivAt hα hf hM hH0 hH ht x).fderiv,
      ← intervalIntegral.integral_sub hIplus hIx]
    simpa only [F,A,sub_self,sub_zero,sub_sub_cancel] using
      (intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := t) A t).symm
  have hnear (r : ℝ) (hr : r ∈ Set.Ioc 0 t) : ‖F r‖ ≤ (2*C2*H)*r^(α/2-1) := by
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ (heatAverage r (fun y => f (y,t-r)))) (x+h)‖ +
          ‖fderiv ℝ (fderiv ℝ (heatAverage r (fun y => f (y,t-r)))) x‖ := norm_sub_le _ _
      _ ≤ C2*H*r^(α/2-1)+C2*H*r^(α/2-1) :=
        add_le_add (hHess r hr.1 _ M H (hfc (t-r)) (hMs (t-r)) hH0 (hH (t-r)) (x+h))
          (hHess r hr.1 _ M H (hfc (t-r)) (hMs (t-r)) hH0 (hH (t-r)) x)
      _ = _ := by ring
  have hfar (r : ℝ) (hr : r ∈ Set.Ioc (‖h‖^2) t) :
      ‖F r‖ ≤ (C3*H)*‖h‖*r^(α/2-3/2) := by
    have hr0 : 0 < r := (sq_pos_of_pos hd).trans hr.1
    exact hInc r hr0 _ M H (hfc (t-r)) (hMs (t-r)) hH0 (hH (t-r)) x h
      (Real.le_sqrt_of_sq_le hr.1.le)
  have hb := schauder_spatial_near_far_integral_bound hα hα1
    (by positivity : 0 ≤ 2*C2*H) (by positivity : 0 ≤ C3*H) hd ht hFi hnear hfar
  rw [heq]
  convert hb using 1 <;> dsimp [C] <;> ring


theorem gaussianKernel_secondFDeriv_time_joint_smooth {n : ℕ} {t : ℝ}
    (ht : 0 < t) (x : Space n) :
    ContDiffAt ℝ ∞ (fun p : ℝ × Space n =>
      deriv (fun r : ℝ => fderiv ℝ (fderiv ℝ (gaussianKernel r)) p.2) p.1) (t,x) := by
  have hF : ContDiffAt ℝ ∞ (fun q : (ℝ × Space n) × ℝ =>
      fderiv ℝ (fderiv ℝ (gaussianKernel q.2)) q.1.2) ((t,x),t) :=
    ContDiffAt.comp (𝕜 := ℝ) (n := ∞)
      (g := fun p : ℝ × Space n => fderiv ℝ (fderiv ℝ (gaussianKernel p.1)) p.2)
      (f := fun q : (ℝ × Space n) × ℝ => (q.2,q.1.2))
      ((t,x),t) (gaussianKernel_secondFDeriv_joint_smooth ht x) (by fun_prop)
  have hh : ContDiffAt ℝ ∞ (fun p : ℝ × Space n =>
      fderiv ℝ (fun r : ℝ => fderiv ℝ (fderiv ℝ (gaussianKernel r)) p.2) p.1) (t,x) :=
    ContDiffAt.fderiv
    (f := fun p : ℝ × Space n => fun r : ℝ =>
      fderiv ℝ (fderiv ℝ (gaussianKernel r)) p.2)
    (g := Prod.fst) hF contDiffAt_fst (by simp)
  simpa only [fderiv_apply_one_eq_deriv] using hh.clm_apply (contDiffAt_const (c := (1 : ℝ)))

theorem gaussianKernel_secondFDeriv_temporal_increment_le {n : ℕ} {t δ : ℝ}
    (ht : 0 < t) (hδ : 0 ≤ δ) (y : Space n) :
    ‖fderiv ℝ (fderiv ℝ (gaussianKernel (t+δ))) y -
      fderiv ℝ (fderiv ℝ (gaussianKernel t)) y‖ ≤
      ∫ r in t..t+δ,
        ‖deriv (fun s : ℝ => fderiv ℝ (fderiv ℝ (gaussianKernel s)) y) r‖ := by
  have hle : t ≤ t+δ := le_add_of_nonneg_right hδ
  have hHc : ContinuousOn (fun r : ℝ => fderiv ℝ (fderiv ℝ (gaussianKernel r)) y)
      (Set.Icc t (t+δ)) := by
    intro r hr
    have hh : ContinuousAt (fun s : ℝ => fderiv ℝ (fderiv ℝ (gaussianKernel s)) y) r :=
      ContinuousAt.comp (f := fun s : ℝ => (s,y))
        (g := fun p : ℝ × Space n => fderiv ℝ (fderiv ℝ (gaussianKernel p.1)) p.2)
        (gaussianKernel_secondFDeriv_joint_smooth (ht.trans_le hr.1) y).continuousAt (by fun_prop)
    exact hh.continuousWithinAt
  have hDc : ContinuousOn (fun r : ℝ =>
      ‖deriv (fun s : ℝ => fderiv ℝ (fderiv ℝ (gaussianKernel s)) y) r‖)
      (Set.Icc t (t+δ)) := by
    intro r hr
    have hh : ContinuousAt (fun r : ℝ =>
        deriv (fun s : ℝ => fderiv ℝ (fderiv ℝ (gaussianKernel s)) y) r) r :=
      ContinuousAt.comp (f := fun s : ℝ => (s,y))
        (g := fun p : ℝ × Space n =>
          deriv (fun s : ℝ => fderiv ℝ (fderiv ℝ (gaussianKernel s)) p.2) p.1)
        (gaussianKernel_secondFDeriv_time_joint_smooth (ht.trans_le hr.1) y).continuousAt (by fun_prop)
    exact hh.norm.continuousWithinAt
  exact norm_sub_le_integral_of_norm_deriv_le_of_le hle hHc
    (fun r hr => (gaussianKernel_secondFDeriv_hasDerivAt (ht.trans hr.1) y).differentiableAt.differentiableWithinAt)
    (ae_of_all _ fun r _ => le_rfl) (hDc.intervalIntegrable_of_Icc hle)

theorem gaussianKernel_secondFDeriv_time_increment_weight_bound {n : ℕ} {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ∀ δ : ℝ, 0 ≤ δ →
      Integrable (fun y : Space n =>
        ‖fderiv ℝ (fderiv ℝ (gaussianKernel (t+δ))) y -
          fderiv ℝ (fderiv ℝ (gaussianKernel t)) y‖ * ‖y‖^α) ∧
      (∫ y : Space n,
        ‖fderiv ℝ (fderiv ℝ (gaussianKernel (t+δ))) y -
          fderiv ℝ (fderiv ℝ (gaussianKernel t)) y‖ * ‖y‖^α) ≤ C*δ*t^(α/2-2) := by
  obtain ⟨C,hC,hbound⟩ := gaussianKernel_secondFDeriv_time_weight_bound (n := n) hα
  refine ⟨C,hC,?_⟩
  intro t ht δ hδ
  have htδ : 0 < t+δ := add_pos_of_pos_of_nonneg ht hδ
  have hle : t ≤ t+δ := le_add_of_nonneg_right hδ
  let μ : Measure ℝ := volume.restrict (Set.Ioc t (t+δ))
  letI : IsFiniteMeasure μ := ⟨by simp [μ,Real.volume_Ioc]⟩
  let F : ℝ → Space n → ℝ := fun r y =>
    ‖deriv (fun s : ℝ => fderiv ℝ (fderiv ℝ (gaussianKernel s)) y) r‖*‖y‖^α
  have hFpos (r : ℝ) (y : Space n) : 0 ≤ F r y :=
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)
  have hFI (r : ℝ) (hr : r ∈ Set.Ioc t (t+δ)) : Integrable (F r) :=
    (hbound r (ht.trans hr.1)).1
  have hFB (r : ℝ) (hr : r ∈ Set.Ioc t (t+δ)) :
      (∫ y : Space n, F r y) ≤ C*t^(α/2-2) := by
    exact ((hbound r (ht.trans hr.1)).2).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos ht hr.1.le (by linarith)) hC.le)
  have hFc : ContinuousOn (Function.uncurry F) (Set.Ioc t (t+δ) ×ˢ Set.univ) := by
    intro p hp
    exact (((gaussianKernel_secondFDeriv_time_joint_smooth (ht.trans hp.1.1) p.2).continuousAt.norm).mul
      (((Real.continuous_rpow_const hα).comp continuous_norm).continuousAt.comp continuousAt_snd)).continuousWithinAt
  have hProd : μ.prod (volume : Measure (Space n)) =
      ((volume : Measure ℝ).prod (volume : Measure (Space n))).restrict
        (Set.Ioc t (t+δ) ×ˢ (Set.univ : Set (Space n))) := by
    simpa only [μ,Measure.restrict_univ] using
      (Measure.prod_restrict (μ := (volume : Measure ℝ))
        (ν := (volume : Measure (Space n))) (Set.Ioc t (t+δ)) Set.univ)
  have hFm : AEStronglyMeasurable (Function.uncurry F) (μ.prod volume) := by
    rw [hProd]
    exact hFc.aestronglyMeasurable (measurableSet_Ioc.prod MeasurableSet.univ)
  have hFnI : Integrable (fun r : ℝ => ∫ y : Space n, ‖F r y‖) μ := by
    apply (integrable_const (C*t^(α/2-2))).mono' hFm.norm.integral_prod_right'
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have heq : (fun y : Space n => ‖F r y‖) = F r := by
      funext y
      exact Real.norm_of_nonneg (hFpos r y)
    change ‖∫ y : Space n, ‖F r y‖‖ ≤ C*t^(α/2-2)
    rw [heq,Real.norm_of_nonneg (integral_nonneg (hFpos r))]
    exact hFB r hr
  have hprod : Integrable (Function.uncurry F) (μ.prod volume) := by
    apply (integrable_prod_iff hFm).mpr
    refine ⟨?_,hFnI⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact hFI r hr
  have hQi := hprod.integral_prod_right
  have hpoint (y : Space n) :
      ‖fderiv ℝ (fderiv ℝ (gaussianKernel (t+δ))) y -
        fderiv ℝ (fderiv ℝ (gaussianKernel t)) y‖*‖y‖^α ≤ ∫ r, F r y ∂μ := by
    have hb := mul_le_mul_of_nonneg_right
      (gaussianKernel_secondFDeriv_temporal_increment_le ht hδ y)
      (Real.rpow_nonneg (norm_nonneg y) α)
    rw [intervalIntegral.integral_of_le hle] at hb
    simpa only [μ,F,integral_mul_const] using hb
  have hHc (r : ℝ) : Continuous (fun y : Space n => fderiv ℝ (fderiv ℝ (gaussianKernel r)) y) :=
    ((gaussianKernel_spatial_smooth r).fderiv_right (m := ∞) (by simp)).continuous_fderiv (by simp)
  have hc : Continuous (fun y : Space n =>
      ‖fderiv ℝ (fderiv ℝ (gaussianKernel (t+δ))) y -
        fderiv ℝ (fderiv ℝ (gaussianKernel t)) y‖*‖y‖^α) :=
    ((hHc (t+δ)).sub (hHc t)).norm.mul ((Real.continuous_rpow_const hα).comp continuous_norm)
  have hi : Integrable (fun y : Space n =>
      ‖fderiv ℝ (fderiv ℝ (gaussianKernel (t+δ))) y -
        fderiv ℝ (fderiv ℝ (gaussianKernel t)) y‖*‖y‖^α) := by
    apply hQi.mono' hc.aestronglyMeasurable
    filter_upwards [] with y
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))]
    exact hpoint y
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ y : Space n, ∫ r, F r y ∂μ := integral_mono_ae hi hQi (ae_of_all _ hpoint)
    _ = ∫ r, (∫ y : Space n, F r y) ∂μ := (integral_integral_swap hprod).symm
    _ ≤ ∫ _r, C*t^(α/2-2) ∂μ := by
      apply integral_mono_ae hprod.integral_prod_left (integrable_const _)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact hFB r hr
    _ = C*δ*t^(α/2-2) := by
      simp only [integral_const]
      simp [μ,Measure.real,Real.volume_Ioc,ENNReal.toReal_ofReal hδ] <;> ring


theorem heatAverage_secondFDeriv_time_increment_bound {n : ℕ} {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ∀ δ : ℝ, 0 ≤ δ →
      ∀ (g : Space n → ℝ) (M H : ℝ), Continuous g → (∀ y, |g y| ≤ M) → 0 ≤ H →
      (∀ x y, |g x-g y| ≤ H*‖x-y‖^α) → ∀ x : Space n,
        ‖fderiv ℝ (fderiv ℝ (heatAverage (t+δ) g)) x -
          fderiv ℝ (fderiv ℝ (heatAverage t g)) x‖ ≤ C*H*δ*t^(α/2-2) := by
  obtain ⟨C,hC,hbound⟩ := gaussianKernel_secondFDeriv_time_increment_weight_bound (n := n) hα hα1
  refine ⟨C,hC,?_⟩
  intro t ht δ hδ g M H hg hM hH0 hH x
  have htδ : 0 < t+δ := add_pos_of_pos_of_nonneg ht hδ
  let D : ℝ → Space n → Space n →L[ℝ] Space n →L[ℝ] ℝ :=
    fun r => fderiv ℝ (fderiv ℝ (gaussianKernel r))
  let K : Space n → Space n →L[ℝ] Space n →L[ℝ] ℝ := fun y => D (t+δ) y-D t y
  have hDc (r : ℝ) : Continuous (D r) :=
    (((gaussianKernel_spatial_smooth (n := n) r).fderiv_right (m := ∞)
      (by simp)).continuous_fderiv (by simp))
  have hDi (r : ℝ) (hr : 0 < r) : Integrable (D r) := by
    apply (integrable_norm_iff (hDc r).aestronglyMeasurable).mp
    simpa only [D,Real.rpow_zero,mul_one] using
      (gaussianKernel_secondFDeriv_weight_integrable_bound (n := n) (s := 0)
        (by norm_num) hr).1
  have hKc : Continuous K := (hDc (t+δ)).sub (hDc t)
  have hKi : Integrable K := (hDi (t+δ) htδ).sub (hDi t ht)
  have hK0 : (∫ y : Space n, K y) = 0 := by
    dsimp [K,D]
    rw [integral_sub (hDi (t+δ) htδ) (hDi t ht),
      gaussianKernel_secondFDeriv_integral_zero htδ,gaussianKernel_secondFDeriv_integral_zero ht,sub_self]
  have hi (r : ℝ) (hr : 0 < r) : Integrable (fun y : Space n => g y • D r (x-y)) := by
    convert ((hDi r hr).comp_sub_left x).bdd_smul M hg.aestronglyMeasurable
      (ae_of_all _ fun y => by simpa only [Real.norm_eq_abs] using hM y) using 1
  have heq : fderiv ℝ (fderiv ℝ (heatAverage (t+δ) g)) x -
        fderiv ℝ (fderiv ℝ (heatAverage t g)) x =
      ∫ y : Space n, (g (x-y)-g x) • K y := by
    rw [heatAverage_secondFDeriv_kernel_of_bounded htδ hg hM x,
      heatAverage_secondFDeriv_kernel_of_bounded ht hg hM x]
    calc
      _ = ∫ y : Space n, g y • D (t+δ) (x-y)-g y • D t (x-y) :=
        (integral_sub (hi (t+δ) htδ) (hi t ht)).symm
      _ = ∫ y : Space n, g (x-y) • D (t+δ) (x-(x-y))-g (x-y) • D t (x-(x-y)) :=
        (integral_sub_left_eq_self
          (fun y : Space n => g y • D (t+δ) (x-y)-g y • D t (x-y)) volume x).symm
      _ = ∫ y : Space n, g (x-y) • K y := by
        congr 1
        funext y
        rw [sub_sub_cancel,← smul_sub]
      _ = _ := integral_smul_sub_const_of_zero_integral hKc hKi.norm hK0
        (hg.comp (continuous_const.sub continuous_id)) (fun y => hM (x-y)) (g x)
  rw [heq]
  calc
    _ ≤ ∫ y : Space n, H*(‖K y‖*‖y‖^α) := by
      apply norm_integral_le_of_norm_le ((hbound t ht δ hδ).1.const_mul H)
      filter_upwards [] with y
      have hy := hH (x-y) x
      have he : (x-y)-x = -y := by abel
      rw [he,norm_neg] at hy
      calc
        _ ≤ ‖g (x-y)-g x‖*‖K y‖ := ContinuousLinearMap.opNorm_smul_le _ _
        _ = |g (x-y)-g x| * ‖K y‖ := by rw [Real.norm_eq_abs]
        _ ≤ (H*‖y‖^α)*‖K y‖ := mul_le_mul_of_nonneg_right hy (K y).opNorm_nonneg
        _ = _ := by ring
    _ = H*(∫ y : Space n, ‖K y‖*‖y‖^α) := integral_const_mul _ _
    _ ≤ H*(C*δ*t^(α/2-2)) := mul_le_mul_of_nonneg_left (hbound t ht δ hδ).2 hH0
    _ = C*H*δ*t^(α/2-2) := by ring


theorem schauder_temporal_tail_weight_bound {α δ t : ℝ}
    (hα : 0 < α) (hα2 : α < 2) (hδ : 0 < δ) (hδt : δ ≤ t) :
    IntervalIntegrable (fun r : ℝ => r^(α/2-2)) volume δ t ∧
      (∫ r in δ..t, r^(α/2-2)) ≤ (2/(2-α))*δ^(α/2-1) := by
  have ht : 0 < t := hδ.trans_le hδt
  have hnot : (0 : ℝ) ∉ Set.uIcc δ t := by
    rw [Set.uIcc_of_le hδt]
    intro h
    exact (not_le_of_gt hδ) h.1
  refine ⟨intervalIntegral.intervalIntegrable_rpow (Or.inr hnot),?_⟩
  rw [integral_rpow (Or.inr ⟨(by linarith : α/2-2 ≠ -1),hnot⟩),
    show α/2-2+1 = α/2-1 by ring]
  have heq : (t^(α/2-1)-δ^(α/2-1))/(α/2-1) =
      (δ^(α/2-1)-t^(α/2-1))/((2-α)/2) := by
    rw [show α/2-1 = -((2-α)/2) by ring,div_neg,← neg_div,neg_sub]
  rw [heq]
  calc
    _ ≤ δ^(α/2-1)/((2-α)/2) :=
      div_le_div_of_nonneg_right (by linarith [Real.rpow_nonneg ht.le (α/2-1)])
        (by linarith)
    _ = (2/(2-α))*δ^(α/2-1) := by field_simp [show 2-α ≠ 0 by linarith]

theorem schauder_temporal_near_far_integral_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {α A B δ t : ℝ} {F : ℝ → E}
    (hα : 0 < α) (hα2 : α < 2) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hδ : 0 < δ) (ht : 0 < t) (hFi : IntervalIntegrable F volume 0 t)
    (hnear : ∀ r ∈ Set.Ioc 0 t, ‖F r‖ ≤ A*r^(α/2-1))
    (hfar : ∀ r ∈ Set.Ioc δ t, ‖F r‖ ≤ B*δ*r^(α/2-2)) :
    ‖∫ r in (0 : ℝ)..t, F r‖ ≤ (2*A/α+2*B/(2-α))*δ^(α/2) := by
  have hδα : 0 ≤ δ^(α/2) := Real.rpow_nonneg hδ.le _
  have hC : 0 ≤ 2*B/(2-α) := div_nonneg (by positivity) (by linarith)
  have hpowI : IntervalIntegrable (fun r : ℝ => r^(α/2-1)) volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hpowEq (s : ℝ) : (∫ r in (0 : ℝ)..s, r^(α/2-1)) = (2/α)*s^(α/2) := by
    rw [integral_rpow (Or.inl (by linarith : -1 < α/2-1)),
      show α/2-1+1 = α/2 by ring,
      Real.zero_rpow (by positivity : α/2 ≠ 0),sub_zero]
    field_simp [hα.ne']
  by_cases htδ : t ≤ δ
  · have hn := intervalIntegral.norm_integral_le_of_norm_le ht.le
      (ae_of_all _ fun r hr => hnear r hr) (hpowI.const_mul A)
    rw [intervalIntegral.integral_const_mul,hpowEq] at hn
    have htp : t^(α/2) ≤ δ^(α/2) := Real.rpow_le_rpow ht.le htδ (by positivity)
    calc
      _ ≤ A*((2/α)*t^(α/2)) := hn
      _ ≤ (2*A/α)*δ^(α/2) := by
        have hh := mul_le_mul_of_nonneg_left htp
          (show 0 ≤ A*(2/α) by positivity)
        convert hh using 1 <;> ring
      _ ≤ _ := by nlinarith [mul_nonneg hC hδα]
  · have hδt : δ < t := lt_of_not_ge htδ
    have hFnear : IntervalIntegrable F volume 0 δ := hFi.mono_set (by
      rw [Set.uIcc_of_le hδ.le,Set.uIcc_of_le ht.le]
      exact Set.Icc_subset_Icc le_rfl hδt.le)
    have hFfar : IntervalIntegrable F volume δ t := hFi.mono_set (by
      rw [Set.uIcc_of_le hδt.le,Set.uIcc_of_le ht.le]
      exact Set.Icc_subset_Icc hδ.le le_rfl)
    have hNI : IntervalIntegrable (fun r : ℝ => r^(α/2-1)) volume 0 δ :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    have hn := intervalIntegral.norm_integral_le_of_norm_le hδ.le
      (ae_of_all _ fun r hr => hnear r ⟨hr.1,hr.2.trans hδt.le⟩) (hNI.const_mul A)
    rw [intervalIntegral.integral_const_mul,hpowEq] at hn
    obtain ⟨hTI,hTB⟩ := schauder_temporal_tail_weight_bound hα hα2 hδ hδt.le
    have hb := intervalIntegral.norm_integral_le_of_norm_le hδt.le
      (ae_of_all _ fun r hr => hfar r hr) (hTI.const_mul (B*δ))
    rw [intervalIntegral.integral_const_mul] at hb
    have hδp : δ*δ^(α/2-1) = δ^(α/2) := by
      have hh := Real.rpow_add hδ 1 (α/2-1)
      simpa only [Real.rpow_one,show (1:ℝ)+(α/2-1) = α/2 by ring] using hh.symm
    have hb' : ‖∫ r in δ..t, F r‖ ≤ (2*B/(2-α))*δ^(α/2) := by
      calc
        _ ≤ (B*δ)*(∫ r in δ..t, r^(α/2-2)) := hb
        _ ≤ (B*δ)*((2/(2-α))*δ^(α/2-1)) :=
          mul_le_mul_of_nonneg_left hTB (by positivity)
        _ = (2*B/(2-α))*(δ*δ^(α/2-1)) := by ring
        _ = _ := by rw [hδp]
    rw [← intervalIntegral.integral_add_adjacent_intervals hFnear hFfar]
    calc
      _ ≤ ‖∫ r in (0 : ℝ)..δ, F r‖+‖∫ r in δ..t, F r‖ := norm_add_le _ _
      _ ≤ A*((2/α)*δ^(α/2))+(2*B/(2-α))*δ^(α/2) := add_le_add hn hb'
      _ = _ := by ring


theorem heatDuhamel_secondFDeriv_temporal_holder_bound {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : Point n → ℝ) (M H : ℝ),
      Continuous f → (∀ p, |f p| ≤ M) → 0 ≤ H →
      (∀ s x y, |f (x,s)-f (y,s)| ≤ H*‖x-y‖^α) →
      ∀ t δ : ℝ, 0 ≤ t → 0 ≤ δ → ∀ x : Space n,
        ‖fderiv ℝ (fderiv ℝ (heatDuhamel f (t+δ))) x -
          fderiv ℝ (fderiv ℝ (heatDuhamel f t)) x‖ ≤ C*H*δ^(α/2) := by
  obtain ⟨C0,hC0,hInit⟩ := heatDuhamel_secondFDeriv_bound (n := n) hα
  obtain ⟨C2,hC2,hHess⟩ := heatAverage_secondFDeriv_holder_bound (n := n) hα.le
  obtain ⟨C3,hC3,hInc⟩ := heatAverage_secondFDeriv_time_increment_bound (n := n) hα.le hα1.le
  let C : ℝ := C0+6*C2/α+2*C3/(2-α)
  have hTwo : 0 < 2-α := by linarith
  have hC : 0 < C := by dsimp [C]; positivity
  have hC0C : C0 ≤ C := by
    have h1 : 0 ≤ 6*C2/α := by positivity
    have h2 : 0 ≤ 2*C3/(2-α) := by positivity
    dsimp [C]
    linarith
  have hRestC : 6*C2/α+2*C3/(2-α) ≤ C := by dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro f M H hf hM hH0 hH t δ ht hδ x
  rcases hδ.eq_or_lt with rfl | hδ
  · simp only [add_zero,sub_self,norm_zero,Real.zero_rpow (by positivity : α/2 ≠ 0),mul_zero,le_refl]
  rcases ht.eq_or_lt with rfl | ht
  · have hz : heatDuhamel f 0 = fun _ : Space n => (0 : ℝ) := funext (heatDuhamel_zero f)
    have hdz : fderiv ℝ (heatDuhamel f 0) =
        fun _ : Space n => (0 : Space n →L[ℝ] ℝ) := by
      rw [hz,fderiv_fun_const]
      rfl
    simp only [zero_add,hdz,fderiv_const_apply,sub_zero]
    exact (hInit f M H hf hM hH0 hH δ hδ.le x).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC0C hH0)
        (Real.rpow_nonneg hδ.le _))
  have htδ : 0 < t+δ := by positivity
  have hle : t ≤ t+δ := le_add_of_nonneg_right hδ.le
  have hfc (s : ℝ) : Continuous (fun y : Space n => f (y,s)) :=
    hf.comp (continuous_id.prodMk continuous_const)
  have hMs (s : ℝ) (y : Space n) : |f (y,s)| ≤ M := hM (y,s)
  let N : ℝ → Space n →L[ℝ] Space n →L[ℝ] ℝ := fun s =>
    fderiv ℝ (fderiv ℝ (heatAverage (t+δ-s) (fun y => f (y,s)))) x
  let O : ℝ → Space n →L[ℝ] Space n →L[ℝ] ℝ := fun s =>
    fderiv ℝ (fderiv ℝ (heatAverage (t-s) (fun y => f (y,s)))) x
  let A : ℝ → Space n →L[ℝ] Space n →L[ℝ] ℝ := fun s => N s-O s
  let F : ℝ → Space n →L[ℝ] Space n →L[ℝ] ℝ := fun r =>
    fderiv ℝ (fderiv ℝ (heatAverage (r+δ) (fun y => f (y,t-r)))) x -
      fderiv ℝ (fderiv ℝ (heatAverage r (fun y => f (y,t-r)))) x
  have hNall : IntervalIntegrable N volume 0 (t+δ) :=
    heatAverage_secondFDeriv_time_integrable hα hf hM hH0 hH htδ x
  have hNt : IntervalIntegrable N volume 0 t := hNall.mono_set (by
    rw [Set.uIcc_of_le ht.le,Set.uIcc_of_le htδ.le]
    exact Set.Icc_subset_Icc le_rfl hle)
  have hNtail : IntervalIntegrable N volume t (t+δ) := hNall.mono_set (by
    rw [Set.uIcc_of_le hle,Set.uIcc_of_le htδ.le]
    exact Set.Icc_subset_Icc ht.le le_rfl)
  have hOi : IntervalIntegrable O volume 0 t :=
    heatAverage_secondFDeriv_time_integrable hα hf hM hH0 hH ht x
  have hAi : IntervalIntegrable A volume 0 t := hNt.sub hOi
  have harg (r : ℝ) : t+δ-(t-r) = r+δ := by abel
  have hFi : IntervalIntegrable F volume 0 t := by
    simpa only [F,A,N,O,sub_self,sub_zero,sub_sub_cancel,harg] using (hAi.comp_sub_left t).symm
  have hFa : (∫ r in (0 : ℝ)..t, F r) = ∫ s in (0 : ℝ)..t, A s := by
    simpa only [F,A,N,O,sub_self,sub_zero,sub_sub_cancel,harg] using
      (intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := t) A t)
  have heq : fderiv ℝ (fderiv ℝ (heatDuhamel f (t+δ))) x -
        fderiv ℝ (fderiv ℝ (heatDuhamel f t)) x =
      (∫ r in (0 : ℝ)..t, F r)+(∫ s in t..t+δ, N s) := by
    rw [(heatDuhamel_fderiv_hasFDerivAt hα hf hM hH0 hH htδ x).fderiv,
      (heatDuhamel_fderiv_hasFDerivAt hα hf hM hH0 hH ht x).fderiv]
    change (∫ s in (0 : ℝ)..t+δ, N s)-(∫ s in (0 : ℝ)..t, O s) = _
    rw [← intervalIntegral.integral_add_adjacent_intervals hNt hNtail,hFa]
    change _ = (∫ s in (0 : ℝ)..t, N s-O s)+_
    rw [intervalIntegral.integral_sub hNt hOi]
    abel
  have hnear (r : ℝ) (hr : r ∈ Set.Ioc 0 t) : ‖F r‖ ≤ (2*C2*H)*r^(α/2-1) := by
    have hp : (r+δ)^(α/2-1) ≤ r^(α/2-1) :=
      Real.rpow_le_rpow_of_nonpos hr.1 (le_add_of_nonneg_right hδ.le) (by linarith)
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ (heatAverage (r+δ) (fun y => f (y,t-r)))) x‖ +
          ‖fderiv ℝ (fderiv ℝ (heatAverage r (fun y => f (y,t-r)))) x‖ := norm_sub_le _ _
      _ ≤ C2*H*(r+δ)^(α/2-1)+C2*H*r^(α/2-1) :=
        add_le_add (hHess (r+δ) (add_pos hr.1 hδ) _ M H (hfc (t-r)) (hMs (t-r)) hH0 (hH (t-r)) x)
          (hHess r hr.1 _ M H (hfc (t-r)) (hMs (t-r)) hH0 (hH (t-r)) x)
      _ ≤ C2*H*r^(α/2-1)+C2*H*r^(α/2-1) :=
        add_le_add (mul_le_mul_of_nonneg_left hp (by positivity)) le_rfl
      _ = _ := by ring
  have hfar (r : ℝ) (hr : r ∈ Set.Ioc δ t) : ‖F r‖ ≤ (C3*H)*δ*r^(α/2-2) := by
    exact hInc r (hδ.trans hr.1) δ hδ.le _ M H (hfc (t-r)) (hMs (t-r)) hH0 (hH (t-r)) x
  have hOld := schauder_temporal_near_far_integral_bound hα (by linarith : α < 2)
    (by positivity : 0 ≤ 2*C2*H) (by positivity : 0 ≤ C3*H) hδ ht hFi hnear hfar
  have hPow : IntervalIntegrable (fun s : ℝ => (t+δ-s)^(α/2-1)) volume t (t+δ) :=
    (schauder_time_weight_integrable hα (t+δ)).mono_set (by
      rw [Set.uIcc_of_le hle,Set.uIcc_of_le htδ.le]
      exact Set.Icc_subset_Icc ht.le le_rfl)
  have hTail := intervalIntegral.norm_integral_le_of_norm_le hle
    (f := N) (g := fun s : ℝ => C2*H*(t+δ-s)^(α/2-1))
    (by
      filter_upwards [(volume : Measure ℝ).ae_ne (t+δ)] with s hst
      intro hs
      exact hHess (t+δ-s) (sub_pos.mpr (lt_of_le_of_ne hs.2 hst)) _ M H
        (hfc s) (hMs s) hH0 (hH s) x)
    (hPow.const_mul (C2*H))
  have hTailWeight : (∫ s in t..t+δ, (t+δ-s)^(α/2-1)) = (2/α)*δ^(α/2) := by
    rw [intervalIntegral.integral_comp_sub_left (fun r : ℝ => r^(α/2-1)) (t+δ)]
    simp only [sub_self,add_sub_cancel_left]
    rw [integral_rpow (Or.inl (by linarith : -1 < α/2-1)),
      show α/2-1+1 = α/2 by ring,
      Real.zero_rpow (by positivity : α/2 ≠ 0),sub_zero]
    field_simp [hα.ne']
  rw [intervalIntegral.integral_const_mul,hTailWeight] at hTail
  rw [heq]
  calc
    _ ≤ ‖∫ r in (0 : ℝ)..t, F r‖+‖∫ s in t..t+δ, N s‖ := norm_add_le _ _
    _ ≤ (6*C2/α+2*C3/(2-α))*H*δ^(α/2) := by
      convert add_le_add hOld hTail using 1 <;> ring
    _ ≤ C*H*δ^(α/2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hRestC hH0)
        (Real.rpow_nonneg hδ.le _)


theorem heatDuhamel_spatialDD_holderBound {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T F : ℝ, 0 ≤ T → T ≤ 1 → ∀ f : Point n → ℝ,
      HolderBound α (cylinder Set.univ 0 T) f F →
      HolderBound α (cylinder Set.univ 0 T)
        (spatialDD (fun p : Point n => heatDuhamel f p.2 p.1)) (C*F) := by
  obtain ⟨C0,hC0,hAbs⟩ := heatDuhamel_secondFDeriv_bound (n := n) hα
  obtain ⟨Cs,hCs,hSpace⟩ := heatDuhamel_secondFDeriv_spatial_holder_bound (n := n) hα hα1
  obtain ⟨Ct,hCt,hTime⟩ := heatDuhamel_secondFDeriv_temporal_holder_bound (n := n) hα hα1
  let C : ℝ := C0+Cs+Ct
  have hC : 0 < C := by dsimp [C]; positivity
  have hC0C : C0 ≤ C := by dsimp [C]; linarith
  have hCsC : Cs ≤ C := by dsimp [C]; linarith
  have hCtC : Ct ≤ C := by dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro T F hT hT1 f hf
  let g : Point n → ℝ := fun p => f (p.1,max 0 (min p.2 T))
  have hhat : HolderBound α Set.univ g F := holderBound_timeClamp hα.le hT hf
  have hc : Continuous g := continuousOn_univ.mp (holderBound_continuousOn hα hhat)
  have hb (p : Point n) : |g p| ≤ F := by
    simpa only [Real.norm_eq_abs] using hhat.2.1 p (Set.mem_univ _)
  have hh (s : ℝ) (x y : Space n) : |g (x,s)-g (y,s)| ≤ F*‖x-y‖^α := by
    simpa only [holderWeight,sub_self,abs_zero,
      Real.zero_rpow (by positivity : α/2 ≠ 0),add_zero,Real.norm_eq_abs] using
      hhat.2.2 (x,s) (Set.mem_univ _) (y,s) (Set.mem_univ _)
  let D : ℝ → Space n → Space n →L[ℝ] Space n →L[ℝ] ℝ :=
    fun t x => fderiv ℝ (fderiv ℝ (heatDuhamel g t)) x
  have heq (t : ℝ) (ht : t ∈ Set.Icc 0 T) : heatDuhamel g t = heatDuhamel f t :=
    funext (heatDuhamel_timeClamp f ht)
  have htime (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (x : Space n) :
      ‖D t x-D s x‖ ≤ Ct*F*|t-s|^(α/2) := by
    rcases le_total s t with hst | hts
    · have h := hTime g F F hc hb hf.1 hh s (t-s) hs (sub_nonneg.mpr hst) x
      have he : s+(t-s) = t := by ring
      rw [he] at h
      simpa only [abs_of_nonneg (sub_nonneg.mpr hst)] using h
    · have h := hTime g F F hc hb hf.1 hh t (s-t) ht (sub_nonneg.mpr hts) x
      have he : t+(s-t) = s := by ring
      rw [he] at h
      rw [norm_sub_rev,abs_sub_comm]
      simpa only [abs_of_nonneg (sub_nonneg.mpr hts)] using h
  change HolderBound α (cylinder Set.univ 0 T)
    (fun p : Point n => fderiv ℝ (fderiv ℝ (heatDuhamel f p.2)) p.1) (C*F)
  refine ⟨mul_nonneg hC.le hf.1,?_,?_⟩
  · intro p hp
    change ‖fderiv ℝ (fderiv ℝ (heatDuhamel f p.2)) p.1‖ ≤ C*F
    rw [← heq p.2 hp.2]
    have htPow : p.2^(α/2) ≤ 1 := by
      simpa only [Real.one_rpow] using
        Real.rpow_le_rpow hp.2.1 (hp.2.2.trans hT1) (by positivity : 0 ≤ α/2)
    calc
      _ ≤ C0*F*p.2^(α/2) := hAbs g F F hc hb hf.1 hh p.2 hp.2.1 p.1
      _ ≤ C0*F := by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left htPow (mul_nonneg hC0.le hf.1)
      _ ≤ C*F := mul_le_mul_of_nonneg_right hC0C hf.1
  · intro p hp q hq
    change ‖fderiv ℝ (fderiv ℝ (heatDuhamel f p.2)) p.1 -
      fderiv ℝ (fderiv ℝ (heatDuhamel f q.2)) q.1‖ ≤ C*F*holderWeight α p q
    rw [← heq p.2 hp.2,← heq q.2 hq.2]
    have hs := hSpace g F F hc hb hf.1 hh p.2 hp.2.1 q.1 (p.1-q.1)
    have he : q.1+(p.1-q.1) = p.1 := by abel
    rw [he] at hs
    calc
      _ = ‖(D p.2 p.1-D p.2 q.1)+(D p.2 q.1-D q.2 q.1)‖ := by congr 1; dsimp [D]; abel
      _ ≤ ‖D p.2 p.1-D p.2 q.1‖+‖D p.2 q.1-D q.2 q.1‖ := norm_add_le _ _
      _ ≤ Cs*F*‖p.1-q.1‖^α+Ct*F*|p.2-q.2|^(α/2) :=
        add_le_add hs (htime q.2 p.2 hq.2.1 hp.2.1 q.1)
      _ ≤ (C*F)*‖p.1-q.1‖^α+(C*F)*|p.2-q.2|^(α/2) :=
        add_le_add
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCsC hf.1)
            (Real.rpow_nonneg (norm_nonneg _) _))
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCtC hf.1)
            (Real.rpow_nonneg (abs_nonneg _) _))
      _ = C*F*holderWeight α p q := by dsimp [holderWeight]; ring

theorem heatDuhamel_spatialDD_continuousOn {n : ℕ} {α T F : ℝ} {f : Point n → ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 ≤ T) (hT1 : T ≤ 1)
    (hf : HolderBound α (cylinder Set.univ 0 T) f F) :
    ContinuousOn (spatialDD (fun p : Point n => heatDuhamel f p.2 p.1))
      (cylinder Set.univ 0 T) := by
  obtain ⟨C,hC,hbound⟩ := heatDuhamel_spatialDD_holderBound (n := n) hα hα1
  exact holderBound_continuousOn hα (hbound T F hT hT1 f hf)


theorem gaussianKernel_time_neighborhood_deriv_domination {n : ℕ} {t : ℝ} (ht : 0 < t) :
    ∃ B : Space n → ℝ, Integrable B ∧
      ∀ s ∈ Set.Icc (t/2) (2*t), ∀ y : Space n,
        |deriv (fun r : ℝ => gaussianKernel r y) s| ≤ B y := by
  let B : Space n → ℝ := fun y =>
    ((4 : ℝ)^n/t^2)*(‖y‖^2*gaussianKernel (2*t) y) +
      ((4 : ℝ)^n*(2*(n:ℝ)/t))*gaussianKernel (2*t) y
  have ht2 : 0 < 2*t := by positivity
  have h2 : Integrable (fun y : Space n => ‖y‖^2*gaussianKernel (2*t) y) := by
    simpa only [Real.rpow_two] using
      gaussianKernel_weight_integrable (n := n) (s := 2) (by norm_num) ht2
  have hBi : Integrable B :=
    (h2.const_mul _).add ((gaussianKernel_integrable ht2).const_mul _)
  refine ⟨B,hBi,?_⟩
  intro s hs y
  have hs0 : 0 < s := (half_pos ht).trans_le hs.1
  have hbase : 0 < 4*Real.pi*(t/2) := by positivity
  have hpow : (4*Real.pi*(t/2))^n ≤ (4*Real.pi*s)^n :=
    pow_le_pow_left₀ hbase.le (mul_le_mul_of_nonneg_left hs.1 (by positivity)) n
  have hcoeff : ((4*Real.pi*s)^n)⁻¹ ≤ (4:ℝ)^n*((4*Real.pi*(2*t))^n)⁻¹ := by
    have hinv := one_div_le_one_div_of_le (pow_pos hbase n) hpow
    simp only [one_div] at hinv
    calc
      _ ≤ ((4*Real.pi*(t/2))^n)⁻¹ := hinv
      _ = _ := by
        let a : ℝ := 4*Real.pi*(t/2)
        change (a^n)⁻¹ = (4:ℝ)^n*((4*Real.pi*(2*t))^n)⁻¹
        rw [show 4*Real.pi*(2*t) = (4:ℝ)*a by dsimp [a]; ring,
          show ((4:ℝ)*a)^n = (4:ℝ)^n*a^n from mul_pow _ _ _,mul_inv_rev]
        symm
        calc
          _ = ((4:ℝ)^n*((4:ℝ)^n)⁻¹)*(a^n)⁻¹ := by ring
          _ = _ := by rw [mul_inv_cancel₀ (by positivity : (4:ℝ)^n ≠ 0),one_mul]
  have harg : -‖y‖^2/(4*s) ≤ -‖y‖^2/(4*(2*t)) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 4*s) (by positivity : 0 < 4*(2*t))).mpr
    have hh := mul_nonneg (sq_nonneg ‖y‖) (sub_nonneg.mpr hs.2)
    nlinarith
  have hK : gaussianKernel s y ≤ (4:ℝ)^n*gaussianKernel (2*t) y := by
    unfold gaussianKernel
    calc
      _ ≤ ((4:ℝ)^n*((4*Real.pi*(2*t))^n)⁻¹)*Real.exp (-‖y‖^2/(4*(2*t))) :=
        mul_le_mul hcoeff (Real.exp_le_exp.mpr harg) (Real.exp_pos _).le (by positivity)
      _ = _ := by ring
  have hsq : t^2 ≤ 4*s^2 := by
    have hh : 0 ≤ 2*s-t := by linarith [hs.1]
    have hp := mul_nonneg hh (show 0 ≤ 2*s+t by positivity)
    nlinarith
  have ha : ‖y‖^2/(4*s^2) ≤ ‖y‖^2/t^2 :=
    div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos ht 2) hsq
  have hb : (n:ℝ)/s ≤ 2*(n:ℝ)/t := by
    calc
      _ ≤ (n:ℝ)/(t/2) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg n) (half_pos ht) hs.1
      _ = _ := by field_simp <;> ring
  have ha0 : 0 ≤ ‖y‖^2/(4*s^2) := by positivity
  have hb0 : 0 ≤ (n:ℝ)/s := by positivity
  have hpoly : |‖y‖^2/(4*s^2)-(n:ℝ)/s| ≤ ‖y‖^2/t^2+2*(n:ℝ)/t := by
    exact (abs_le.mpr ⟨by linarith,by linarith⟩).trans (add_le_add ha hb)
  rw [(gaussianKernel_hasDerivAt hs0 y).deriv,abs_mul,abs_of_pos (gaussianKernel_pos hs0 y)]
  have hK2 : 0 < gaussianKernel (2*t) y := gaussianKernel_pos ht2 y
  calc
    _ ≤ ((4:ℝ)^n*gaussianKernel (2*t) y)*(‖y‖^2/t^2+2*(n:ℝ)/t) :=
      mul_le_mul hK hpoly (abs_nonneg _) (by positivity)
    _ = B y := by dsimp [B]; ring

theorem heatAverage_hasDerivAt_of_bounded {n : ℕ} {t M : ℝ} {g : Space n → ℝ}
    (ht : 0 < t) (hg : Continuous g) (hM : ∀ y, |g y| ≤ M) (x : Space n) :
    HasDerivAt (fun s : ℝ => heatAverage s g x)
      (∫ y : Space n, (gaussianKernel t (x-y)*
        (‖x-y‖^2/(4*t^2)-(n:ℝ)/t))*g y) t := by
  let D : ℝ → Space n → ℝ := fun s y => gaussianKernel s (x-y)*
    (‖x-y‖^2/(4*s^2)-(n:ℝ)/s)
  obtain ⟨B,hBi,hBound⟩ := gaussianKernel_time_neighborhood_deriv_domination (n := n) ht
  have hDc (s : ℝ) : Continuous (D s) := by dsimp [D,gaussianKernel]; fun_prop
  have hKc (s : ℝ) : Continuous (fun y : Space n => gaussianKernel s (x-y)) :=
    (gaussianKernel_spatial_smooth s).continuous.comp (continuous_const.sub continuous_id)
  have hF_int : Integrable (fun y : Space n => gaussianKernel t (x-y)*g y) :=
    ((gaussianKernel_integrable ht).comp_sub_left x).mul_bdd hg.aestronglyMeasurable
      (ae_of_all _ fun y => by simpa only [Real.norm_eq_abs] using hM y)
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s (y : Space n) => gaussianKernel s (x-y)*g y)
    (F' := fun s y => D s y*g y)
    (bound := fun y => M*B (x-y)) (s := Set.Ioo (t/2) (2*t))
    (Ioo_mem_nhds (by linarith : t/2 < t) (by linarith : t < 2*t))
    (Eventually.of_forall fun s => ((hKc s).mul hg).aestronglyMeasurable)
    hF_int ((hDc t).mul hg).aestronglyMeasurable
    (ae_of_all _ fun y s hs => ?_)
    ((hBi.comp_sub_left x).const_mul M)
    (ae_of_all _ fun y s hs => ?_)
  · convert hres.2 using 1
    funext s
    exact convolution_eq_swap (ContinuousLinearMap.lsmul ℝ ℝ)
  · have hs0 : 0 < s := (half_pos ht).trans hs.1
    have hb := hBound s ⟨hs.1.le,hs.2.le⟩ (x-y)
    rw [(gaussianKernel_hasDerivAt hs0 (x-y)).deriv] at hb
    change |D s y| ≤ B (x-y) at hb
    rw [Real.norm_eq_abs,abs_mul]
    calc
      _ ≤ B (x-y)*M := mul_le_mul hb (hM y) (abs_nonneg _) ((abs_nonneg _).trans hb)
      _ = _ := mul_comm _ _
  · have hs0 : 0 < s := (half_pos ht).trans hs.1
    exact (gaussianKernel_hasDerivAt hs0 (x-y)).mul_const (g y)

theorem heatAverage_hasDerivAt_laplacian_of_bounded {n : ℕ} {t M : ℝ} {g : Space n → ℝ}
    (ht : 0 < t) (hg : Continuous g) (hM : ∀ y, |g y| ≤ M) (x : Space n) :
    HasDerivAt (fun s : ℝ => heatAverage s g x) (heatLaplacian (heatAverage t g) x) t := by
  have hHc := ((gaussianKernel_spatial_smooth (n := n) t).fderiv_right (m := ∞)
    (by simp)).continuous_fderiv (by simp)
  have hHK : Integrable (fderiv ℝ (fderiv ℝ (gaussianKernel (n := n) t))) := by
    apply (integrable_norm_iff hHc.aestronglyMeasurable).mp
    simpa only [Real.rpow_zero,mul_one] using
      (gaussianKernel_secondFDeriv_weight_integrable_bound (n := n) (s := 0)
        (by norm_num) ht).1
  have hiH : Integrable (fun y : Space n =>
      g y • fderiv ℝ (fderiv ℝ (gaussianKernel t)) (x-y)) := by
    convert (hHK.comp_sub_left x).bdd_smul M hg.aestronglyMeasurable
      (ae_of_all _ fun y => by simpa only [Real.norm_eq_abs] using hM y) using 1
  have happ (v w : Space n) : fderiv ℝ (fderiv ℝ (heatAverage t g)) x v w =
      ∫ y : Space n, g y*fderiv ℝ (fderiv ℝ (gaussianKernel t)) (x-y) v w := by
    have hiv := hiH.apply_continuousLinearMap v
    rw [heatAverage_secondFDeriv_kernel_of_bounded ht hg hM x,
      ContinuousLinearMap.integral_apply hiH v,ContinuousLinearMap.integral_apply hiv w]
    rfl
  have his (i : Yau.RIdx n) : Integrable (fun y : Space n =>
      g y*fderiv ℝ (fderiv ℝ (gaussianKernel t)) (x-y) (Yau.realVec i) (Yau.realVec i)) := by
    simpa only [ContinuousLinearMap.smul_apply,smul_eq_mul] using
      (hiH.apply_continuousLinearMap (Yau.realVec i)).apply_continuousLinearMap (Yau.realVec i)
  have heq : (∫ y : Space n, (gaussianKernel t (x-y)*
        (‖x-y‖^2/(4*t^2)-(n:ℝ)/t))*g y) = heatLaplacian (heatAverage t g) x := by
    unfold heatLaplacian
    simp_rw [happ]
    rw [← integral_finsetSum Finset.univ (fun i _ => his i)]
    apply integral_congr_ae
    filter_upwards [] with y
    have hK := gaussianKernel_time_eq_laplacian ht (x-y)
    rw [(gaussianKernel_hasDerivAt ht (x-y)).deriv] at hK
    rw [← Finset.mul_sum,← hK]
    ring
  exact (heatAverage_hasDerivAt_of_bounded ht hg hM x).congr_deriv heq


theorem heatAverage_laplacian_integral_of_holder {n : ℕ} {α M H t : ℝ}
    {g : Space n → ℝ} (hα : 0 < α) (hg : Continuous g) (hM : ∀ y, |g y| ≤ M)
    (hH0 : 0 ≤ H) (hH : ∀ x y, |g x-g y| ≤ H*‖x-y‖^α)
    (ht : 0 < t) (x : Space n) :
    IntervalIntegrable (fun r : ℝ => heatLaplacian (heatAverage r g) x) volume 0 t ∧
      (∫ r in (0 : ℝ)..t, heatLaplacian (heatAverage r g) x) = heatAverage t g x-g x := by
  have hFi : IntervalIntegrable (fun s : ℝ =>
      fderiv ℝ (fderiv ℝ (heatAverage (t-s) g)) x) volume 0 t :=
    heatAverage_secondFDeriv_time_integrable hα (hg.comp continuous_fst)
      (fun p : Point n => hM p.1) hH0 (fun s => hH) ht x
  have hHi : IntervalIntegrable (fun r : ℝ => fderiv ℝ (fderiv ℝ (heatAverage r g)) x)
      volume 0 t := by
    simpa only [sub_self,sub_zero,sub_sub_cancel] using (hFi.comp_sub_left t).symm
  have his (i : Yau.RIdx n) : IntervalIntegrable
      (fun r : ℝ => fderiv ℝ (fderiv ℝ (heatAverage r g)) x (Yau.realVec i) (Yau.realVec i))
      volume 0 t :=
    ⟨(hHi.1.apply_continuousLinearMap (Yau.realVec i)).apply_continuousLinearMap (Yau.realVec i),
      (hHi.2.apply_continuousLinearMap (Yau.realVec i)).apply_continuousLinearMap (Yau.realVec i)⟩
  have hLap : IntervalIntegrable (fun r : ℝ => heatLaplacian (heatAverage r g) x) volume 0 t := by
    have hsum := IntervalIntegrable.sum Finset.univ (fun i _ => his i)
    have heq : (∑ i : Yau.RIdx n, fun r : ℝ =>
        fderiv ℝ (fderiv ℝ (heatAverage r g)) x (Yau.realVec i) (Yau.realVec i)) =
        fun r : ℝ => heatLaplacian (heatAverage r g) x := by
      funext r
      simp only [Finset.sum_apply,heatLaplacian]
    rw [heq] at hsum
    exact hsum
  refine ⟨hLap,?_⟩
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto ht
    (fun r hr => heatAverage_hasDerivAt_laplacian_of_bounded hr.1 hg hM x) hLap
    (heatAverage_tendsto_initial_of_holder hα hg hM hH0 hH x)
    (((heatAverage_hasDerivAt_laplacian_of_bounded ht hg hM x).continuousAt.tendsto).mono_left
      nhdsWithin_le_nhds)


theorem heatLaplacian_abs_le {n : ℕ} (g : Space n → ℝ) (x : Space n) :
    |heatLaplacian g x| ≤ (Fintype.card (Yau.RIdx n) : ℝ)*‖fderiv ℝ (fderiv ℝ g) x‖ := by
  rw [← Real.norm_eq_abs,heatLaplacian]
  calc
    _ ≤ ∑ i : Yau.RIdx n, ‖fderiv ℝ (fderiv ℝ g) x (Yau.realVec i) (Yau.realVec i)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i : Yau.RIdx n, ‖fderiv ℝ (fderiv ℝ g) x‖ := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ ‖fderiv ℝ (fderiv ℝ g) x (Yau.realVec i)‖*‖Yau.realVec i‖ :=
          (fderiv ℝ (fderiv ℝ g) x (Yau.realVec i)).le_opNorm _
        _ ≤ (‖fderiv ℝ (fderiv ℝ g) x‖*‖Yau.realVec i‖)*‖Yau.realVec i‖ :=
          mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ g) x).le_opNorm _) (norm_nonneg _)
        _ = _ := by rw [realVec_norm]; ring
    _ = _ := by simp

theorem heatDuhamel_laplacian_eq_integral {n : ℕ} {α M H t : ℝ} {f : Point n → ℝ}
    (hα : 0 < α) (hf : Continuous f) (hM : ∀ p, |f p| ≤ M) (hH0 : 0 ≤ H)
    (hH : ∀ s x y, |f (x,s)-f (y,s)| ≤ H*‖x-y‖^α)
    (ht : 0 < t) (x : Space n) :
    IntervalIntegrable (fun s : ℝ => heatLaplacian (heatAverage (t-s) (fun y => f (y,s))) x)
        volume 0 t ∧
      heatLaplacian (heatDuhamel f t) x =
        ∫ s in (0 : ℝ)..t, heatLaplacian (heatAverage (t-s) (fun y => f (y,s))) x := by
  have hHi := heatAverage_secondFDeriv_time_integrable hα hf hM hH0 hH ht x
  have hvi (v : Space n) : IntervalIntegrable (fun s : ℝ =>
      (fderiv ℝ (fderiv ℝ (heatAverage (t-s) (fun y => f (y,s)))) x) v) volume 0 t :=
    ⟨hHi.1.apply_continuousLinearMap v,hHi.2.apply_continuousLinearMap v⟩
  have his (i : Yau.RIdx n) : IntervalIntegrable (fun s : ℝ =>
      fderiv ℝ (fderiv ℝ (heatAverage (t-s) (fun y => f (y,s)))) x
        (Yau.realVec i) (Yau.realVec i)) volume 0 t :=
    ⟨((hvi (Yau.realVec i)).1).apply_continuousLinearMap (Yau.realVec i),
      ((hvi (Yau.realVec i)).2).apply_continuousLinearMap (Yau.realVec i)⟩
  have hLap : IntervalIntegrable
      (fun s : ℝ => heatLaplacian (heatAverage (t-s) (fun y => f (y,s))) x) volume 0 t := by
    have hsum := IntervalIntegrable.sum Finset.univ (fun i _ => his i)
    have heq : (∑ i : Yau.RIdx n, fun s : ℝ =>
        fderiv ℝ (fderiv ℝ (heatAverage (t-s) (fun y => f (y,s)))) x
          (Yau.realVec i) (Yau.realVec i)) =
        fun s : ℝ => heatLaplacian (heatAverage (t-s) (fun y => f (y,s))) x := by
      funext s
      simp only [Finset.sum_apply,heatLaplacian]
    rw [heq] at hsum
    exact hsum
  refine ⟨hLap,?_⟩
  have happ (v w : Space n) : fderiv ℝ (fderiv ℝ (heatDuhamel f t)) x v w =
      ∫ s in (0 : ℝ)..t,
        fderiv ℝ (fderiv ℝ (heatAverage (t-s) (fun y => f (y,s)))) x v w := by
    rw [(heatDuhamel_fderiv_hasFDerivAt hα hf hM hH0 hH ht x).fderiv,
      ContinuousLinearMap.intervalIntegral_apply hHi v,
      ContinuousLinearMap.intervalIntegral_apply (hvi v) w]
  unfold heatLaplacian
  simp_rw [happ]
  rw [← intervalIntegral.integral_finsetSum (fun i _ => his i)]

theorem heatDuhamel_integrated_heat_equation {n : ℕ} {α M H t : ℝ} {f : Point n → ℝ}
    (hα : 0 < α) (hf : Continuous f) (hM : ∀ p, |f p| ≤ M) (hH0 : 0 ≤ H)
    (hH : ∀ s x y, |f (x,s)-f (y,s)| ≤ H*‖x-y‖^α)
    (ht : 0 < t) (x : Space n) :
    IntervalIntegrable (fun r : ℝ => heatLaplacian (heatDuhamel f r) x) volume 0 t ∧
      heatDuhamel f t x = (∫ s in (0 : ℝ)..t, f (x,s)) +
        ∫ r in (0 : ℝ)..t, heatLaplacian (heatDuhamel f r) x := by
  obtain ⟨C,hC,hHess⟩ := heatAverage_secondFDeriv_holder_bound (n := n) hα.le
  let μ : Measure ℝ := volume.restrict (Set.Ioo 0 t)
  letI : IsFiniteMeasure μ := ⟨by simp [μ,Real.volume_Ioo]⟩
  let B : ℝ := (Fintype.card (Yau.RIdx n) : ℝ)*C*H
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hfc (s : ℝ) : Continuous (fun y : Space n => f (y,s)) :=
    hf.comp (continuous_id.prodMk continuous_const)
  have hMs (s : ℝ) (y : Space n) : |f (y,s)| ≤ M := hM (y,s)
  let K : ℝ × ℝ → ℝ := fun p => if p.2 < p.1 then
    heatLaplacian (heatAverage (p.1-p.2) (fun y => f (y,p.2))) x else 0
  have hKm : StronglyMeasurable K := by
    let A : (ℝ × ℝ) × Space n → ℝ := fun q =>
      (gaussianKernel (q.1.1-q.1.2) (x-q.2)*
        (‖x-q.2‖^2/(4*(q.1.1-q.1.2)^2)-(n:ℝ)/(q.1.1-q.1.2)))*f (q.2,q.1.2)
    have hGm : Measurable (fun q : (ℝ × ℝ) × Space n =>
        gaussianKernel (q.1.1-q.1.2) (x-q.2)) :=
      gaussianKernel_joint_measurable.comp
        (show Measurable (fun q : (ℝ × ℝ) × Space n =>
          (q.1.1-q.1.2,x-q.2)) from by fun_prop)
    have hAm : Measurable A :=
      (hGm.mul (show Measurable (fun q : (ℝ × ℝ) × Space n =>
        ‖x-q.2‖^2/(4*(q.1.1-q.1.2)^2)-(n:ℝ)/(q.1.1-q.1.2)) from by fun_prop)).mul
        (hf.measurable.comp (show Measurable (fun q : (ℝ × ℝ) × Space n =>
          (q.2,q.1.2)) from by fun_prop))
    let I : ℝ × ℝ → ℝ := fun p => ∫ y : Space n, A (p,y)
    have hIm : StronglyMeasurable I := hAm.stronglyMeasurable.integral_prod_right'
    have heq : K = ({p : ℝ × ℝ | p.2 < p.1}).indicator I := by
      funext p
      by_cases hp : p.2 < p.1
      · simp only [K,if_pos hp,Set.indicator_of_mem (show p ∈ {q : ℝ × ℝ | q.2 < q.1} from hp)]
        exact ((heatAverage_hasDerivAt_of_bounded (sub_pos.mpr hp) (hfc p.2) (hMs p.2) x).unique
          (heatAverage_hasDerivAt_laplacian_of_bounded (sub_pos.mpr hp) (hfc p.2) (hMs p.2) x)).symm
      · simp only [K,if_neg hp,Set.indicator_of_notMem (show p ∉ {q : ℝ × ℝ | q.2 < q.1} from hp)]
    rw [heq]
    exact hIm.indicator (measurableSet_lt measurable_snd measurable_fst)
  have hRightSet (s : ℝ) (hs : s ∈ Set.Ioo 0 t) :
      Set.Ioi s ∩ Set.Ioo (0 : ℝ) t = Set.Ioo s t := by
    ext r
    simp only [Set.mem_inter_iff,Set.mem_Ioi,Set.mem_Ioo]
    constructor
    · intro h
      exact ⟨h.1,h.2.2⟩
    · intro h
      exact ⟨h.1,hs.1.trans h.1,h.2⟩
  have hLeftSet (r : ℝ) (hr : r ∈ Set.Ioo 0 t) :
      Set.Iio r ∩ Set.Ioo (0 : ℝ) t = Set.Ioo 0 r := by
    ext s
    simp only [Set.mem_inter_iff,Set.mem_Iio,Set.mem_Ioo]
    constructor
    · intro h
      exact ⟨h.2.1,h.1⟩
    · intro h
      exact ⟨h.2,h.1,h.2.trans hr.2⟩
  have hright (s : ℝ) (hs : s ∈ Set.Ioo 0 t) (L : ℝ → ℝ) :
      (∫ r, (Set.Ioi s).indicator L r ∂μ) = ∫ r in s..t, L r := by
    rw [integral_indicator measurableSet_Ioi]
    change (∫ r, L r ∂((volume.restrict (Set.Ioo 0 t)).restrict (Set.Ioi s))) = _
    rw [Measure.restrict_restrict measurableSet_Ioi,hRightSet s hs,
      ← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le hs.2.le]
  have hleft (r : ℝ) (hr : r ∈ Set.Ioo 0 t) (L : ℝ → ℝ) :
      (∫ s, (Set.Iio r).indicator L s ∂μ) = ∫ s in (0 : ℝ)..r, L s := by
    rw [integral_indicator measurableSet_Iio]
    change (∫ s, L s ∂((volume.restrict (Set.Ioo 0 t)).restrict (Set.Iio r))) = _
    rw [Measure.restrict_restrict measurableSet_Iio,hLeftSet r hr,
      ← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le hr.1.le]
  have hFTC (s : ℝ) (hs : s ∈ Set.Ioo 0 t) :=
    heatAverage_laplacian_integral_of_holder hα (hfc s) (hMs s) hH0 (hH s) (sub_pos.mpr hs.2) x
  have hRI (s : ℝ) (hs : s ∈ Set.Ioo 0 t) : IntervalIntegrable
      (fun r : ℝ => heatLaplacian (heatAverage (r-s) (fun y => f (y,s))) x) volume s t := by
    simpa only [zero_add,sub_add_cancel] using ((hFTC s hs).1.comp_sub_right s)
  have hKri (s : ℝ) (hs : s ∈ Set.Ioo 0 t) : Integrable (fun r : ℝ => K (r,s)) μ := by
    have heq : (fun r : ℝ => K (r,s)) = (Set.Ioi s).indicator
        (fun r : ℝ => heatLaplacian (heatAverage (r-s) (fun y => f (y,s))) x) := by
      funext r
      rfl
    rw [heq,integrable_indicator_iff measurableSet_Ioi]
    change Integrable _ ((volume.restrict (Set.Ioo 0 t)).restrict (Set.Ioi s))
    rw [Measure.restrict_restrict measurableSet_Ioi,hRightSet s hs]
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hs.2.le).mp (hRI s hs)
  have hKnB (s : ℝ) (hs : s ∈ Set.Ioo 0 t) :
      (∫ r, ‖K (r,s)‖ ∂μ) ≤ B*(2/α)*t^(α/2) := by
    have heq : (fun r : ℝ => ‖K (r,s)‖) = (Set.Ioi s).indicator
        (fun r : ℝ => |heatLaplacian (heatAverage (r-s) (fun y => f (y,s))) x|) := by
      funext r
      by_cases hsr : s < r
      · simp only [K,if_pos hsr,Set.indicator_of_mem (show r ∈ Set.Ioi s from hsr),Real.norm_eq_abs]
      · simp only [K,if_neg hsr,Set.indicator_of_notMem (show r ∉ Set.Ioi s from hsr),norm_zero]
    rw [heq,hright s hs]
    have hPow : IntervalIntegrable (fun r : ℝ => (r-s)^(α/2-1)) volume s t := by
      simpa only [zero_add,sub_add_cancel] using
        (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := t-s)
          (by linarith : -1 < α/2-1)).comp_sub_right s
    calc
      _ ≤ ∫ r in s..t, B*(r-s)^(α/2-1) := by
        apply intervalIntegral.integral_mono_on_of_le_Ioo hs.2.le (hRI s hs).abs (hPow.const_mul B)
        intro r hr
        calc
          _ ≤ (Fintype.card (Yau.RIdx n) : ℝ)*
              ‖fderiv ℝ (fderiv ℝ (heatAverage (r-s) (fun y => f (y,s)))) x‖ := heatLaplacian_abs_le _ _
          _ ≤ (Fintype.card (Yau.RIdx n) : ℝ)*(C*H*(r-s)^(α/2-1)) :=
            mul_le_mul_of_nonneg_left
              (hHess (r-s) (sub_pos.mpr hr.1) _ M H (hfc s) (hMs s) hH0 (hH s) x)
              (Nat.cast_nonneg _)
          _ = _ := by dsimp [B]; ring
      _ = B*(2/α)*(t-s)^(α/2) := by
        rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_sub_right
          (fun u : ℝ => u^(α/2-1)) s,sub_self]
        rw [integral_rpow (Or.inl (by linarith : -1 < α/2-1)),
          show α/2-1+1 = α/2 by ring,
          Real.zero_rpow (by positivity : α/2 ≠ 0),sub_zero]
        field_simp [hα.ne'] <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (sub_pos.mpr hs.2).le (sub_le_self t hs.1.le) (by positivity))
        (by positivity)
  have hFnI : Integrable (fun s : ℝ => ∫ r, ‖K (r,s)‖ ∂μ) μ := by
    apply (integrable_const (B*(2/α)*t^(α/2))).mono'
      hKm.norm.integral_prod_left'.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    rw [Real.norm_of_nonneg (integral_nonneg (fun r => norm_nonneg (K (r,s))))]
    exact hKnB s hs
  have hprod : Integrable K (μ.prod μ) := by
    apply (integrable_prod_iff' hKm.aestronglyMeasurable).mpr
    refine ⟨?_,hFnI⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact hKri s hs
  have hKL (r : ℝ) (hr : r ∈ Set.Ioo 0 t) :
      heatLaplacian (heatDuhamel f r) x = ∫ s, K (r,s) ∂μ := by
    rw [(heatDuhamel_laplacian_eq_integral hα hf hM hH0 hH hr.1 x).2]
    exact (hleft r hr (fun s : ℝ =>
      heatLaplacian (heatAverage (r-s) (fun y => f (y,s))) x)).symm
  have hKR (s : ℝ) (hs : s ∈ Set.Ioo 0 t) :
      (∫ r, K (r,s) ∂μ) = heatAverage (t-s) (fun y => f (y,s)) x-f (x,s) := by
    change (∫ r, (Set.Ioi s).indicator
      (fun r : ℝ => heatLaplacian (heatAverage (r-s) (fun y => f (y,s))) x) r ∂μ) = _
    rw [hright s hs,intervalIntegral.integral_comp_sub_right
      (fun u : ℝ => heatLaplacian (heatAverage u (fun y => f (y,s))) x) s,sub_self]
    exact (hFTC s hs).2
  have hLapIO : Integrable (fun r : ℝ => heatLaplacian (heatDuhamel f r) x) μ := by
    apply hprod.integral_prod_left.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact (hKL r hr).symm
  have hDouble : (∫ r, heatLaplacian (heatDuhamel f r) x ∂μ) =
      ∫ s, (heatAverage (t-s) (fun y => f (y,s)) x-f (x,s)) ∂μ := by
    calc
      _ = ∫ r, (∫ s, K (r,s) ∂μ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
        exact hKL r hr
      _ = ∫ s, (∫ r, K (r,s) ∂μ) ∂μ := integral_integral_swap hprod
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
        exact hKR s hs
  have hAvgIO : Integrable (fun s : ℝ => heatAverage (t-s) (fun y => f (y,s)) x) μ :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp
      (heatDuhamel_integrable_and_bound hf hM ht.le x).1
  have hFIO : Integrable (fun s : ℝ => f (x,s)) μ :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp
      ((hf.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 t)
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mpr hLapIO,?_⟩
  have hEq : (∫ r in (0 : ℝ)..t, heatLaplacian (heatDuhamel f r) x) =
      heatDuhamel f t x-(∫ s in (0 : ℝ)..t, f (x,s)) := by
    rw [intervalIntegral.integral_of_le ht.le,integral_Ioc_eq_integral_Ioo]
    change (∫ r, heatLaplacian (heatDuhamel f r) x ∂μ) = _
    rw [hDouble,integral_sub hAvgIO hFIO]
    rw [heatDuhamel,intervalIntegral.integral_of_le ht.le,integral_Ioc_eq_integral_Ioo,
      intervalIntegral.integral_of_le ht.le,integral_Ioc_eq_integral_Ioo]
  linarith


theorem heatDuhamel_laplacian_continuousOn {n : ℕ} {α T F : ℝ} {f : Point n → ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 ≤ T) (hT1 : T ≤ 1)
    (hf : HolderBound α (cylinder Set.univ 0 T) f F) :
    ContinuousOn (fun p : Point n => heatLaplacian (heatDuhamel f p.2) p.1)
      (cylinder Set.univ 0 T) := by
  have hD := heatDuhamel_spatialDD_continuousOn hα hα1 hT hT1 hf
  change ContinuousOn (fun p : Point n =>
    fderiv ℝ (fderiv ℝ (heatDuhamel f p.2)) p.1) (cylinder Set.univ 0 T) at hD
  change ContinuousOn (fun p : Point n => ∑ i : Yau.RIdx n,
    fderiv ℝ (fderiv ℝ (heatDuhamel f p.2)) p.1 (Yau.realVec i) (Yau.realVec i)) _
  exact continuousOn_finsetSum Finset.univ (fun i _ =>
    (hD.clm_apply continuousOn_const).clm_apply continuousOn_const)

theorem heatDuhamel_hasDerivWithinAt_of_holder {n : ℕ} {α T F t : ℝ} {f : Point n → ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (hf : HolderBound α (cylinder Set.univ 0 T) f F) (ht : t ∈ Set.Icc 0 T) (x : Space n) :
    HasDerivWithinAt (fun r : ℝ => heatDuhamel f r x)
      (f (x,t)+heatLaplacian (heatDuhamel f t) x) (Set.Icc 0 T) t := by
  let g : Point n → ℝ := fun p => f (p.1,max 0 (min p.2 T))
  have hhat : HolderBound α Set.univ g F := holderBound_timeClamp hα.le hT.le hf
  have hhatQ : HolderBound α (cylinder Set.univ 0 T) g F :=
    ⟨hhat.1,fun p _ => hhat.2.1 p (Set.mem_univ _),
      fun p _ q _ => hhat.2.2 p (Set.mem_univ _) q (Set.mem_univ _)⟩
  have hc : Continuous g := continuousOn_univ.mp (holderBound_continuousOn hα hhat)
  have hb (p : Point n) : |g p| ≤ F := by
    simpa only [Real.norm_eq_abs] using hhat.2.1 p (Set.mem_univ _)
  have hh (s : ℝ) (y z : Space n) : |g (y,s)-g (z,s)| ≤ F*‖y-z‖^α := by
    simpa only [holderWeight,sub_self,abs_zero,
      Real.zero_rpow (by positivity : α/2 ≠ 0),add_zero,Real.norm_eq_abs] using
      hhat.2.2 (y,s) (Set.mem_univ _) (z,s) (Set.mem_univ _)
  have hLap := heatDuhamel_laplacian_continuousOn hα hα1 hT.le hT1 hhatQ
  have hLtime : ContinuousOn (fun r : ℝ => heatLaplacian (heatDuhamel g r) x) (Set.Icc 0 T) :=
    hLap.comp (f := fun r : ℝ => (x,r))
      (show ContinuousOn (fun r : ℝ => (x,r)) (Set.Icc 0 T) from
        (continuous_const.prodMk continuous_id).continuousOn)
      (fun r hr => ⟨Set.mem_univ _,hr⟩)
  let A : ℝ → ℝ := fun r => g (x,r)+heatLaplacian (heatDuhamel g r) x
  have hAc : ContinuousOn A (Set.Icc 0 T) :=
    (hc.comp (continuous_const.prodMk continuous_id)).continuousOn.add hLtime
  have hEq (r : ℝ) (hr : r ∈ Set.Icc 0 T) :
      heatDuhamel g r x = ∫ s in (0 : ℝ)..r, A s := by
    rcases hr.1.eq_or_lt with rfl | hr0
    · simp [heatDuhamel]
    have hE := heatDuhamel_integrated_heat_equation hα hc hb hf.1 hh hr0 x
    change _ = ∫ s in (0 : ℝ)..r, g (x,s)+heatLaplacian (heatDuhamel g s) x
    have hgi : IntervalIntegrable (fun s : ℝ => g (x,s)) volume 0 r :=
      (hc.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 r
    rw [intervalIntegral.integral_add hgi hE.1]
    exact hE.2
  have hAi : IntervalIntegrable A volume 0 t :=
    (hAc.mono (Set.Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
  letI : Fact (t ∈ Set.Icc 0 T) := ⟨ht⟩
  have hd := intervalIntegral.integral_hasDerivWithinAt_right hAi
    (s := Set.Icc 0 T) (t := Set.Icc 0 T)
    (hAc.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hAc t ht)
  have hdu : HasDerivWithinAt (fun r : ℝ => heatDuhamel g r x)
      (g (x,t)+heatLaplacian (heatDuhamel g t) x) (Set.Icc 0 T) t :=
    hd.congr_of_mem hEq ht
  have hgx : g (x,t) = f (x,t) :=
    timeClamp_eqOn T f (show (x,t) ∈ cylinder Set.univ 0 T from ⟨Set.mem_univ _,ht⟩)
  have hSlice : heatDuhamel g t = heatDuhamel f t := funext (heatDuhamel_timeClamp f ht)
  rw [hgx,hSlice] at hdu
  exact hdu.congr_of_mem (fun r hr => (heatDuhamel_timeClamp f hr x).symm) ht

theorem heatDuhamel_timeD_eq {n : ℕ} {α T F t : ℝ} {f : Point n → ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (hf : HolderBound α (cylinder Set.univ 0 T) f F) (ht : t ∈ Set.Icc 0 T) (x : Space n) :
    timeD (cylinder Set.univ 0 T) (fun p : Point n => heatDuhamel f p.2 p.1) (x,t) =
      f (x,t)+heatLaplacian (heatDuhamel f t) x := by
  change derivWithin (fun r : ℝ => heatDuhamel f r x)
    {r | (x,r) ∈ cylinder Set.univ 0 T} t = _
  have hset : {r : ℝ | (x,r) ∈ cylinder Set.univ 0 T} = Set.Icc 0 T := by
    ext r
    simp only [Set.mem_setOf_eq,Yau.Parabolic.cylinder,Set.mem_prod,Set.mem_univ,true_and]
  rw [hset]
  exact (heatDuhamel_hasDerivWithinAt_of_holder hα hα1 hT hT1 hf ht x).derivWithin
    (uniqueDiffOn_Icc hT t ht)

theorem heatDuhamel_euclidean_linearOp {n : ℕ} {α T F : ℝ} {f : Point n → ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (hf : HolderBound α (cylinder Set.univ 0 T) f F) (p : Point n)
    (hp : p ∈ cylinder Set.univ 0 T) :
    linearOp (cylinder Set.univ 0 T) (fun _ => (1 : Mat n)) (fun _ _ => 0)
      (fun p : Point n => heatDuhamel f p.2 p.1) p = f p := by
  rcases p with ⟨x,t⟩
  unfold linearOp
  rw [heatDuhamel_timeD_eq hα hα1 hT hT1 hf hp.2 x]
  simp [Matrix.one_apply,spatialDD,heatLaplacian]


theorem heatDuhamel_spatial_contDiffAt_two {n : ℕ} {α T F t : ℝ} {f : Point n → ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 ≤ T) (hT1 : T ≤ 1)
    (hf : HolderBound α (cylinder Set.univ 0 T) f F) (ht : t ∈ Set.Icc 0 T) (x : Space n) :
    ContDiffAt ℝ 2 (heatDuhamel f t) x := by
  rcases ht.1.eq_or_lt with rfl | ht0
  · have hz : heatDuhamel f 0 = fun _ : Space n => (0 : ℝ) := funext (heatDuhamel_zero f)
    rw [hz]
    exact contDiffAt_const
  let g : Point n → ℝ := fun p => f (p.1,max 0 (min p.2 T))
  have hhat : HolderBound α Set.univ g F := holderBound_timeClamp hα.le hT hf
  have hhatQ : HolderBound α (cylinder Set.univ 0 T) g F :=
    ⟨hhat.1,fun p _ => hhat.2.1 p (Set.mem_univ _),
      fun p _ q _ => hhat.2.2 p (Set.mem_univ _) q (Set.mem_univ _)⟩
  have hc : Continuous g := continuousOn_univ.mp (holderBound_continuousOn hα hhat)
  have hb (p : Point n) : |g p| ≤ F := by
    simpa only [Real.norm_eq_abs] using hhat.2.1 p (Set.mem_univ _)
  have hh (s : ℝ) (y z : Space n) : |g (y,s)-g (z,s)| ≤ F*‖y-z‖^α := by
    simpa only [holderWeight,sub_self,abs_zero,
      Real.zero_rpow (by positivity : α/2 ≠ 0),add_zero,Real.norm_eq_abs] using
      hhat.2.2 (y,s) (Set.mem_univ _) (z,s) (Set.mem_univ _)
  have hSlice : heatDuhamel g t = heatDuhamel f t := funext (heatDuhamel_timeClamp f ht)
  rw [← hSlice]
  have hD2 := heatDuhamel_spatialDD_continuousOn hα hα1 hT hT1 hhatQ
  change ContinuousOn (fun p : Point n =>
    fderiv ℝ (fderiv ℝ (heatDuhamel g p.2)) p.1) (cylinder Set.univ 0 T) at hD2
  have hHs : Continuous (fderiv ℝ (fderiv ℝ (heatDuhamel g t))) := by
    apply continuousOn_univ.mp
    exact hD2.comp (f := fun y : Space n => (y,t))
      (show ContinuousOn (fun y : Space n => (y,t)) Set.univ from
        (continuous_id.prodMk continuous_const).continuousOn)
      (fun y _ => ⟨Set.mem_univ _,ht⟩)
  have hd (y : Space n) : HasFDerivAt (heatDuhamel g t) (fderiv ℝ (heatDuhamel g t) y) y :=
    (heatDuhamel_hasFDerivAt hc hb ht0 y).differentiableAt.hasFDerivAt
  have hd2 (y : Space n) : HasFDerivAt (fderiv ℝ (heatDuhamel g t))
      (fderiv ℝ (fderiv ℝ (heatDuhamel g t)) y) y :=
    (heatDuhamel_fderiv_hasFDerivAt hα hc hb hf.1 hh ht0 y).differentiableAt.hasFDerivAt
  have hGrad : ContDiffAt ℝ 1 (fderiv ℝ (heatDuhamel g t)) x :=
    contDiffAt_one_iff.mpr ⟨fderiv ℝ (fderiv ℝ (heatDuhamel g t)),Set.univ,univ_mem,
      hHs.continuousOn,fun y _ => hd2 y⟩
  exact (contDiffAt_succ_iff_hasFDerivAt (n := 1)).mpr
    ⟨fderiv ℝ (heatDuhamel g t),⟨Set.univ,univ_mem,fun y _ => hd y⟩,hGrad⟩


theorem heatAverage_first_jet_holder_bound {n : ℕ} {α : ℝ} (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : Point n → ℝ) (F : ℝ), HolderBound α Set.univ f F →
      ∀ r : ℝ, 0 < r → r ≤ 1 →
        (∀ p : Point n, ‖(heatAverage r (fun y => f (y,p.2)) p.1,
          fderiv ℝ (heatAverage r (fun y => f (y,p.2))) p.1)‖ ≤ C*F*r^(-(1/2:ℝ))) ∧
        ∀ p q : Point n,
          ‖(heatAverage r (fun y => f (y,p.2)) p.1,
              fderiv ℝ (heatAverage r (fun y => f (y,p.2))) p.1) -
            (heatAverage r (fun y => f (y,q.2)) q.1,
              fderiv ℝ (heatAverage r (fun y => f (y,q.2))) q.1)‖ ≤
                C*F*r^(-(1/2:ℝ))*holderWeight α p q := by
  obtain ⟨C0,hC0,hGrad⟩ := heatAverage_fderiv_bound_of_bounded (n := n)
  let C : ℝ := C0+1
  have hC : 0 < C := by dsimp [C]; positivity
  have h1C : 1 ≤ C := by dsimp [C]; linarith
  have hC0C : C0 ≤ C := by dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro f F hf r hr hr1
  have hF0 : 0 ≤ F := hf.1
  have hc : Continuous f := continuousOn_univ.mp (holderBound_continuousOn hα hf)
  have hfc (s : ℝ) : Continuous (fun y : Space n => f (y,s)) :=
    hc.comp (continuous_id.prodMk continuous_const)
  have hb (p : Point n) : |f p| ≤ F := by
    simpa only [Real.norm_eq_abs] using hf.2.1 p (Set.mem_univ _)
  have hrPow : 1 ≤ r^(-(1/2:ℝ)) := by
    simpa only [Real.one_rpow] using
      Real.rpow_le_rpow_of_nonpos hr hr1 (by norm_num : -(1/2:ℝ) ≤ 0)
  have hFbound : F ≤ C*F*r^(-(1/2:ℝ)) := by
    calc
      _ = (1:ℝ)*F*1 := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right h1C hf.1) hrPow (by positivity) (by positivity)
  have hiD := gaussianKernel_fderiv_integrable (n := n) hr
  have hiP (p : Point n) : Integrable (fun y : Space n =>
      f (y+p.1,p.2) • fderiv ℝ (gaussianKernel r) (-y)) := by
    have hsc : Continuous (fun y : Space n => f (y+p.1,p.2)) :=
      (hfc p.2).comp (continuous_id.add continuous_const)
    have hi := (hiD.comp_neg).bdd_smul F hsc.aestronglyMeasurable
      (ae_of_all _ fun y => by simpa only [Real.norm_eq_abs] using hb (y+p.1,p.2))
    convert hi using 1
  have hGRep (p : Point n) : fderiv ℝ (heatAverage r (fun y => f (y,p.2))) p.1 =
      ∫ y : Space n, f (y+p.1,p.2) • fderiv ℝ (gaussianKernel r) (-y) := by
    rw [(heatAverage_hasFDerivAt_kernel_of_bounded hr (hfc p.2) (fun y => hb (y,p.2)) p.1).fderiv]
    calc
      _ = ∫ y : Space n, f (y+p.1,p.2) • fderiv ℝ (gaussianKernel r) (p.1-(y+p.1)) :=
        (integral_add_right_eq_self (fun y : Space n =>
          f (y,p.2) • fderiv ℝ (gaussianKernel r) (p.1-y)) p.1).symm
      _ = _ := by
        congr 1
        funext y
        rw [show p.1-(y+p.1) = -y by abel]
  constructor
  · intro p
    change max |heatAverage r (fun y => f (y,p.2)) p.1|
      ‖fderiv ℝ (heatAverage r (fun y => f (y,p.2))) p.1‖ ≤ _
    apply max_le
    · exact (heatAverage_bound hr (hfc p.2) (fun y => hb (y,p.2)) p.1).trans hFbound
    · exact (hGrad r hr _ F (hfc p.2) (fun y => hb (y,p.2)) p.1).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC0C hf.1)
          (Real.rpow_nonneg hr.le _))
  · intro p q
    let h : Space n → ℝ := fun y => f (y+p.1,p.2)-f (y+q.1,q.2)
    have hhc : Continuous h :=
      ((hfc p.2).comp (continuous_id.add continuous_const)).sub
        ((hfc q.2).comp (continuous_id.add continuous_const))
    have hW0 : 0 ≤ holderWeight α p q := by dsimp [holderWeight]; positivity
    have hhb (y : Space n) : |h y| ≤ F*holderWeight α p q := by
      have hh := hf.2.2 (y+p.1,p.2) (Set.mem_univ _) (y+q.1,q.2) (Set.mem_univ _)
      have he : (y+p.1)-(y+q.1) = p.1-q.1 := by abel
      simpa only [h,holderWeight,he,Real.norm_eq_abs] using hh
    have hEq0 : heatAverage r (fun y => f (y,p.2)) p.1 -
        heatAverage r (fun y => f (y,q.2)) q.1 = heatAverage r h 0 := by
      rw [heatAverage_def,heatAverage_def,heatAverage_def,
        ← integral_sub
          (heatAverage_integrable_of_bounded hr (hfc p.2) (fun y => hb (y,p.2)) p.1)
          (heatAverage_integrable_of_bounded hr (hfc q.2) (fun y => hb (y,q.2)) q.1)]
      congr 1
      funext y
      dsimp [h]
      rw [zero_sub,show p.1-y = -y+p.1 by abel,show q.1-y = -y+q.1 by abel]
      ring
    have hEq1 : fderiv ℝ (heatAverage r (fun y => f (y,p.2))) p.1 -
        fderiv ℝ (heatAverage r (fun y => f (y,q.2))) q.1 = fderiv ℝ (heatAverage r h) 0 := by
      rw [hGRep p,hGRep q,← integral_sub (hiP p) (hiP q),
        (heatAverage_hasFDerivAt_kernel_of_bounded hr hhc hhb 0).fderiv]
      congr 1
      funext y
      rw [zero_sub]
      exact (sub_smul _ _ _).symm
    change max |heatAverage r (fun y => f (y,p.2)) p.1 -
        heatAverage r (fun y => f (y,q.2)) q.1|
      ‖fderiv ℝ (heatAverage r (fun y => f (y,p.2))) p.1 -
        fderiv ℝ (heatAverage r (fun y => f (y,q.2))) q.1‖ ≤ _
    apply max_le
    · rw [hEq0]
      exact (heatAverage_bound hr hhc hhb 0).trans
        (mul_le_mul_of_nonneg_right hFbound hW0)
    · rw [hEq1]
      have hh := hGrad r hr h (F*holderWeight α p q) hhc hhb 0
      calc
        _ ≤ C0*(F*holderWeight α p q)*r^(-(1/2:ℝ)) := hh
        _ = (C0*F*r^(-(1/2:ℝ)))*holderWeight α p q := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC0C hf.1)
            (Real.rpow_nonneg hr.le _)) hW0


theorem heatAverage_fderiv_time_integrable {n : ℕ} {M t : ℝ} {f : Point n → ℝ}
    (hf : Continuous f) (hM : ∀ p, |f p| ≤ M) (ht : 0 < t) (x : Space n) :
    IntervalIntegrable (fun s : ℝ => fderiv ℝ (heatAverage (t-s) (fun y => f (y,s))) x)
      volume 0 t := by
  obtain ⟨C,hC,hGrad⟩ := heatAverage_fderiv_bound_of_bounded (n := n)
  let μ : Measure ℝ := volume.restrict (Set.Ioo 0 t)
  letI : IsFiniteMeasure μ := ⟨by simp [μ,Real.volume_Ioo]⟩
  have hfc (s : ℝ) : Continuous (fun y : Space n => f (y,s)) :=
    hf.comp (continuous_id.prodMk continuous_const)
  have hMs (s : ℝ) (y : Space n) : |f (y,s)| ≤ M := hM (y,s)
  let J : ℝ × Space n → Space n →L[ℝ] ℝ := fun p =>
    f (p.2,p.1) • fderiv ℝ (gaussianKernel (t-p.1)) (x-p.2)
  have hJC : ContinuousOn J (Set.Ioo 0 t ×ˢ Set.univ) := by
    intro p hp
    have hKC : ContinuousAt (fun q : ℝ × Space n =>
        fderiv ℝ (gaussianKernel (t-q.1)) (x-q.2)) p :=
      ContinuousAt.comp
        (f := fun q : ℝ × Space n => (t-q.1,x-q.2))
        (g := fun q : ℝ × Space n => fderiv ℝ (gaussianKernel q.1) q.2)
        (gaussianKernel_fderiv_joint_smooth (sub_pos.mpr hp.1.2) (x-p.2)).continuousAt
        (by fun_prop)
    have hsc : Continuous (fun q : ℝ × Space n => f (q.2,q.1)) :=
      hf.comp (show Continuous (fun q : ℝ × Space n => (q.2,q.1)) from by fun_prop)
    exact (hsc.continuousAt.smul hKC).continuousWithinAt
  have hProd : μ.prod (volume : Measure (Space n)) =
      ((volume : Measure ℝ).prod (volume : Measure (Space n))).restrict
        (Set.Ioo 0 t ×ˢ (Set.univ : Set (Space n))) := by
    simpa only [μ,Measure.restrict_univ] using
      (Measure.prod_restrict (μ := (volume : Measure ℝ))
        (ν := (volume : Measure (Space n))) (Set.Ioo 0 t) Set.univ)
  have hJm : AEStronglyMeasurable J (μ.prod volume) := by
    rw [hProd]
    exact hJC.aestronglyMeasurable (measurableSet_Ioo.prod MeasurableSet.univ)
  have hGm : AEStronglyMeasurable
      (fun s : ℝ => fderiv ℝ (heatAverage (t-s) (fun y => f (y,s))) x) μ := by
    apply hJm.integral_prod_right'.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact (heatAverage_hasFDerivAt_kernel_of_bounded (sub_pos.mpr hs.2)
      (hfc s) (hMs s) x).fderiv.symm
  have hPow : IntervalIntegrable (fun s : ℝ => (t-s)^(-(1/2:ℝ))) volume 0 t := by
    simpa only [show (1:ℝ)/2-1 = -(1/2:ℝ) by ring] using
      schauder_time_weight_integrable (α := 1) (by norm_num) t
  have hBI : Integrable (fun s : ℝ => C*M*(t-s)^(-(1/2:ℝ))) μ :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp (hPow.const_mul (C*M))
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mpr
  apply hBI.mono' hGm
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  exact hGrad (t-s) (sub_pos.mpr hs.2) (fun y => f (y,s)) M (hfc s) (hMs s) x

theorem heatDuhamel_first_jet_integral {n : ℕ} {M t : ℝ} {f : Point n → ℝ}
    (hf : Continuous f) (hM : ∀ p, |f p| ≤ M) (ht : 0 < t) (x : Space n) :
    IntervalIntegrable (fun r : ℝ =>
      (heatAverage r (fun y => f (y,t-r)) x,fderiv ℝ (heatAverage r (fun y => f (y,t-r))) x))
        volume 0 t ∧
      (heatDuhamel f t x,fderiv ℝ (heatDuhamel f t) x) =
        ∫ r in (0 : ℝ)..t,
          (heatAverage r (fun y => f (y,t-r)) x,fderiv ℝ (heatAverage r (fun y => f (y,t-r))) x) := by
  have hUi := (heatDuhamel_integrable_and_bound hf hM ht.le x).1
  have hGi := heatAverage_fderiv_time_integrable hf hM ht x
  have hJi : IntervalIntegrable (fun s : ℝ =>
      (heatAverage (t-s) (fun y => f (y,s)) x,
        fderiv ℝ (heatAverage (t-s) (fun y => f (y,s))) x)) volume 0 t :=
    ⟨hUi.1.prodMk hGi.1,hUi.2.prodMk hGi.2⟩
  have hJri : IntervalIntegrable (fun r : ℝ =>
      (heatAverage r (fun y => f (y,t-r)) x,fderiv ℝ (heatAverage r (fun y => f (y,t-r))) x))
        volume 0 t := by
    simpa only [sub_self,sub_zero,sub_sub_cancel] using (hJi.comp_sub_left t).symm
  refine ⟨hJri,?_⟩
  calc
    _ = ∫ s in (0 : ℝ)..t,
        (heatAverage (t-s) (fun y => f (y,s)) x,
          fderiv ℝ (heatAverage (t-s) (fun y => f (y,s))) x) := by
      rw [(heatDuhamel_hasFDerivAt hf hM ht x).fderiv,heatDuhamel]
      simp only [intervalIntegral.integral_of_le ht.le,integral_pair hUi.1 hGi.1]
    _ = _ := by
      simpa only [sub_self,sub_zero,sub_sub_cancel] using
        (intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := t)
          (fun s : ℝ => (heatAverage (t-s) (fun y => f (y,s)) x,
            fderiv ℝ (heatAverage (t-s) (fun y => f (y,s))) x)) t).symm


theorem heatDuhamel_first_jet_holderBound_global {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T F : ℝ, 0 < T → T ≤ 1 → ∀ f : Point n → ℝ,
      HolderBound α Set.univ f F →
      HolderBound α (cylinder Set.univ 0 T)
        (fun p : Point n => (heatDuhamel f p.2 p.1,fderiv ℝ (heatDuhamel f p.2) p.1))
        (C*F*(T^(1/2:ℝ)+T^((1-α)/2))) := by
  obtain ⟨C0,hC0,hOp⟩ := heatAverage_first_jet_holder_bound (n := n) hα
  refine ⟨2*C0,by positivity,?_⟩
  intro T F hT hT1 f hf
  have hF0 : 0 ≤ F := hf.1
  have hc : Continuous f := continuousOn_univ.mp (holderBound_continuousOn hα hf)
  have hb (p : Point n) : |f p| ≤ F := by
    simpa only [Real.norm_eq_abs] using hf.2.1 p (Set.mem_univ _)
  let J : ℝ → Point n → ℝ × (Space n →L[ℝ] ℝ) := fun r p =>
    (heatAverage r (fun y => f (y,p.2)) p.1,fderiv ℝ (heatAverage r (fun y => f (y,p.2))) p.1)
  let U : Point n → ℝ × (Space n →L[ℝ] ℝ) := fun p =>
    (heatDuhamel f p.2 p.1,fderiv ℝ (heatDuhamel f p.2) p.1)
  have hRep (s : ℝ) (hs : 0 ≤ s) (x : Space n) :
      IntervalIntegrable (fun r : ℝ => J r (x,s-r)) volume 0 s ∧
        U (x,s) = ∫ r in (0 : ℝ)..s, J r (x,s-r) := by
    rcases hs.eq_or_lt with rfl | hs
    · have hz : heatDuhamel f 0 = fun _ : Space n => (0 : ℝ) := funext (heatDuhamel_zero f)
      constructor
      · simp
      · simp [U,hz,heatDuhamel_zero]
    · exact heatDuhamel_first_jet_integral hc hb hs x
  have hPowI (s : ℝ) : IntervalIntegrable (fun r : ℝ => r^(-(1/2:ℝ))) volume 0 s :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hPowEq (s : ℝ) : (∫ r in (0 : ℝ)..s, r^(-(1/2:ℝ))) = 2*s^(1/2:ℝ) := by
    rw [integral_rpow (Or.inl (by norm_num : -1 < -(1/2:ℝ))),
      show -(1/2:ℝ)+1 = (1/2:ℝ) by ring,Real.zero_rpow (by norm_num : (1/2:ℝ) ≠ 0),sub_zero]
    field_simp
  have hAbs (s : ℝ) (hs : 0 ≤ s) (hsT : s ≤ T) (x : Space n) :
      ‖U (x,s)‖ ≤ 2*C0*F*s^(1/2:ℝ) := by
    rw [(hRep s hs x).2]
    have hn := intervalIntegral.norm_integral_le_of_norm_le hs
      (f := fun r : ℝ => J r (x,s-r))
      (g := fun r : ℝ => C0*F*r^(-(1/2:ℝ)))
      (ae_of_all _ fun r hr => (hOp f F hf r hr.1 (hr.2.trans (hsT.trans hT1))).1 (x,s-r))
      ((hPowI s).const_mul (C0*F))
    rw [intervalIntegral.integral_const_mul,hPowEq] at hn
    convert hn using 1 <;> ring
  have hLow (d : ℝ) (hd : 0 ≤ d) (hdT : d ≤ T) :
      d^(1/2:ℝ) ≤ T^((1-α)/2)*d^(α/2) := by
    have heq : d^(1/2:ℝ) = d^(α/2)*d^((1-α)/2) := by
      rw [← Real.rpow_add_of_nonneg hd (by positivity : 0 ≤ α/2) (by linarith : 0 ≤ (1-α)/2)]
      congr 1
      ring
    rw [heq]
    have hh := Real.rpow_le_rpow hd hdT (by linarith : 0 ≤ (1-α)/2)
    calc
      _ ≤ d^(α/2)*T^((1-α)/2) := mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hd _)
      _ = _ := mul_comm _ _
  have hDiff (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) (x y : Space n) :
      ‖U (x,t)-U (y,s)‖ ≤ (2*C0)*F*(T^(1/2:ℝ)+T^((1-α)/2))*
        (‖x-y‖^α+|t-s|^(α/2)) := by
    have ht : 0 ≤ t := hs.trans hst
    let A : ℝ → ℝ × (Space n →L[ℝ] ℝ) := fun r => J r (x,t-r)
    let B : ℝ → ℝ × (Space n →L[ℝ] ℝ) := fun r => J r (y,s-r)
    let W : ℝ := ‖x-y‖^α+|t-s|^(α/2)
    have hW0 : 0 ≤ W := by dsimp [W]; positivity
    have hAi : IntervalIntegrable A volume 0 t := (hRep t ht x).1
    have hBi : IntervalIntegrable B volume 0 s := (hRep s hs y).1
    have hApre : IntervalIntegrable A volume 0 s := hAi.mono_set (by
      rw [Set.uIcc_of_le hs,Set.uIcc_of_le ht]
      exact Set.Icc_subset_Icc le_rfl hst)
    have hAtail : IntervalIntegrable A volume s t := hAi.mono_set (by
      rw [Set.uIcc_of_le hst,Set.uIcc_of_le ht]
      exact Set.Icc_subset_Icc hs le_rfl)
    have hEq : U (x,t)-U (y,s) =
        (∫ r in (0 : ℝ)..s, A r-B r)+(∫ r in s..t, A r) := by
      rw [(hRep t ht x).2,(hRep s hs y).2]
      change (∫ r in (0 : ℝ)..t, A r)-(∫ r in (0 : ℝ)..s, B r) = _
      rw [← intervalIntegral.integral_add_adjacent_intervals hApre hAtail,
        intervalIntegral.integral_sub hApre hBi]
      abel
    have hPre := intervalIntegral.norm_integral_le_of_norm_le hs
      (f := fun r : ℝ => A r-B r) (g := fun r : ℝ => C0*F*r^(-(1/2:ℝ))*W)
      (by
        filter_upwards [] with r
        intro hr
        have hh := (hOp f F hf r hr.1 (hr.2.trans (hst.trans (htT.trans hT1)))).2 (x,t-r) (y,s-r)
        have he : (t-r)-(s-r) = t-s := by ring
        simpa only [A,B,J,W,holderWeight,he] using hh)
      (((hPowI s).const_mul (C0*F)).mul_const W)
    rw [intervalIntegral.integral_mul_const,intervalIntegral.integral_const_mul,hPowEq] at hPre
    have hPre' : ‖∫ r in (0 : ℝ)..s, A r-B r‖ ≤ 2*C0*F*T^(1/2:ℝ)*W := by
      calc
        _ ≤ (C0*F*(2*s^(1/2:ℝ)))*W := hPre
        _ ≤ (C0*F*(2*T^(1/2:ℝ)))*W := by
          apply mul_le_mul_of_nonneg_right _ hW0
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow hs (hst.trans htT) (by norm_num : 0 ≤ (1/2:ℝ))) (by norm_num)
        _ = _ := by ring
    have hTI : IntervalIntegrable (fun r : ℝ => (r-s)^(-(1/2:ℝ))) volume s t := by
      simpa only [zero_add,sub_add_cancel] using (hPowI (t-s)).comp_sub_right s
    have hTail := intervalIntegral.norm_integral_le_of_norm_le hst
      (f := A) (g := fun r : ℝ => C0*F*(r-s)^(-(1/2:ℝ)))
      (by
        filter_upwards [] with r
        intro hr
        have hh := (hOp f F hf r (hs.trans_lt hr.1) (hr.2.trans (htT.trans hT1))).1 (x,t-r)
        exact hh.trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (sub_pos.mpr hr.1) (sub_le_self r hs) (by norm_num))
          (by positivity)))
      (hTI.const_mul (C0*F))
    rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_sub_right
      (fun u : ℝ => u^(-(1/2:ℝ))) s,sub_self,hPowEq] at hTail
    have hTail' : ‖∫ r in s..t, A r‖ ≤ 2*C0*F*T^((1-α)/2)*W := by
      have hδ0 : 0 ≤ t-s := sub_nonneg.mpr hst
      have hδT : t-s ≤ T := (sub_le_self t hs).trans htT
      calc
        _ ≤ C0*F*(2*(t-s)^(1/2:ℝ)) := hTail
        _ ≤ C0*F*(2*(T^((1-α)/2)*(t-s)^(α/2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hLow (t-s) hδ0 hδT) (by norm_num))
            (by positivity)
        _ = 2*C0*F*T^((1-α)/2)*|t-s|^(α/2) := by rw [abs_of_nonneg hδ0]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (by dsimp [W]; exact le_add_of_nonneg_left (Real.rpow_nonneg (norm_nonneg (x-y)) α))
          (by positivity)
    rw [hEq]
    calc
      _ ≤ ‖∫ r in (0 : ℝ)..s, A r-B r‖+‖∫ r in s..t, A r‖ := norm_add_le _ _
      _ ≤ 2*C0*F*T^(1/2:ℝ)*W+2*C0*F*T^((1-α)/2)*W := add_le_add hPre' hTail'
      _ = _ := by dsimp [W]; ring
  change HolderBound α (cylinder Set.univ 0 T) U _
  refine ⟨by positivity,?_,?_⟩
  · intro p hp
    calc
      _ ≤ 2*C0*F*p.2^(1/2:ℝ) := hAbs p.2 hp.2.1 hp.2.2 p.1
      _ ≤ 2*C0*F*T^(1/2:ℝ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hp.2.1 hp.2.2 (by norm_num : 0 ≤ (1/2:ℝ))) (by positivity)
      _ ≤ _ := by
        have hh := mul_nonneg (show 0 ≤ 2*C0*F by positivity) (Real.rpow_nonneg hT.le ((1-α)/2))
        nlinarith
  · intro p hp q hq
    rcases le_total q.2 p.2 with hqp | hpq
    · exact hDiff q.2 p.2 hq.2.1 hqp hp.2.2 p.1 q.1
    · rw [norm_sub_rev]
      have hh := hDiff p.2 q.2 hp.2.1 hpq hq.2.2 q.1 p.1
      simpa only [holderWeight,norm_sub_rev,abs_sub_comm] using hh

theorem heatDuhamel_first_jet_holderBound {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T F : ℝ, 0 < T → T ≤ 1 → ∀ f : Point n → ℝ,
      HolderBound α (cylinder Set.univ 0 T) f F →
      HolderBound α (cylinder Set.univ 0 T)
        (fun p : Point n => (heatDuhamel f p.2 p.1,
          spatialD (fun p : Point n => heatDuhamel f p.2 p.1) p))
        (C*F*(T^(1/2:ℝ)+T^((1-α)/2))) := by
  obtain ⟨C,hC,hbound⟩ := heatDuhamel_first_jet_holderBound_global (n := n) hα hα1
  refine ⟨C,hC,?_⟩
  intro T F hT hT1 f hf
  let g : Point n → ℝ := fun p => f (p.1,max 0 (min p.2 T))
  have hhat : HolderBound α Set.univ g F := holderBound_timeClamp hα.le hT.le hf
  have hB := hbound T F hT hT1 g hhat
  have hSlice (t : ℝ) (ht : t ∈ Set.Icc 0 T) : heatDuhamel g t = heatDuhamel f t :=
    funext (heatDuhamel_timeClamp f ht)
  refine ⟨hB.1,?_,?_⟩
  · intro p hp
    change ‖(heatDuhamel f p.2 p.1,fderiv ℝ (heatDuhamel f p.2) p.1)‖ ≤ _
    rw [← hSlice p.2 hp.2]
    exact hB.2.1 p hp
  · intro p hp q hq
    change ‖(heatDuhamel f p.2 p.1,fderiv ℝ (heatDuhamel f p.2) p.1) -
      (heatDuhamel f q.2 q.1,fderiv ℝ (heatDuhamel f q.2) q.1)‖ ≤ _
    rw [← hSlice p.2 hp.2,← hSlice q.2 hq.2]
    exact hB.2.2 p hp q hq

theorem heatDuhamel_low_spatial_jets_continuousOn {n : ℕ} {α T F : ℝ} {f : Point n → ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (hf : HolderBound α (cylinder Set.univ 0 T) f F) :
    ContinuousOn (fun p : Point n => heatDuhamel f p.2 p.1) (cylinder Set.univ 0 T) ∧
      ContinuousOn (spatialD (fun p : Point n => heatDuhamel f p.2 p.1)) (cylinder Set.univ 0 T) := by
  obtain ⟨C,hC,hbound⟩ := heatDuhamel_first_jet_holderBound (n := n) hα hα1
  have hc := holderBound_continuousOn hα (hbound T F hT hT1 f hf)
  exact ⟨hc.fst,hc.snd⟩


theorem heatDuhamel_C2 {n : ℕ} {α T F : ℝ} {f : Point n → ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (hf : HolderBound α (cylinder Set.univ 0 T) f F) :
    C2 (cylinder Set.univ 0 T) (fun p : Point n => heatDuhamel f p.2 p.1) := by
  obtain ⟨hu,hDu⟩ := heatDuhamel_low_spatial_jets_continuousOn hα hα1 hT hT1 hf
  have hTime : ContinuousOn
      (timeD (cylinder Set.univ 0 T) (fun p : Point n => heatDuhamel f p.2 p.1))
      (cylinder Set.univ 0 T) := by
    apply ((holderBound_continuousOn hα hf).add
      (heatDuhamel_laplacian_continuousOn hα hα1 hT.le hT1 hf)).congr
    intro p hp
    rcases p with ⟨x,t⟩
    exact heatDuhamel_timeD_eq hα hα1 hT hT1 hf hp.2 x
  refine ⟨hu,hDu,heatDuhamel_spatialDD_continuousOn hα hα1 hT.le hT1 hf,hTime,?_,?_⟩
  · intro p hp
    exact heatDuhamel_spatial_contDiffAt_two hα hα1 hT.le hT1 hf hp.2 p.1
  · intro p hp
    change DifferentiableWithinAt ℝ (fun r : ℝ => heatDuhamel f r p.1)
      {r | (p.1,r) ∈ cylinder Set.univ 0 T} p.2
    have hset : {r : ℝ | (p.1,r) ∈ cylinder Set.univ 0 T} = Set.Icc 0 T := by
      ext r
      simp only [Set.mem_setOf_eq,Yau.Parabolic.cylinder,Set.mem_prod,Set.mem_univ,true_and]
    rw [hset]
    exact (heatDuhamel_hasDerivWithinAt_of_holder hα hα1 hT hT1 hf hp.2 p.1).differentiableWithinAt


def heatTrace {n : ℕ} : (Space n →L[ℝ] Space n →L[ℝ] ℝ) →L[ℝ] ℝ :=
  ∑ i : Yau.RIdx n, (ContinuousLinearMap.apply ℝ ℝ (Yau.realVec i)).comp
    (ContinuousLinearMap.apply ℝ (Space n →L[ℝ] ℝ) (Yau.realVec i))

theorem heatTrace_apply {n : ℕ} (A : Space n →L[ℝ] Space n →L[ℝ] ℝ) :
    heatTrace A = ∑ i : Yau.RIdx n, A (Yau.realVec i) (Yau.realVec i) := by
  simp [heatTrace]

theorem heatTrace_abs_le {n : ℕ} (A : Space n →L[ℝ] Space n →L[ℝ] ℝ) :
    |heatTrace A| ≤ (Fintype.card (Yau.RIdx n) : ℝ)*‖A‖ := by
  rw [heatTrace_apply,← Real.norm_eq_abs]
  calc
    _ ≤ ∑ i : Yau.RIdx n, ‖A (Yau.realVec i) (Yau.realVec i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Yau.RIdx n, ‖A‖ := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ ‖A (Yau.realVec i)‖*‖Yau.realVec i‖ := (A (Yau.realVec i)).le_opNorm _
        _ ≤ (‖A‖*‖Yau.realVec i‖)*‖Yau.realVec i‖ :=
          mul_le_mul_of_nonneg_right (A.le_opNorm _) (norm_nonneg _)
        _ = _ := by rw [realVec_norm]; ring
    _ = _ := by simp

theorem heatLaplacian_eq_heatTrace {n : ℕ} (g : Space n → ℝ) (x : Space n) :
    heatLaplacian g x = heatTrace (fderiv ℝ (fderiv ℝ g) x) := by
  rw [heatTrace_apply] <;> rfl

theorem heatDuhamel_timeD_holderBound {n : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T F : ℝ, 0 < T → T ≤ 1 → ∀ f : Point n → ℝ,
      HolderBound α (cylinder Set.univ 0 T) f F →
      HolderBound α (cylinder Set.univ 0 T)
        (timeD (cylinder Set.univ 0 T) (fun p : Point n => heatDuhamel f p.2 p.1)) (C*F) := by
  obtain ⟨C0,hC0,hHess⟩ := heatDuhamel_spatialDD_holderBound (n := n) hα hα1
  let m : ℝ := Fintype.card (Yau.RIdx n)
  have hm : 0 ≤ m := Nat.cast_nonneg _
  let C : ℝ := 1+m*C0
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro T F hT hT1 f hf
  have hF0 : 0 ≤ F := hf.1
  have hDD := hHess T F hT.le hT1 f hf
  let D : Point n → Space n →L[ℝ] Space n →L[ℝ] ℝ :=
    spatialDD (fun p : Point n => heatDuhamel f p.2 p.1)
  have hEq (p : Point n) (hp : p ∈ cylinder Set.univ 0 T) :
      timeD (cylinder Set.univ 0 T) (fun p : Point n => heatDuhamel f p.2 p.1) p =
        f p+heatTrace (D p) := by
    rcases p with ⟨x,t⟩
    rw [heatDuhamel_timeD_eq hα hα1 hT hT1 hf hp.2 x,heatLaplacian_eq_heatTrace] <;> rfl
  refine ⟨mul_nonneg hC.le hF0,?_,?_⟩
  · intro p hp
    rw [Real.norm_eq_abs,hEq p hp]
    calc
      _ ≤ |f p|+|heatTrace (D p)| := abs_add_le _ _
      _ ≤ F+m*(C0*F) := add_le_add
        (by simpa only [Real.norm_eq_abs] using hf.2.1 p hp)
        ((heatTrace_abs_le (D p)).trans (mul_le_mul_of_nonneg_left (hDD.2.1 p hp) hm))
      _ = C*F := by dsimp [C]; ring
  · intro p hp q hq
    rw [Real.norm_eq_abs,hEq p hp,hEq q hq]
    have heq : (f p+heatTrace (D p))-(f q+heatTrace (D q)) =
        (f p-f q)+heatTrace (D p-D q) := by rw [map_sub]; ring
    rw [heq]
    calc
      _ ≤ |f p-f q|+|heatTrace (D p-D q)| := abs_add_le _ _
      _ ≤ F*holderWeight α p q+m*((C0*F)*holderWeight α p q) :=
        add_le_add (by simpa only [Real.norm_eq_abs] using hf.2.2 p hp q hq)
          ((heatTrace_abs_le (D p-D q)).trans
            (mul_le_mul_of_nonneg_left (hDD.2.2 p hp q hq) hm))
      _ = C*F*holderWeight α p q := by dsimp [C]; ring

theorem heatDuhamel_schauder_solution {n : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T F : ℝ, 0 < T → T ≤ 1 → ∀ f : Point n → ℝ,
      HolderBound α (cylinder Set.univ 0 T) f F →
      SchauderBound α (cylinder Set.univ 0 T) (fun p : Point n => heatDuhamel f p.2 p.1) (C*F) ∧
        (∀ x : Space n, heatDuhamel f 0 x = 0) ∧
        ∀ p ∈ cylinder Set.univ 0 T,
          linearOp (cylinder Set.univ 0 T) (fun _ => (1 : Mat n)) (fun _ _ => 0)
            (fun p : Point n => heatDuhamel f p.2 p.1) p = f p := by
  obtain ⟨Cd,hCd,hD⟩ := heatDuhamel_derivative_bounds_of_holder (n := n) hα
  obtain ⟨Ch,hCh,hH⟩ := heatDuhamel_spatialDD_holderBound (n := n) hα hα1
  obtain ⟨Ct,hCt,hT⟩ := heatDuhamel_timeD_holderBound (n := n) hα hα1
  let C : ℝ := 1+Cd+Ch+Ct
  have hC : 0 < C := by dsimp [C]; positivity
  have h1C : 1 ≤ C := by dsimp [C]; linarith
  have hCdC : Cd ≤ C := by dsimp [C]; linarith
  have hChC : Ch ≤ C := by dsimp [C]; linarith
  have hCtC : Ct ≤ C := by dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro T F hT0 hT1 f hf
  have hF0 : 0 ≤ F := hf.1
  have hmono {E : Type} [NormedAddCommGroup E] {g : Point n → E} {A B : ℝ}
      (hg : HolderBound α (cylinder Set.univ 0 T) g A) (hAB : A ≤ B) :
      HolderBound α (cylinder Set.univ 0 T) g B := by
    refine ⟨hg.1.trans hAB,fun p hp => (hg.2.1 p hp).trans hAB,?_⟩
    intro p hp q hq
    exact (hg.2.2 p hp q hq).trans (mul_le_mul_of_nonneg_right hAB
      (by dsimp [holderWeight]; positivity))
  refine ⟨⟨heatDuhamel_C2 hα hα1 hT0 hT1 hf,mul_nonneg hC.le hF0,?_,
    hmono (hH T F hT0.le hT1 f hf) (mul_le_mul_of_nonneg_right hChC hF0),
    hmono (hT T F hT0 hT1 f hf) (mul_le_mul_of_nonneg_right hCtC hF0)⟩,
    heatDuhamel_zero f,fun p hp => heatDuhamel_euclidean_linearOp hα hα1 hT0 hT1 hf p hp⟩
  intro p hp
  constructor
  · exact (heatDuhamel_bound_of_holder hα hT0.le hf hp.2 p.1).trans
      ((mul_le_mul_of_nonneg_right (hp.2.2.trans hT1) hF0).trans
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right h1C hF0))
  · change ‖fderiv ℝ (heatDuhamel f p.2) p.1‖ ≤ C*F
    have htPow : p.2^(1/2:ℝ) ≤ 1 := by
      simpa only [Real.one_rpow] using Real.rpow_le_rpow hp.2.1
        (hp.2.2.trans hT1) (by norm_num : 0 ≤ (1/2:ℝ))
    exact ((hD T F hT0.le f hf p.2 hp.2 p.1).1.trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left htPow (by positivity : 0 ≤ Cd*F))).trans
        (mul_le_mul_of_nonneg_right hCdC hF0)


def spaceRealBasis (n : ℕ) : OrthonormalBasis (Yau.RIdx n) ℝ (Space n) :=
  (Pi.orthonormalBasis fun _ : Fin n => Complex.orthonormalBasisOneI).reindex
    (Equiv.sigmaEquivProd (Fin n) (Fin 2))

theorem spaceRealBasis_apply (n : ℕ) (a : Yau.RIdx n) : spaceRealBasis n a = Yau.realVec a := by
  rcases a with ⟨i,j⟩
  fin_cases j <;> ext l <;>
    simp [spaceRealBasis,OrthonormalBasis.reindex_apply,Pi.orthonormalBasis_apply,
      Complex.coe_orthonormalBasisOneI,Yau.realVec,EuclideanSpace.single,PiLp.single_apply,smul_eq_mul]

theorem realVec_inner {n : ℕ} (i j : Yau.RIdx n) :
    inner ℝ (Yau.realVec i) (Yau.realVec j) = if i = j then 1 else 0 := by
  simpa only [spaceRealBasis_apply] using (orthonormal_iff_ite.mp (spaceRealBasis n).orthonormal) i j

def realCoordLinear {n : ℕ} (i : Yau.RIdx n) : Space n →L[ℝ] ℝ := innerSL ℝ (Yau.realVec i)

theorem realCoordLinear_apply {n : ℕ} (i : Yau.RIdx n) (x : Space n) :
    realCoordLinear i x = Yau.realCoord x i := by
  change inner ℝ (Yau.realVec i) x = _
  rw [real_inner_comm,real_inner_realVec]

def matrixSpaceOperator {n : ℕ} (A : Mat n) : Space n →L[ℝ] Space n :=
  ∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n,
    A i j • (realCoordLinear j).smulRight (Yau.realVec i)

theorem matrixSpaceOperator_apply {n : ℕ} (A : Mat n) (x : Space n) :
    matrixSpaceOperator A x = ∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n,
      (A i j*Yau.realCoord x j) • Yau.realVec i := by
  simp [matrixSpaceOperator,realCoordLinear_apply,smul_smul]

theorem realCoord_matrixSpaceOperator {n : ℕ} (A : Mat n) (x : Space n) (i : Yau.RIdx n) :
    Yau.realCoord (matrixSpaceOperator A x) i = ∑ j : Yau.RIdx n, A i j*Yau.realCoord x j := by
  rw [← real_inner_realVec,matrixSpaceOperator_apply]
  simp [sum_inner,real_inner_smul_left,realVec_inner]

theorem matrixSpaceOperator_norm_sq {n : ℕ} (A : Mat n) (x : Space n) :
    ‖matrixSpaceOperator A x‖^2 = ∑ i : Yau.RIdx n, (∑ j : Yau.RIdx n,
      A i j*Yau.realCoord x j)^2 := by
  rw [← sum_realCoord_sq]
  simp only [realCoord_matrixSpaceOperator]

open scoped MatrixOrder in
theorem posSemidef_symmetric_square {n : ℕ} {A : Mat n} (hA : A.PosSemidef) :
    ∃ S : Mat n, S.IsSymm ∧ A = S*S := by
  refine ⟨CFC.sqrt A,?_,?_⟩
  · exact (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian.isSymm
  · rw [← sq]
    exact (CFC.sq_sqrt A hA.nonneg).symm

theorem matrixSpaceOperator_gram_norm_sq {n : ℕ} (S : Mat n) (x : Space n) :
    ‖matrixSpaceOperator S x‖^2 = ∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n,
      (S.transpose*S) i j*Yau.realCoord x i*Yau.realCoord x j := by
  rw [matrixSpaceOperator_norm_sq]
  calc
    _ = ∑ k : Yau.RIdx n, ∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n,
        S k i*S k j*Yau.realCoord x i*Yau.realCoord x j := by
      apply Finset.sum_congr rfl
      intro k _
      rw [pow_two,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ i : Yau.RIdx n, ∑ k : Yau.RIdx n, ∑ j : Yau.RIdx n,
        S k i*S k j*Yau.realCoord x i*Yau.realCoord x j := Finset.sum_comm
    _ = ∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n, ∑ k : Yau.RIdx n,
        S k i*S k j*Yau.realCoord x i*Yau.realCoord x j := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := by simp only [Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul]

theorem matrixSpaceOperator_gram_bounds {n : ℕ} {lam upper : ℝ} {A S : Mat n}
    (hAS : A = S.transpose*S)
    (hA : ∀ v : Yau.RIdx n → ℝ,
      lam*(∑ i, (v i)^2) ≤ ∑ i, ∑ j, A i j*v i*v j ∧
        (∑ i, ∑ j, A i j*v i*v j) ≤ upper*(∑ i, (v i)^2)) (x : Space n) :
    lam*‖x‖^2 ≤ ‖matrixSpaceOperator S x‖^2 ∧
      ‖matrixSpaceOperator S x‖^2 ≤ upper*‖x‖^2 := by
  rw [matrixSpaceOperator_gram_norm_sq,← hAS]
  simpa only [sum_realCoord_sq] using hA (Yau.realCoord x)

theorem matrixSpaceOperator_injective_of_lower_bound {n : ℕ} {lam : ℝ} {S : Mat n}
    (hLam : 0 < lam) (hLower : ∀ x : Space n, lam*‖x‖^2 ≤ ‖matrixSpaceOperator S x‖^2) :
    Function.Injective (matrixSpaceOperator S) := by
  intro x y hxy
  have hmap : matrixSpaceOperator S (x-y) = 0 := by rw [map_sub,hxy,sub_self]
  have hle := hLower (x-y)
  rw [hmap,norm_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hle
  have hsq : ‖x-y‖^2 ≤ 0 := (mul_le_mul_iff_right₀ hLam).mp (by simpa only [mul_zero] using hle)
  have hn : ‖x-y‖ = 0 := sq_eq_zero_iff.mp (le_antisymm hsq (sq_nonneg _))
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

def matrixSpaceEquivOfLowerBound {n : ℕ} {lam : ℝ} (S : Mat n)
    (hLam : 0 < lam) (hLower : ∀ x : Space n, lam*‖x‖^2 ≤ ‖matrixSpaceOperator S x‖^2) :
    Space n ≃L[ℝ] Space n := by
  have hinj : Function.Injective (matrixSpaceOperator S).toLinearMap :=
    matrixSpaceOperator_injective_of_lower_bound hLam hLower
  exact (LinearEquiv.ofBijective (matrixSpaceOperator S).toLinearMap
    ⟨hinj,LinearMap.surjective_of_injective hinj⟩).toContinuousLinearEquiv

theorem matrixSpaceEquivOfLowerBound_apply {n : ℕ} {lam : ℝ} (S : Mat n)
    (hLam : 0 < lam) (hLower : ∀ x : Space n, lam*‖x‖^2 ≤ ‖matrixSpaceOperator S x‖^2)
    (x : Space n) : matrixSpaceEquivOfLowerBound S hLam hLower x = matrixSpaceOperator S x := rfl

theorem matrixSpaceEquivOfLowerBound_norm_bounds {n : ℕ} {lam upper : ℝ} (S : Mat n)
    (hLam : 0 < lam) (hLamUpper : lam ≤ upper)
    (hLower : ∀ x : Space n, lam*‖x‖^2 ≤ ‖matrixSpaceOperator S x‖^2)
    (hUpper : ∀ x : Space n, ‖matrixSpaceOperator S x‖^2 ≤ upper*‖x‖^2) :
    ‖(matrixSpaceEquivOfLowerBound S hLam hLower : Space n →L[ℝ] Space n)‖ ≤ Real.sqrt upper ∧
      ‖((matrixSpaceEquivOfLowerBound S hLam hLower).symm : Space n →L[ℝ] Space n)‖ ≤
        (Real.sqrt lam)⁻¹ := by
  let B : Space n ≃L[ℝ] Space n := matrixSpaceEquivOfLowerBound S hLam hLower
  have hUpper0 : 0 ≤ upper := (hLam.trans_le hLamUpper).le
  have hUN (x : Space n) : ‖matrixSpaceOperator S x‖ ≤ Real.sqrt upper*‖x‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow,Real.sq_sqrt hUpper0]
    exact hUpper x
  have hLN (x : Space n) : Real.sqrt lam*‖x‖ ≤ ‖matrixSpaceOperator S x‖ := by
    apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) (norm_nonneg _)).mp
    rw [mul_pow,Real.sq_sqrt hLam.le]
    exact hLower x
  constructor
  · apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg upper)
    intro x
    exact hUN x
  · apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr (Real.sqrt_nonneg lam))
    intro x
    change ‖B.symm x‖ ≤ (Real.sqrt lam)⁻¹*‖x‖
    have heq : matrixSpaceOperator S (B.symm x) = x := by
      change B (B.symm x) = x
      exact B.apply_symm_apply x
    have hh := hLN (B.symm x)
    rw [heq] at hh
    have hDiv : ‖B.symm x‖ ≤ ‖x‖/(Real.sqrt lam) :=
      (le_div_iff₀ (Real.sqrt_pos.mpr hLam)).mpr (by simpa only [mul_comm] using hh)
    simpa only [B,div_eq_mul_inv,mul_comm] using hDiv

theorem matrixSpaceOperator_realVec {n : ℕ} (A : Mat n) (k : Yau.RIdx n) :
    matrixSpaceOperator A (Yau.realVec k) = ∑ i : Yau.RIdx n, A i k • Yau.realVec i := by
  rw [matrixSpaceOperator_apply]
  simp [← real_inner_realVec,realVec_inner]

theorem matrixSpaceOperator_bilinear_contraction {n : ℕ} (S : Mat n)
    (H : Space n →L[ℝ] Space n →L[ℝ] ℝ) :
    (∑ k : Yau.RIdx n, H (matrixSpaceOperator S (Yau.realVec k))
      (matrixSpaceOperator S (Yau.realVec k))) =
        ∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n, (S*S.transpose) i j*H (Yau.realVec i) (Yau.realVec j) := by
  simp_rw [matrixSpaceOperator_realVec]
  simp only [map_sum,map_smul,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,Finset.mul_sum]
  calc
    _ = ∑ k : Yau.RIdx n, ∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n,
        S i k*S j k*H (Yau.realVec i) (Yau.realVec j) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ i : Yau.RIdx n, ∑ k : Yau.RIdx n, ∑ j : Yau.RIdx n,
        S i k*S j k*H (Yau.realVec i) (Yau.realVec j) := Finset.sum_comm
    _ = ∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n, ∑ k : Yau.RIdx n,
        S i k*S j k*H (Yau.realVec i) (Yau.realVec j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := by simp only [Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul]

theorem elliptic_matrix_space_equiv {n : ℕ} {lam upper : ℝ} (A : Mat n)
    (hLam : 0 < lam) (hLamUpper : lam ≤ upper) (hSymm : A.IsSymm)
    (hForm : ∀ v : Yau.RIdx n → ℝ,
      lam*(∑ i, (v i)^2) ≤ ∑ i, ∑ j, A i j*v i*v j ∧
        (∑ i, ∑ j, A i j*v i*v j) ≤ upper*(∑ i, (v i)^2)) :
    ∃ B : Space n ≃L[ℝ] Space n,
      ‖(B : Space n →L[ℝ] Space n)‖ ≤ Real.sqrt upper ∧
      ‖(B.symm : Space n →L[ℝ] Space n)‖ ≤ (Real.sqrt lam)⁻¹ ∧
      ∀ H : Space n →L[ℝ] Space n →L[ℝ] ℝ,
        (∑ k : Yau.RIdx n, H (B (Yau.realVec k)) (B (Yau.realVec k))) =
          ∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n, A i j*H (Yau.realVec i) (Yau.realVec j) := by
  have hEll : Elliptic (Set.univ : Set (Point n)) (fun _ => A) lam upper :=
    ⟨hLam,hLamUpper,fun p _ => ⟨hSymm,hForm⟩⟩
  have hA : A.PosSemidef := elliptic_posSemidef hEll (show (0 : Point n) ∈ Set.univ from Set.mem_univ _)
  obtain ⟨S,hS,hAS⟩ := posSemidef_symmetric_square hA
  have hST : S.transpose = S := hS
  have hGram : A = S.transpose*S := by simpa only [hST] using hAS
  have hBnds := matrixSpaceOperator_gram_bounds hGram hForm
  let B : Space n ≃L[ℝ] Space n :=
    matrixSpaceEquivOfLowerBound S hLam (fun x => (hBnds x).1)
  obtain ⟨hBN,hBI⟩ := matrixSpaceEquivOfLowerBound_norm_bounds S hLam hLamUpper
    (fun x => (hBnds x).1) (fun x => (hBnds x).2)
  refine ⟨B,?_,?_,?_⟩
  · simpa only [B] using hBN
  · simpa only [B] using hBI
  intro H
  change (∑ k : Yau.RIdx n, H (matrixSpaceOperator S (Yau.realVec k))
    (matrixSpaceOperator S (Yau.realVec k))) = _
  rw [matrixSpaceOperator_bilinear_contraction,hST,← hAS]


def spaceTimePullback {n : ℕ} (L : Space n ≃L[ℝ] Space n) (v : Point n → ℝ) : Point n → ℝ :=
  fun p => v (L p.1,p.2)

def gradientPullback {n : ℕ} (L : Space n ≃L[ℝ] Space n) :
    (Space n →L[ℝ] ℝ) ≃L[ℝ] Space n →L[ℝ] ℝ :=
  L.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)

theorem gradientPullback_apply {n : ℕ} (L : Space n ≃L[ℝ] Space n)
    (A : Space n →L[ℝ] ℝ) (x : Space n) : gradientPullback L A x = A (L x) := by
  simp [gradientPullback]

theorem gradientPullback_eq_comp {n : ℕ} (L : Space n ≃L[ℝ] Space n)
    (A : Space n →L[ℝ] ℝ) : gradientPullback L A = A.comp (L : Space n →L[ℝ] Space n) := by
  ext x
  rw [gradientPullback_apply]
  rfl

def hessianPullback {n : ℕ} (L : Space n ≃L[ℝ] Space n) :
    (Space n →L[ℝ] Space n →L[ℝ] ℝ) ≃L[ℝ] Space n →L[ℝ] Space n →L[ℝ] ℝ :=
  L.symm.arrowCongr (gradientPullback L)

theorem hessianPullback_apply {n : ℕ} (L : Space n ≃L[ℝ] Space n)
    (A : Space n →L[ℝ] Space n →L[ℝ] ℝ) (x y : Space n) :
    hessianPullback L A x y = A (L x) (L y) := by
  simp [hessianPullback,gradientPullback_apply]

theorem spatialD_spaceTimePullback {n : ℕ} (L : Space n ≃L[ℝ] Space n)
    (v : Point n → ℝ) (p : Point n) :
    spatialD (spaceTimePullback L v) p = gradientPullback L (spatialD v (L p.1,p.2)) := by
  change fderiv ℝ ((fun y : Space n => v (y,p.2)) ∘ L) p.1 =
    gradientPullback L (fderiv ℝ (fun y : Space n => v (y,p.2)) (L p.1))
  rw [L.comp_right_fderiv,gradientPullback_eq_comp]

theorem spatialDD_spaceTimePullback {n : ℕ} (L : Space n ≃L[ℝ] Space n)
    (v : Point n → ℝ) (p : Point n) :
    spatialDD (spaceTimePullback L v) p = hessianPullback L (spatialDD v (L p.1,p.2)) := by
  let f : Space n → ℝ := fun y => v (y,p.2)
  let P : (Space n →L[ℝ] ℝ) ≃L[ℝ] Space n →L[ℝ] ℝ := gradientPullback L
  have hFirst : fderiv ℝ (f ∘ L) = P ∘ (fderiv ℝ f) ∘ L := by
    funext x
    change fderiv ℝ (f ∘ L) x = gradientPullback L (fderiv ℝ f (L x))
    rw [L.comp_right_fderiv,gradientPullback_eq_comp]
  change fderiv ℝ (fderiv ℝ (f ∘ L)) p.1 = hessianPullback L (fderiv ℝ (fderiv ℝ f) (L p.1))
  rw [hFirst]
  change fderiv ℝ (P ∘ ((fderiv ℝ f) ∘ L)) p.1 = _
  rw [P.comp_fderiv,L.comp_right_fderiv]
  ext x y
  simp [P,ContinuousLinearMap.comp_apply,gradientPullback_apply,hessianPullback_apply]

theorem timeD_spaceTimePullback {n : ℕ} (L : Space n ≃L[ℝ] Space n)
    (v : Point n → ℝ) (T : ℝ) (p : Point n) :
    timeD (cylinder Set.univ 0 T) (spaceTimePullback L v) p =
      timeD (cylinder Set.univ 0 T) v (L p.1,p.2) := by
  simp only [timeD,spaceTimePullback,Yau.Parabolic.cylinder,Set.mem_prod,Set.mem_univ,true_and]

theorem gradientPullback_norm_le {n : ℕ} (L : Space n ≃L[ℝ] Space n)
    (A : Space n →L[ℝ] ℝ) :
    ‖gradientPullback L A‖ ≤ ‖(L : Space n →L[ℝ] Space n)‖*‖A‖ := by
  rw [gradientPullback_eq_comp]
  exact (A.opNorm_comp_le (L : Space n →L[ℝ] Space n)).trans_eq (mul_comm _ _)

theorem hessianPullback_norm_le {n : ℕ} (L : Space n ≃L[ℝ] Space n)
    (A : Space n →L[ℝ] Space n →L[ℝ] ℝ) :
    ‖hessianPullback L A‖ ≤ ‖(L : Space n →L[ℝ] Space n)‖^2*‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  have heq : hessianPullback L A x = gradientPullback L (A (L x)) := by
    ext y
    rw [hessianPullback_apply,gradientPullback_apply]
  rw [heq]
  calc
    _ ≤ ‖(L : Space n →L[ℝ] Space n)‖*‖A (L x)‖ := gradientPullback_norm_le _ _
    _ ≤ ‖(L : Space n →L[ℝ] Space n)‖*(‖A‖*‖L x‖) :=
      mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg _)
    _ ≤ ‖(L : Space n →L[ℝ] Space n)‖*(‖A‖*(‖(L : Space n →L[ℝ] Space n)‖*‖x‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left ((L : Space n →L[ℝ] Space n).le_opNorm x) (norm_nonneg _))
        (norm_nonneg _)
    _ = _ := by ring

theorem C2_spaceTimePullback {n : ℕ} (L : Space n ≃L[ℝ] Space n)
    {v : Point n → ℝ} {T : ℝ} (hv : C2 (cylinder Set.univ 0 T) v) :
    C2 (cylinder Set.univ 0 T) (spaceTimePullback L v) := by
  let Φ : Point n → Point n := fun p => (L p.1,p.2)
  have hΦ : Continuous Φ := (L.continuous.comp continuous_fst).prodMk continuous_snd
  have hMap : Set.MapsTo Φ (cylinder Set.univ 0 T) (cylinder Set.univ 0 T) :=
    fun p hp => ⟨Set.mem_univ _,hp.2⟩
  have hu : ContinuousOn (spaceTimePullback L v) (cylinder Set.univ 0 T) :=
    hv.1.comp hΦ.continuousOn hMap
  have hD : ContinuousOn (spatialD (spaceTimePullback L v)) (cylinder Set.univ 0 T) := by
    apply ((gradientPullback L).continuous.comp_continuousOn (hv.2.1.comp hΦ.continuousOn hMap)).congr
    intro p _
    exact spatialD_spaceTimePullback L v p
  have hDD : ContinuousOn (spatialDD (spaceTimePullback L v)) (cylinder Set.univ 0 T) := by
    apply ((hessianPullback L).continuous.comp_continuousOn (hv.2.2.1.comp hΦ.continuousOn hMap)).congr
    intro p _
    exact spatialDD_spaceTimePullback L v p
  have hTime : ContinuousOn (timeD (cylinder Set.univ 0 T) (spaceTimePullback L v))
      (cylinder Set.univ 0 T) := by
    apply (hv.2.2.2.1.comp hΦ.continuousOn hMap).congr
    intro p _
    exact timeD_spaceTimePullback L v T p
  refine ⟨hu,hD,hDD,hTime,?_,?_⟩
  · intro p hp
    have hV := hv.2.2.2.2.1 (Φ p) (hMap hp)
    exact ContDiffAt.comp (f := (L : Space n → Space n)) (g := fun y : Space n => v (y,p.2))
      p.1 hV (by fun_prop)
  · intro p hp
    have hV := hv.2.2.2.2.2 (Φ p) (hMap hp)
    simpa only [Φ,spaceTimePullback,Yau.Parabolic.cylinder,Set.mem_prod,Set.mem_univ,true_and] using hV

theorem holderBound_comp_spaceLinearMap {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {α T C : ℝ} {f : Point n → E} (hα : 0 ≤ α) (L : Space n →L[ℝ] Space n)
    (hf : HolderBound α (cylinder Set.univ 0 T) f C) :
    HolderBound α (cylinder Set.univ 0 T) (fun p : Point n => f (L p.1,p.2))
      (C*(1+‖L‖^α)) := by
  have hPow : 0 ≤ ‖L‖^α := Real.rpow_nonneg (norm_nonneg _) _
  have hFactor : 1 ≤ 1+‖L‖^α := by linarith
  have hMap (p : Point n) (hp : p ∈ cylinder Set.univ 0 T) :
      (L p.1,p.2) ∈ cylinder Set.univ 0 T := ⟨Set.mem_univ _,hp.2⟩
  refine ⟨mul_nonneg hf.1 (by positivity),?_,?_⟩
  · intro p hp
    exact (hf.2.1 _ (hMap p hp)).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hFactor hf.1)
  · intro p hp q hq
    have hsp : ‖L p.1-L q.1‖^α ≤ ‖L‖^α*‖p.1-q.1‖^α := by
      rw [← map_sub]
      calc
        _ ≤ (‖L‖*‖p.1-q.1‖)^α :=
          Real.rpow_le_rpow (norm_nonneg _) (L.le_opNorm _) hα
        _ = _ := Real.mul_rpow (norm_nonneg _) (norm_nonneg _)
    have hWeight : holderWeight α (L p.1,p.2) (L q.1,q.2) ≤
        (1+‖L‖^α)*holderWeight α p q := by
      unfold holderWeight
      calc
        _ ≤ ‖L‖^α*‖p.1-q.1‖^α+|p.2-q.2|^(α/2) := add_le_add hsp le_rfl
        _ ≤ (1+‖L‖^α)*‖p.1-q.1‖^α+(1+‖L‖^α)*|p.2-q.2|^(α/2) :=
          add_le_add
            (mul_le_mul_of_nonneg_right (by linarith : ‖L‖^α ≤ 1+‖L‖^α)
              (Real.rpow_nonneg (norm_nonneg _) _))
            (by simpa only [one_mul] using
              (mul_le_mul_of_nonneg_right hFactor (Real.rpow_nonneg (abs_nonneg _) _)))
        _ = _ := by ring
    exact (hf.2.2 _ (hMap p hp) _ (hMap q hq)).trans
      ((mul_le_mul_of_nonneg_left hWeight hf.1).trans_eq (by ring))

theorem holderBound_comp_continuousLinearMap {n : ℕ} {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α C : ℝ} {Q : Set (Point n)} {f : Point n → E} (L : E →L[ℝ] F)
    (hf : HolderBound α Q f C) :
    HolderBound α Q (fun p : Point n => L (f p)) (‖L‖*C) := by
  refine ⟨mul_nonneg (norm_nonneg _) hf.1,?_,?_⟩
  · intro p hp
    exact (L.le_opNorm (f p)).trans (mul_le_mul_of_nonneg_left (hf.2.1 p hp) (norm_nonneg _))
  · intro p hp q hq
    change ‖L (f p)-L (f q)‖ ≤ _
    rw [← map_sub]
    exact (L.le_opNorm (f p-f q)).trans
      ((mul_le_mul_of_nonneg_left (hf.2.2 p hp q hq) (norm_nonneg _)).trans_eq (by ring))

theorem SchauderBound_spaceTimePullback {n : ℕ} {α T C : ℝ} {v : Point n → ℝ}
    (hα : 0 ≤ α) (L : Space n ≃L[ℝ] Space n)
    (hv : SchauderBound α (cylinder Set.univ 0 T) v C) :
    SchauderBound α (cylinder Set.univ 0 T) (spaceTimePullback L v)
      (C*(1+‖(L : Space n →L[ℝ] Space n)‖)^2*(1+‖(L : Space n →L[ℝ] Space n)‖^α)) := by
  have hC0 : 0 ≤ C := hv.2.1
  let K : ℝ := ‖(L : Space n →L[ℝ] Space n)‖
  let W : ℝ := 1+K^α
  let R : ℝ := (1+K)^2
  have hK : 0 ≤ K := norm_nonneg _
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hW1 : 1 ≤ W := by dsimp [W]; exact le_add_of_nonneg_right (Real.rpow_nonneg hK _)
  have hR1 : 1 ≤ R := by dsimp [R]; nlinarith [sq_nonneg K]
  have hKR : K ≤ R := by dsimp [R]; nlinarith [sq_nonneg K]
  have hK2R : K^2 ≤ R := by dsimp [R]; nlinarith
  have hR : 0 ≤ R := (by norm_num : (0:ℝ) ≤ 1).trans hR1
  have hBudget : C ≤ C*R*W := by
    calc
      _ = C*1*1 := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hR1 hv.2.1) hW1
        (by positivity) (by positivity)
  have hmono {E : Type} [NormedAddCommGroup E] {f : Point n → E} {A B : ℝ}
      (hf : HolderBound α (cylinder Set.univ 0 T) f A) (hAB : A ≤ B) :
      HolderBound α (cylinder Set.univ 0 T) f B := by
    refine ⟨hf.1.trans hAB,fun p hp => (hf.2.1 p hp).trans hAB,?_⟩
    intro p hp q hq
    exact (hf.2.2 p hp q hq).trans (mul_le_mul_of_nonneg_right hAB
      (by dsimp [holderWeight]; positivity))
  have hcongr {E : Type} [NormedAddCommGroup E] {f g : Point n → E} {A : ℝ}
      (hf : HolderBound α (cylinder Set.univ 0 T) f A)
      (heq : Set.EqOn g f (cylinder Set.univ 0 T)) :
      HolderBound α (cylinder Set.univ 0 T) g A := by
    refine ⟨hf.1,?_,?_⟩
    · intro p hp
      simpa only [heq hp] using hf.2.1 p hp
    · intro p hp q hq
      simpa only [heq hp,heq hq] using hf.2.2 p hp q hq
  have hMap (p : Point n) (hp : p ∈ cylinder Set.univ 0 T) :
      (L p.1,p.2) ∈ cylinder Set.univ 0 T := ⟨Set.mem_univ _,hp.2⟩
  have hPN : ‖(hessianPullback L : (Space n →L[ℝ] Space n →L[ℝ] ℝ) →L[ℝ]
      Space n →L[ℝ] Space n →L[ℝ] ℝ)‖ ≤ K^2 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg K)
    intro A
    exact hessianPullback_norm_le L A
  have hHp := holderBound_comp_continuousLinearMap
    (hessianPullback L : (Space n →L[ℝ] Space n →L[ℝ] ℝ) →L[ℝ]
      Space n →L[ℝ] Space n →L[ℝ] ℝ)
    (holderBound_comp_spaceLinearMap hα (L : Space n →L[ℝ] Space n) hv.2.2.2.1)
  have hHH : HolderBound α (cylinder Set.univ 0 T) (spatialDD (spaceTimePullback L v))
      (C*R*W) := by
    apply hmono (hcongr hHp (fun p _ => spatialDD_spaceTimePullback L v p))
    calc
      _ ≤ K^2*(C*W) := mul_le_mul_of_nonneg_right hPN (mul_nonneg hv.2.1 hW)
      _ ≤ R*(C*W) := mul_le_mul_of_nonneg_right hK2R (mul_nonneg hv.2.1 hW)
      _ = _ := by ring
  have hTp := holderBound_comp_spaceLinearMap hα (L : Space n →L[ℝ] Space n) hv.2.2.2.2
  have hTT : HolderBound α (cylinder Set.univ 0 T)
      (timeD (cylinder Set.univ 0 T) (spaceTimePullback L v)) (C*R*W) := by
    apply hmono (hcongr hTp (fun p _ => timeD_spaceTimePullback L v T p))
    calc
      _ = (C*W)*1 := by ring
      _ ≤ (C*W)*R := mul_le_mul_of_nonneg_left hR1 (mul_nonneg hv.2.1 hW)
      _ = _ := by ring
  change SchauderBound α (cylinder Set.univ 0 T) (spaceTimePullback L v) (C*R*W)
  refine ⟨C2_spaceTimePullback L hv.1,by positivity,?_,hHH,hTT⟩
  intro p hp
  constructor
  · exact ((hv.2.2.1 _ (hMap p hp)).1).trans hBudget
  · rw [spatialD_spaceTimePullback]
    calc
      _ ≤ K*‖spatialD v (L p.1,p.2)‖ := gradientPullback_norm_le _ _
      _ ≤ K*C := mul_le_mul_of_nonneg_left (hv.2.2.1 _ (hMap p hp)).2 hK
      _ ≤ R*C := mul_le_mul_of_nonneg_right hKR hv.2.1
      _ ≤ (R*C)*W := by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hW1 (mul_nonneg hR hv.2.1)
      _ = _ := by ring


theorem linearOp_spaceTimePullback_constant {n : ℕ} {A : Mat n}
    (B : Space n ≃L[ℝ] Space n)
    (hB : ∀ H : Space n →L[ℝ] Space n →L[ℝ] ℝ,
      (∑ k : Yau.RIdx n, H (B (Yau.realVec k)) (B (Yau.realVec k))) =
        ∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n, A i j*H (Yau.realVec i) (Yau.realVec j))
    (v : Point n → ℝ) (T : ℝ) (p : Point n) :
    linearOp (cylinder Set.univ 0 T) (fun _ => A) (fun _ _ => 0) (spaceTimePullback B.symm v) p =
      linearOp (cylinder Set.univ 0 T) (fun _ => (1 : Mat n)) (fun _ _ => 0) v (B.symm p.1,p.2) := by
  have hContr : (∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n,
      A i j*spatialDD (spaceTimePullback B.symm v) p (Yau.realVec i) (Yau.realVec j)) =
        ∑ k : Yau.RIdx n, spatialDD v (B.symm p.1,p.2) (Yau.realVec k) (Yau.realVec k) := by
    rw [← hB (spatialDD (spaceTimePullback B.symm v) p)]
    simp only [spatialDD_spaceTimePullback,hessianPullback_apply,ContinuousLinearEquiv.symm_apply_apply]
  simp only [linearOp,zero_mul,Finset.sum_const_zero,sub_zero]
  rw [timeD_spaceTimePullback,hContr]
  simp [Matrix.one_apply]

theorem constant_elliptic_schauder_solution {n : ℕ} {α lam upper : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hLam : 0 < lam) (hLamUpper : lam ≤ upper) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : Mat n, A.IsSymm →
      (∀ z : Yau.RIdx n → ℝ,
        lam*(∑ i, (z i)^2) ≤ ∑ i, ∑ j, A i j*z i*z j ∧
          (∑ i, ∑ j, A i j*z i*z j) ≤ upper*(∑ i, (z i)^2)) →
      ∀ T F : ℝ, 0 < T → T ≤ 1 → ∀ f : Point n → ℝ,
        HolderBound α (cylinder Set.univ 0 T) f F →
        ∃ u : Point n → ℝ, SchauderBound α (cylinder Set.univ 0 T) u (C*F) ∧
          (∀ x : Space n, u (x,0) = 0) ∧
          ∀ p ∈ cylinder Set.univ 0 T,
            linearOp (cylinder Set.univ 0 T) (fun _ => A) (fun _ _ => 0) u p = f p := by
  obtain ⟨C0,hC0,hEucl⟩ := heatDuhamel_schauder_solution (n := n) hα hα1
  let normBudget : ℝ := Real.sqrt upper
  let invBudget : ℝ := (Real.sqrt lam)⁻¹
  let C : ℝ := C0*(1+normBudget^α)*(1+invBudget)^2*(1+invBudget^α)
  have hU : 0 ≤ normBudget := Real.sqrt_nonneg _
  have hI : 0 ≤ invBudget := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro A hSymm hForm T F hT hT1 f hf
  have hF0 : 0 ≤ F := hf.1
  obtain ⟨B,hBN,hBI,hContract⟩ := elliptic_matrix_space_equiv A hLam hLamUpper hSymm hForm
  let g : Point n → ℝ := spaceTimePullback B f
  have hg : HolderBound α (cylinder Set.univ 0 T) g
      (F*(1+‖(B : Space n →L[ℝ] Space n)‖^α)) :=
    holderBound_comp_spaceLinearMap hα.le (B : Space n →L[ℝ] Space n) hf
  let v : Point n → ℝ := fun p => heatDuhamel g p.2 p.1
  have hV := hEucl T (F*(1+‖(B : Space n →L[ℝ] Space n)‖^α)) hT hT1 g hg
  let u : Point n → ℝ := spaceTimePullback B.symm v
  have hUp := SchauderBound_spaceTimePullback hα.le B.symm hV.1
  have hPowB : ‖(B : Space n →L[ℝ] Space n)‖^α ≤ normBudget^α :=
    Real.rpow_le_rpow (norm_nonneg _) hBN hα.le
  have hPowI : ‖(B.symm : Space n →L[ℝ] Space n)‖^α ≤ invBudget^α :=
    Real.rpow_le_rpow (norm_nonneg _) hBI hα.le
  have hSqI : (1+‖(B.symm : Space n →L[ℝ] Space n)‖)^2 ≤ (1+invBudget)^2 :=
    pow_le_pow_left₀ (by positivity) (add_le_add (show (1:ℝ) ≤ 1 from le_rfl) hBI) 2
  have hBudget : (C0*(F*(1+‖(B : Space n →L[ℝ] Space n)‖^α)))*
      (1+‖(B.symm : Space n →L[ℝ] Space n)‖)^2*(1+‖(B.symm : Space n →L[ℝ] Space n)‖^α) ≤ C*F := by
    have h0 : C0*(F*(1+‖(B : Space n →L[ℝ] Space n)‖^α)) ≤ C0*(F*(1+normBudget^α)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (add_le_add (show (1:ℝ) ≤ 1 from le_rfl) hPowB) hF0) hC0.le
    have h1 := mul_le_mul h0 hSqI (sq_nonneg _) (by positivity)
    exact (mul_le_mul h1 (add_le_add (show (1:ℝ) ≤ 1 from le_rfl) hPowI) (by positivity) (by positivity)).trans_eq
      (by dsimp [C] <;> ring)
  have hHolderMono {E : Type} [NormedAddCommGroup E] {w : Point n → E} {a b : ℝ}
      (hw : HolderBound α (cylinder Set.univ 0 T) w a) (hab : a ≤ b) :
      HolderBound α (cylinder Set.univ 0 T) w b := by
    refine ⟨hw.1.trans hab,fun p hp => (hw.2.1 p hp).trans hab,?_⟩
    intro p hp q hq
    exact (hw.2.2 p hp q hq).trans
      (mul_le_mul_of_nonneg_right hab (by dsimp [holderWeight]; positivity))
  have hSchauderMono {w : Point n → ℝ} {a b : ℝ}
      (hw : SchauderBound α (cylinder Set.univ 0 T) w a) (hab : a ≤ b) :
      SchauderBound α (cylinder Set.univ 0 T) w b :=
    ⟨hw.1,hw.2.1.trans hab,fun p hp => ⟨(hw.2.2.1 p hp).1.trans hab,(hw.2.2.1 p hp).2.trans hab⟩,
      hHolderMono hw.2.2.2.1 hab,hHolderMono hw.2.2.2.2 hab⟩
  refine ⟨u,hSchauderMono hUp hBudget,?_,?_⟩
  · intro x
    exact hV.2.1 (B.symm x)
  · intro p hp
    change linearOp (cylinder Set.univ 0 T) (fun _ => A) (fun _ _ => 0)
      (spaceTimePullback B.symm v) p = _
    rw [linearOp_spaceTimePullback_constant B hContract v T p]
    have hq : (B.symm p.1,p.2) ∈ cylinder Set.univ 0 T := ⟨Set.mem_univ _,hp.2⟩
    simpa only [g,spaceTimePullback,ContinuousLinearEquiv.apply_symm_apply,Prod.eta] using
      hV.2.2 (B.symm p.1,p.2) hq


abbrev HolderPairs {n : ℕ} (Q : Set (Point n)) := {z : Q × Q // z.1 ≠ z.2}

def holderGraph {n : ℕ} (α : ℝ) (Q : Set (Point n)) :
    Submodule ℝ ((BoundedContinuousFunction Q ℝ) × (BoundedContinuousFunction (HolderPairs Q) ℝ)) where
  carrier := {u | ∀ z : HolderPairs Q,
    u.1 z.val.1-u.1 z.val.2 = holderWeight α z.val.1.val z.val.2.val*u.2 z}
  zero_mem' := by intro z; simp
  add_mem' := by
    intro f g hf hg z
    change (f.1 z.val.1+g.1 z.val.1)-(f.1 z.val.2+g.1 z.val.2) =
      holderWeight α z.val.1.val z.val.2.val*(f.2 z+g.2 z)
    rw [mul_add,← hf z,← hg z]
    ring
  smul_mem' := by
    intro a f hf z
    change a*f.1 z.val.1-a*f.1 z.val.2 = holderWeight α z.val.1.val z.val.2.val*(a*f.2 z)
    rw [← mul_sub,hf z]
    ring

theorem holderGraph_isClosed {n : ℕ} (α : ℝ) (Q : Set (Point n)) :
    IsClosed (holderGraph α Q : Set ((BoundedContinuousFunction Q ℝ) × (BoundedContinuousFunction (HolderPairs Q) ℝ))) := by
  change IsClosed {u : (BoundedContinuousFunction Q ℝ) × (BoundedContinuousFunction (HolderPairs Q) ℝ) | ∀ z : HolderPairs Q,
    u.1 z.val.1-u.1 z.val.2 = holderWeight α z.val.1.val z.val.2.val*u.2 z}
  simp only [Set.setOf_forall]
  apply isClosed_iInter
  intro z
  exact isClosed_eq
    (((BoundedContinuousFunction.evalCLM ℝ z.val.1).continuous.comp continuous_fst).sub
      ((BoundedContinuousFunction.evalCLM ℝ z.val.2).continuous.comp continuous_fst))
    (continuous_const.mul ((BoundedContinuousFunction.evalCLM ℝ z).continuous.comp continuous_snd))

instance holderGraph_completeSpace {n : ℕ} (α : ℝ) (Q : Set (Point n)) :
    CompleteSpace (holderGraph α Q) := (holderGraph_isClosed α Q).completeSpace_coe

def holderGraphFun {n : ℕ} {α : ℝ} {Q : Set (Point n)} (u : holderGraph α Q) : Point n → ℝ := by
  classical
  exact fun p => if hp : p ∈ Q then u.val.1 ⟨p,hp⟩ else 0

theorem holderGraphFun_apply {n : ℕ} {α : ℝ} {Q : Set (Point n)} (u : holderGraph α Q) (p : Q) :
    holderGraphFun u p.val = u.val.1 p := by simp [holderGraphFun,p.property]

theorem holderGraphFun_holderBound {n : ℕ} {α : ℝ} {Q : Set (Point n)} (u : holderGraph α Q) :
    HolderBound α Q (holderGraphFun u) ‖u‖ := by
  have hN1 : ‖u.val.1‖ ≤ ‖u‖ := by
    change ‖u.val.1‖ ≤ max ‖u.val.1‖ ‖u.val.2‖
    exact le_max_left _ _
  have hN2 : ‖u.val.2‖ ≤ ‖u‖ := by
    change ‖u.val.2‖ ≤ max ‖u.val.1‖ ‖u.val.2‖
    exact le_max_right _ _
  have hNu : 0 ≤ ‖u‖ := by
    change 0 ≤ max ‖u.val.1‖ ‖u.val.2‖
    exact (norm_nonneg u.val.1).trans (le_max_left _ _)
  refine ⟨hNu,?_,?_⟩
  · intro p hp
    have hP := (u.val.1.norm_coe_le_norm ⟨p,hp⟩).trans hN1
    simpa only [holderGraphFun,dif_pos hp] using hP
  · intro p hp q hq
    by_cases hpq : p = q
    · subst q
      simp only [sub_self,norm_zero]
      exact mul_nonneg hNu (by dsimp [holderWeight]; positivity)
    let pQ : Q := ⟨p,hp⟩
    let qQ : Q := ⟨q,hq⟩
    have hpqQ : pQ ≠ qQ := fun h => hpq (congrArg Subtype.val h)
    let z : HolderPairs Q := ⟨(pQ,qQ),hpqQ⟩
    have heq : holderGraphFun u p-holderGraphFun u q = holderWeight α p q*u.val.2 z := by
      simpa only [holderGraphFun,dif_pos hp,dif_pos hq,pQ,qQ,z] using u.property z
    have hW : 0 ≤ holderWeight α p q := by dsimp [holderWeight]; positivity
    rw [heq,Real.norm_eq_abs,abs_mul,abs_of_nonneg hW]
    calc
      _ ≤ holderWeight α p q*‖u‖ :=
        mul_le_mul_of_nonneg_left
          (by simpa only [Real.norm_eq_abs] using (u.val.2.norm_coe_le_norm z).trans hN2) hW
      _ = _ := mul_comm _ _

theorem holderWeight_pos_of_ne {n : ℕ} (α : ℝ) {p q : Point n} (hpq : p ≠ q) :
    0 < holderWeight α p q := by
  unfold holderWeight
  by_cases hxy : p.1 = q.1
  · have ht : p.2 ≠ q.2 := fun h => hpq (Prod.ext hxy h)
    exact add_pos_of_nonneg_of_pos (Real.rpow_nonneg (norm_nonneg _) _)
      (Real.rpow_pos_of_pos (abs_pos.mpr (sub_ne_zero.mpr ht)) _)
  · exact add_pos_of_pos_of_nonneg
      (Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) _)
      (Real.rpow_nonneg (abs_nonneg _) _)

theorem holderWeight_continuous {n : ℕ} {α : ℝ} (hα : 0 ≤ α) :
    Continuous (fun z : Point n × Point n => holderWeight α z.1 z.2) := by
  unfold holderWeight
  exact ((Real.continuous_rpow_const hα).comp
    (continuous_norm.comp (continuous_fst.fst.sub continuous_snd.fst))).add
      ((Real.continuous_rpow_const (by positivity : 0 ≤ α/2)).comp
        (continuous_fst.snd.sub continuous_snd.snd).abs)


def boundedRealContinuousOfBound {X : Type*} [TopologicalSpace X] (f : X → ℝ)
    (hc : Continuous f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    BoundedContinuousFunction X ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨f,hc⟩ (2*C) (by
    intro x y
    rw [dist_eq_norm]
    exact (norm_sub_le (f x) (f y)).trans (by linarith [hC x,hC y]))

theorem holderPair_weight_pos {n : ℕ} (α : ℝ) {Q : Set (Point n)} (z : HolderPairs Q) :
    0 < holderWeight α z.val.1.val z.val.2.val :=
  holderWeight_pos_of_ne α (fun h => z.property (Subtype.ext h))

theorem holderQuotient_continuous {n : ℕ} {α C : ℝ} {Q : Set (Point n)} {f : Point n → ℝ}
    (hα : 0 < α) (hf : HolderBound α Q f C) :
    Continuous (fun z : HolderPairs Q =>
      (f z.val.1.val-f z.val.2.val)/holderWeight α z.val.1.val z.val.2.val) := by
  have h1 : Continuous (fun z : HolderPairs Q => z.val.1) :=
    continuous_fst.comp continuous_subtype_val
  have h2 : Continuous (fun z : HolderPairs Q => z.val.2) :=
    continuous_snd.comp continuous_subtype_val
  have hval : Continuous (fun p : Q => (p.val : Point n)) := continuous_subtype_val
  have hx : Continuous (fun z : HolderPairs Q => z.val.1.val.1-z.val.2.val.1) :=
    (hval.comp h1).fst.sub (hval.comp h2).fst
  have ht : Continuous (fun z : HolderPairs Q => z.val.1.val.2-z.val.2.val.2) :=
    (hval.comp h1).snd.sub (hval.comp h2).snd
  have hW : Continuous (fun z : HolderPairs Q => holderWeight α z.val.1.val z.val.2.val) := by
    unfold holderWeight
    exact (hx.norm.rpow_const (fun _ => Or.inr hα.le)).add
      (ht.abs.rpow_const (fun _ => Or.inr (by positivity : 0 ≤ α/2)))
  have hFc : Continuous (fun p : Q => f p.val) := (holderBound_continuousOn hα hf).domRestrict
  exact ((hFc.comp h1).sub (hFc.comp h2)).div hW (fun z => (holderPair_weight_pos α z).ne')

theorem holderQuotient_norm_bound {n : ℕ} {α C : ℝ} {Q : Set (Point n)} {f : Point n → ℝ}
    (hf : HolderBound α Q f C) (z : HolderPairs Q) :
    ‖(f z.val.1.val-f z.val.2.val)/holderWeight α z.val.1.val z.val.2.val‖ ≤ C := by
  rw [norm_div,Real.norm_eq_abs (holderWeight α z.val.1.val z.val.2.val),
    abs_of_pos (holderPair_weight_pos α z)]
  exact (div_le_iff₀ (holderPair_weight_pos α z)).mpr
    (hf.2.2 z.val.1.val z.val.1.property z.val.2.val z.val.2.property)

def holderSourceBCF {n : ℕ} {α C : ℝ} {Q : Set (Point n)} {f : Point n → ℝ}
    (hα : 0 < α) (hf : HolderBound α Q f C) : BoundedContinuousFunction Q ℝ :=
  boundedRealContinuousOfBound (fun p : Q => f p.val)
    (holderBound_continuousOn hα hf).domRestrict C (fun p => hf.2.1 p.val p.property)

def holderQuotientBCF {n : ℕ} {α C : ℝ} {Q : Set (Point n)} {f : Point n → ℝ}
    (hα : 0 < α) (hf : HolderBound α Q f C) : BoundedContinuousFunction (HolderPairs Q) ℝ :=
  boundedRealContinuousOfBound (fun z : HolderPairs Q =>
    (f z.val.1.val-f z.val.2.val)/holderWeight α z.val.1.val z.val.2.val)
    (holderQuotient_continuous hα hf) C (holderQuotient_norm_bound hf)

def holderGraphOfBound {n : ℕ} {α C : ℝ} {Q : Set (Point n)} {f : Point n → ℝ}
    (hα : 0 < α) (hf : HolderBound α Q f C) : holderGraph α Q :=
  ⟨(holderSourceBCF hα hf,holderQuotientBCF hα hf),by
    intro z
    change f z.val.1.val-f z.val.2.val =
      holderWeight α z.val.1.val z.val.2.val *
        ((f z.val.1.val-f z.val.2.val)/holderWeight α z.val.1.val z.val.2.val)
    exact (mul_div_cancel₀ _ (holderPair_weight_pos α z).ne').symm⟩

theorem holderGraphOfBound_apply {n : ℕ} {α C : ℝ} {Q : Set (Point n)} {f : Point n → ℝ}
    (hα : 0 < α) (hf : HolderBound α Q f C) (p : Q) :
    (holderGraphOfBound hα hf).val.1 p = f p.val := rfl

theorem holderGraphOfBound_norm_le {n : ℕ} {α C : ℝ} {Q : Set (Point n)} {f : Point n → ℝ}
    (hα : 0 < α) (hf : HolderBound α Q f C) : ‖holderGraphOfBound hα hf‖ ≤ C := by
  change max ‖(holderGraphOfBound hα hf).val.1‖ ‖(holderGraphOfBound hα hf).val.2‖ ≤ C
  apply max_le
  · apply (BoundedContinuousFunction.norm_le hf.1).mpr
    intro p
    exact hf.2.1 p.val p.property
  · apply (BoundedContinuousFunction.norm_le hf.1).mpr
    intro z
    change ‖(f z.val.1.val-f z.val.2.val)/holderWeight α z.val.1.val z.val.2.val‖ ≤ C
    have hWpos : 0 < holderWeight α z.val.1.val z.val.2.val :=
      holderWeight_pos_of_ne α (fun h => z.property (Subtype.ext h))
    rw [norm_div,Real.norm_eq_abs (holderWeight α z.val.1.val z.val.2.val),abs_of_pos hWpos]
    exact (div_le_iff₀ hWpos).mpr
      (hf.2.2 z.val.1.val z.val.1.property z.val.2.val z.val.2.property)

theorem holderGraphOfBound_eqOn {n : ℕ} {α C : ℝ} {Q : Set (Point n)} {f : Point n → ℝ}
    (hα : 0 < α) (hf : HolderBound α Q f C) :
    Set.EqOn (holderGraphFun (holderGraphOfBound hα hf)) f Q := by
  intro p hp
  rw [holderGraphFun_apply _ ⟨p,hp⟩]
  rfl


theorem holderGraph_norm_le_of_holderBound {n : ℕ} {α C : ℝ} {Q : Set (Point n)}
    (u : holderGraph α Q) (hf : HolderBound α Q (holderGraphFun u) C) : ‖u‖ ≤ C := by
  change max ‖u.val.1‖ ‖u.val.2‖ ≤ C
  apply max_le
  · apply (BoundedContinuousFunction.norm_le hf.1).mpr
    intro p
    simpa only [holderGraphFun_apply] using hf.2.1 p.val p.property
  · apply (BoundedContinuousFunction.norm_le hf.1).mpr
    intro z
    have hW : 0 < holderWeight α z.val.1.val z.val.2.val :=
      holderWeight_pos_of_ne α (fun h => z.property (Subtype.ext h))
    have hB := hf.2.2 z.val.1.val z.val.1.property z.val.2.val z.val.2.property
    rw [holderGraphFun_apply,holderGraphFun_apply,u.property z,norm_mul,
      Real.norm_eq_abs (holderWeight α z.val.1.val z.val.2.val),abs_of_pos hW] at hB
    exact (mul_le_mul_iff_right₀ hW).mp (hB.trans_eq (mul_comm _ _))

theorem holderGraph_ext {n : ℕ} {α : ℝ} {Q : Set (Point n)} {u v : holderGraph α Q}
    (h : ∀ p : Q, u.val.1 p = v.val.1 p) : u = v := by
  apply Subtype.ext
  apply Prod.ext
  · exact BoundedContinuousFunction.ext h
  · apply BoundedContinuousFunction.ext
    intro z
    have hW : holderWeight α z.val.1.val z.val.2.val ≠ 0 :=
      (holderWeight_pos_of_ne α (fun h => z.property (Subtype.ext h))).ne'
    apply mul_left_cancel₀ hW
    rw [← u.property z,← v.property z,h z.val.1,h z.val.2]

theorem holderGraphFun_zero {n : ℕ} {α : ℝ} {Q : Set (Point n)} :
    holderGraphFun (0 : holderGraph α Q) = 0 := by
  classical
  funext p
  by_cases hp : p ∈ Q <;> simp [holderGraphFun,hp]

theorem holderGraphFun_add {n : ℕ} {α : ℝ} {Q : Set (Point n)} (u v : holderGraph α Q) :
    holderGraphFun (u+v) = holderGraphFun u+holderGraphFun v := by
  classical
  funext p
  by_cases hp : p ∈ Q <;> simp [holderGraphFun,hp]

theorem holderGraphFun_smul {n : ℕ} {α : ℝ} {Q : Set (Point n)} (a : ℝ) (u : holderGraph α Q) :
    holderGraphFun (a • u) = a • holderGraphFun u := by
  classical
  funext p
  by_cases hp : p ∈ Q <;> simp [holderGraphFun,hp]


theorem heatAverage_smul {n : ℕ} (a t : ℝ) (g : Space n → ℝ) (x : Space n) :
    heatAverage t (a • g) x = a * heatAverage t g x := by
  simp only [heatAverage_def,Pi.smul_apply,smul_eq_mul]
  calc
    _ = ∫ y : Space n, a * (gaussianKernel t y * g (x-y)) := by
      apply integral_congr_ae
      exact ae_of_all _ (fun _ => by ring)
    _ = _ := integral_const_mul _ _

theorem heatAverage_add_of_bounded {n : ℕ} {t F G : ℝ} {f g : Space n → ℝ}
    (ht : 0 < t) (hf : Continuous f) (hg : Continuous g)
    (hF : ∀ y, |f y| ≤ F) (hG : ∀ y, |g y| ≤ G) (x : Space n) :
    heatAverage t (f+g) x = heatAverage t f x+heatAverage t g x := by
  simp only [heatAverage_def,Pi.add_apply,mul_add]
  exact integral_add (heatAverage_integrable_of_bounded ht hf hF x)
    (heatAverage_integrable_of_bounded ht hg hG x)

theorem heatDuhamel_smul {n : ℕ} (a : ℝ) (f : Point n → ℝ) (t : ℝ) (x : Space n) :
    heatDuhamel (a • f) t x = a * heatDuhamel f t x := by
  change (∫ s in (0 : ℝ)..t, heatAverage (t-s) (a • fun y => f (y,s)) x) = _
  simp_rw [heatAverage_smul]
  exact intervalIntegral.integral_const_mul _ _

theorem heatDuhamel_add_of_bounded {n : ℕ} {F G t : ℝ} {f g : Point n → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hF : ∀ p, |f p| ≤ F) (hG : ∀ p, |g p| ≤ G)
    (ht : 0 ≤ t) (x : Space n) :
    heatDuhamel (f+g) t x = heatDuhamel f t x+heatDuhamel g t x := by
  have hFi := (heatDuhamel_integrable_and_bound hf hF ht x).1
  have hGi := (heatDuhamel_integrable_and_bound hg hG ht x).1
  simp only [heatDuhamel]
  calc
    _ = ∫ s in (0 : ℝ)..t,
        (heatAverage (t-s) (fun y => f (y,s)) x+heatAverage (t-s) (fun y => g (y,s)) x) := by
      apply intervalIntegral.integral_congr_Ioo_of_le ht
      intro s hs
      exact heatAverage_add_of_bounded (sub_pos.mpr hs.2)
        (hf.comp (continuous_id.prodMk continuous_const))
        (hg.comp (continuous_id.prodMk continuous_const))
        (fun y => hF (y,s)) (fun y => hG (y,s)) x
    _ = _ := intervalIntegral.integral_add hFi hGi


theorem heatDuhamel_add_of_holder {n : ℕ} {α F G T t : ℝ} {f g : Point n → ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (hf : HolderBound α (cylinder Set.univ 0 T) f F)
    (hg : HolderBound α (cylinder Set.univ 0 T) g G) (ht : t ∈ Set.Icc 0 T) (x : Space n) :
    heatDuhamel (f+g) t x = heatDuhamel f t x+heatDuhamel g t x := by
  let fhat : Point n → ℝ := fun p => f (p.1,max 0 (min p.2 T))
  let ghat : Point n → ℝ := fun p => g (p.1,max 0 (min p.2 T))
  have hFhat : HolderBound α Set.univ fhat F := holderBound_timeClamp hα.le hT hf
  have hGhat : HolderBound α Set.univ ghat G := holderBound_timeClamp hα.le hT hg
  have hFc : Continuous fhat := continuousOn_univ.mp (holderBound_continuousOn hα hFhat)
  have hGc : Continuous ghat := continuousOn_univ.mp (holderBound_continuousOn hα hGhat)
  rw [← heatDuhamel_timeClamp (f+g) ht x,← heatDuhamel_timeClamp f ht x,
    ← heatDuhamel_timeClamp g ht x]
  change heatDuhamel (fhat+ghat) t x = heatDuhamel fhat t x+heatDuhamel ghat t x
  exact heatDuhamel_add_of_bounded hFc hGc
    (fun p => by simpa only [Real.norm_eq_abs] using hFhat.2.1 p (Set.mem_univ _))
    (fun p => by simpa only [Real.norm_eq_abs] using hGhat.2.1 p (Set.mem_univ _)) ht.1 x

def constantHeatDuhamel {n : ℕ} (B : Space n ≃L[ℝ] Space n) (f : Point n → ℝ)
    (p : Point n) : ℝ := heatDuhamel (spaceTimePullback B f) p.2 (B.symm p.1)

theorem constantHeatDuhamel_smul {n : ℕ} (B : Space n ≃L[ℝ] Space n) (a : ℝ)
    (f : Point n → ℝ) (p : Point n) :
    constantHeatDuhamel B (a • f) p = a * constantHeatDuhamel B f p :=
  heatDuhamel_smul a (spaceTimePullback B f) p.2 (B.symm p.1)

theorem constantHeatDuhamel_add_of_bounded {n : ℕ} (B : Space n ≃L[ℝ] Space n)
    {F G : ℝ} {f g : Point n → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hF : ∀ p, |f p| ≤ F) (hG : ∀ p, |g p| ≤ G) (p : Point n) (ht : 0 ≤ p.2) :
    constantHeatDuhamel B (f+g) p = constantHeatDuhamel B f p+constantHeatDuhamel B g p := by
  have hB : Continuous (fun q : Point n => (B q.1,q.2)) :=
    (B.continuous.comp continuous_fst).prodMk continuous_snd
  exact heatDuhamel_add_of_bounded (hf.comp hB) (hg.comp hB)
    (fun q => hF (B q.1,q.2)) (fun q => hG (B q.1,q.2)) ht (B.symm p.1)

theorem constantHeatDuhamel_initial {n : ℕ} (B : Space n ≃L[ℝ] Space n)
    (f : Point n → ℝ) (x : Space n) : constantHeatDuhamel B f (x,0) = 0 :=
  heatDuhamel_zero (spaceTimePullback B f) (B.symm x)

theorem constantHeatDuhamel_schauderBound {n : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : Space n ≃L[ℝ] Space n) (T F : ℝ),
      0 < T → T ≤ 1 → ∀ f : Point n → ℝ,
      HolderBound α (cylinder Set.univ 0 T) f F →
      SchauderBound α (cylinder Set.univ 0 T) (constantHeatDuhamel B f)
        (C*F*(1+‖(B : Space n →L[ℝ] Space n)‖^α)*
          (1+‖(B.symm : Space n →L[ℝ] Space n)‖)^2*
          (1+‖(B.symm : Space n →L[ℝ] Space n)‖^α)) := by
  obtain ⟨C,hC,hEucl⟩ := heatDuhamel_schauder_solution (n := n) hα hα1
  refine ⟨C,hC,?_⟩
  intro B T F hT hT1 f hf
  have hg : HolderBound α (cylinder Set.univ 0 T) (spaceTimePullback B f)
      (F*(1+‖(B : Space n →L[ℝ] Space n)‖^α)) :=
    holderBound_comp_spaceLinearMap hα.le (B : Space n →L[ℝ] Space n) hf
  have hV := hEucl T (F*(1+‖(B : Space n →L[ℝ] Space n)‖^α)) hT hT1
    (spaceTimePullback B f) hg
  have hU := SchauderBound_spaceTimePullback hα.le B.symm hV.1
  have hFun : constantHeatDuhamel B f =
      spaceTimePullback B.symm (fun p => heatDuhamel (spaceTimePullback B f) p.2 p.1) := by
    funext p
    rfl
  rw [hFun]
  simpa only [mul_assoc] using hU

theorem constantHeatDuhamel_linearOp {n : ℕ} {α T F : ℝ} {A : Mat n}
    (B : Space n ≃L[ℝ] Space n)
    (hB : ∀ H : Space n →L[ℝ] Space n →L[ℝ] ℝ,
      (∑ k : Yau.RIdx n, H (B (Yau.realVec k)) (B (Yau.realVec k))) =
        ∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n, A i j*H (Yau.realVec i) (Yau.realVec j))
    {f : Point n → ℝ} (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (hf : HolderBound α (cylinder Set.univ 0 T) f F) {p : Point n}
    (hp : p ∈ cylinder Set.univ 0 T) :
    linearOp (cylinder Set.univ 0 T) (fun _ => A) (fun _ _ => 0)
      (constantHeatDuhamel B f) p = f p := by
  change linearOp (cylinder Set.univ 0 T) (fun _ => A) (fun _ _ => 0)
    (spaceTimePullback B.symm (fun q => heatDuhamel (spaceTimePullback B f) q.2 q.1)) p = _
  rw [linearOp_spaceTimePullback_constant B hB]
  have hg : HolderBound α (cylinder Set.univ 0 T) (spaceTimePullback B f)
      (F*(1+‖(B : Space n →L[ℝ] Space n)‖^α)) :=
    holderBound_comp_spaceLinearMap hα.le (B : Space n →L[ℝ] Space n) hf
  have hP : (B.symm p.1,p.2) ∈ cylinder Set.univ 0 T := ⟨Set.mem_univ _,hp.2⟩
  simpa only [spaceTimePullback,ContinuousLinearEquiv.apply_symm_apply,Prod.eta] using
    heatDuhamel_euclidean_linearOp hα hα1 hT hT1 hg (B.symm p.1,p.2) hP

theorem constantHeatDuhamel_add_of_holder {n : ℕ} (B : Space n ≃L[ℝ] Space n)
    {α F G T : ℝ} {f g : Point n → ℝ} (hα : 0 < α) (hT : 0 ≤ T)
    (hf : HolderBound α (cylinder Set.univ 0 T) f F)
    (hg : HolderBound α (cylinder Set.univ 0 T) g G)
    {p : Point n} (hp : p ∈ cylinder Set.univ 0 T) :
    constantHeatDuhamel B (f+g) p = constantHeatDuhamel B f p+constantHeatDuhamel B g p := by
  have hF := holderBound_comp_spaceLinearMap hα.le (B : Space n →L[ℝ] Space n) hf
  have hG := holderBound_comp_spaceLinearMap hα.le (B : Space n →L[ℝ] Space n) hg
  exact heatDuhamel_add_of_holder hα hT hF hG hp.2 (B.symm p.1)


theorem secondFDeriv_mul_apply {n : ℕ} {f g : Space n → ℝ} {x : Space n}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) (v w : Space n) :
    fderiv ℝ (fderiv ℝ (fun y => f y*g y)) x v w =
      f x*fderiv ℝ (fderiv ℝ g) x v w+
        fderiv ℝ f x v*fderiv ℝ g x w+
        fderiv ℝ f x w*fderiv ℝ g x v+
        g x*fderiv ℝ (fderiv ℝ f) x v w := by
  have hf1 : DifferentiableAt ℝ f x := hf.differentiableAt (by norm_num)
  have hg1 : DifferentiableAt ℝ g x := hg.differentiableAt (by norm_num)
  have hf2 : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hg2 : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hprod2 : DifferentiableAt ℝ (fderiv ℝ (fun y => f y*g y)) x :=
    ((hf.mul hg).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hleft : fderiv ℝ (fun y => fderiv ℝ (fun z => f z*g z) y w) x v =
      fderiv ℝ (fderiv ℝ (fun y => f y*g y)) x v w := by
    rw [fderiv_clm_apply hprod2 (differentiableAt_const w)]
    simp
  have heq : (fun y => fderiv ℝ (fun z => f z*g z) y w) =ᶠ[𝓝 x]
      (fun y => f y*fderiv ℝ g y w+g y*fderiv ℝ f y w) := by
    filter_upwards [hf.eventually (by norm_num),hg.eventually (by norm_num)] with y hfy hgy
    rw [fderiv_fun_mul (hfy.differentiableAt (by norm_num)) (hgy.differentiableAt (by norm_num))]
    simp
  have hdg : DifferentiableAt ℝ (fun y => fderiv ℝ g y w) x :=
    hg2.clm_apply (differentiableAt_const w)
  have hdf : DifferentiableAt ℝ (fun y => fderiv ℝ f y w) x :=
    hf2.clm_apply (differentiableAt_const w)
  have hAdd : fderiv ℝ (fun y => f y*fderiv ℝ g y w+g y*fderiv ℝ f y w) x =
      fderiv ℝ (fun y => f y*fderiv ℝ g y w) x+
        fderiv ℝ (fun y => g y*fderiv ℝ f y w) x :=
    fderiv_fun_add (hf1.fun_mul hdg) (hg1.fun_mul hdf)
  rw [← hleft,heq.fderiv_eq]
  rw [hAdd,fderiv_fun_mul hf1 hdg,
    fderiv_fun_mul hg1 hdf,fderiv_clm_apply hg2 (differentiableAt_const w),
    fderiv_clm_apply hf2 (differentiableAt_const w)]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,
    fderiv_const_apply,ContinuousLinearMap.comp_zero,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.zero_apply,mul_zero,add_zero,zero_add]
  ring

theorem timeD_spatial_mul {n : ℕ} (Q : Set (Point n)) (φ : Space n → ℝ)
    (u : Point n → ℝ) (p : Point n) :
    timeD Q (fun q => φ q.1*u q) p = φ p.1*timeD Q u p := by
  exact derivWithin_const_mul_field (φ p.1)

theorem linearOp_spatial_mul {n : ℕ} {Q : Set (Point n)} {a : Point n → Mat n}
    {b : Point n → Yau.RIdx n → ℝ} {φ : Space n → ℝ} {u : Point n → ℝ} {p : Point n}
    (hφ : ContDiffAt ℝ 2 φ p.1) (hu : ContDiffAt ℝ 2 (fun y => u (y,p.2)) p.1) :
    linearOp Q a b (fun q => φ q.1*u q) p = φ p.1*linearOp Q a b u p-
      (∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n, a p i j *
        (fderiv ℝ φ p.1 (Yau.realVec i)*spatialD u p (Yau.realVec j)+
          fderiv ℝ φ p.1 (Yau.realVec j)*spatialD u p (Yau.realVec i)+
          u p*fderiv ℝ (fderiv ℝ φ) p.1 (Yau.realVec i) (Yau.realVec j)))-
      u p*(∑ i : Yau.RIdx n, b p i*fderiv ℝ φ p.1 (Yau.realVec i)) := by
  have hD : spatialD (fun q => φ q.1*u q) p =
      φ p.1 • spatialD u p+u p • fderiv ℝ φ p.1 :=
    fderiv_fun_mul (hφ.differentiableAt (by norm_num)) (hu.differentiableAt (by norm_num))
  have hH (i j : Yau.RIdx n) :
      spatialDD (fun q => φ q.1*u q) p (Yau.realVec i) (Yau.realVec j) =
        φ p.1*spatialDD u p (Yau.realVec i) (Yau.realVec j)+
          fderiv ℝ φ p.1 (Yau.realVec i)*spatialD u p (Yau.realVec j)+
          fderiv ℝ φ p.1 (Yau.realVec j)*spatialD u p (Yau.realVec i)+
          u p*fderiv ℝ (fderiv ℝ φ) p.1 (Yau.realVec i) (Yau.realVec j) :=
    secondFDeriv_mul_apply hφ hu _ _
  simp only [linearOp,timeD_spatial_mul,hD,hH,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,smul_eq_mul]
  simp only [mul_add,mul_sub,add_mul,sub_mul,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    Finset.mul_sum,Finset.sum_mul]
  simp only [mul_assoc,mul_left_comm,mul_comm]
  ring

theorem secondFDeriv_mul {n : ℕ} {f g : Space n → ℝ} {x : Space n}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    fderiv ℝ (fderiv ℝ (fun y => f y*g y)) x =
      f x • fderiv ℝ (fderiv ℝ g) x+
        (fderiv ℝ f x).smulRight (fderiv ℝ g x)+
        (fderiv ℝ g x).smulRight (fderiv ℝ f x)+
        g x • fderiv ℝ (fderiv ℝ f) x := by
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  rw [secondFDeriv_mul_apply hf hg]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply,smul_eq_mul]
  ring

theorem c2_spatial_mul {n : ℕ} {Q : Set (Point n)} {φ : Space n → ℝ} {u : Point n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hu : C2 Q u) : C2 Q (fun p => φ p.1*u p) := by
  have hφc : Continuous (fun p : Point n => φ p.1) := hφ.continuous.comp continuous_fst
  have hφD : Continuous (fun p : Point n => fderiv ℝ φ p.1) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).continuous.comp continuous_fst
  have hφH : Continuous (fun p : Point n => fderiv ℝ (fderiv ℝ φ) p.1) :=
    ((hφ.fderiv_right (m := 1) (by norm_num)).fderiv_right
      (m := 0) (by norm_num)).continuous.comp continuous_fst
  have hD (p : Point n) (hp : p ∈ Q) : spatialD (fun q => φ q.1*u q) p =
      φ p.1 • spatialD u p+u p • fderiv ℝ φ p.1 :=
    fderiv_fun_mul (hφ.differentiable (by norm_num) p.1)
      ((hu.2.2.2.2.1 p hp).differentiableAt (by norm_num))
  have hH (p : Point n) (hp : p ∈ Q) : spatialDD (fun q => φ q.1*u q) p =
      φ p.1 • spatialDD u p+
        (fderiv ℝ φ p.1).smulRight (spatialD u p)+
        (spatialD u p).smulRight (fderiv ℝ φ p.1)+
        u p • fderiv ℝ (fderiv ℝ φ) p.1 :=
    secondFDeriv_mul hφ.contDiffAt (hu.2.2.2.2.1 p hp)
  have hTensor : Continuous (fun z : (Space n →L[ℝ] ℝ) × (Space n →L[ℝ] ℝ) =>
      z.1.smulRight z.2) :=
    (isBoundedBilinearMap_smulRight : IsBoundedBilinearMap ℝ
      (fun z : (Space n →L[ℝ] ℝ) × (Space n →L[ℝ] ℝ) => z.1.smulRight z.2)).continuous
  refine ⟨hφc.continuousOn.mul hu.1,?_,?_,?_,?_,?_⟩
  · exact ((hφc.continuousOn.smul hu.2.1).add (hu.1.smul hφD.continuousOn)).congr hD
  · have hC1 := hTensor.comp_continuousOn (hφD.continuousOn.prodMk hu.2.1)
    have hC2 := hTensor.comp_continuousOn (hu.2.1.prodMk hφD.continuousOn)
    exact ((((hφc.continuousOn.smul hu.2.2.1).add hC1).add hC2).add
      (hu.1.smul hφH.continuousOn)).congr hH
  · exact (hφc.continuousOn.mul hu.2.2.2.1).congr (fun p _ => timeD_spatial_mul Q φ u p)
  · intro p hp
    exact hφ.contDiffAt.mul (hu.2.2.2.2.1 p hp)
  · intro p hp
    exact (differentiableWithinAt_const (φ p.1)).mul (hu.2.2.2.2.2 p hp)

theorem c2_add {n : ℕ} {Q : Set (Point n)} {u v : Point n → ℝ}
    (hu : C2 Q u) (hv : C2 Q v) : C2 Q (fun p => u p+v p) := by
  have h := c2_sub hu (c2_sub (c2_zero Q) hv)
  simpa only [zero_sub,sub_neg_eq_add] using h

theorem linearOp_add {n : ℕ} {Q : Set (Point n)}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {u v : Point n → ℝ}
    (hu : C2 Q u) (hv : C2 Q v) {p : Point n} (hp : p ∈ Q) :
    linearOp Q a b (fun q => u q+v q) p = linearOp Q a b u p+linearOp Q a b v p := by
  have hn := linearOp_sub (a := a) (b := b) (c2_zero Q) hv hp
  simp only [linearOp_zero,zero_sub] at hn
  have h := linearOp_sub (a := a) (b := b) hu (c2_sub (c2_zero Q) hv) hp
  simpa only [zero_sub,sub_neg_eq_add,hn] using h

theorem c2_sum {n : ℕ} {ι : Type*} (s : Finset ι) {Q : Set (Point n)}
    {u : ι → Point n → ℝ} (hu : ∀ i ∈ s, C2 Q (u i)) :
    C2 Q (fun p => ∑ i ∈ s, u i p) := by
  classical
  revert hu
  induction s using Finset.induction_on with
  | empty => intro hu; simpa only [Finset.sum_empty] using c2_zero Q
  | @insert i s hi ih =>
    intro hu
    have hs : C2 Q (fun p => ∑ j ∈ s, u j p) := ih (fun j hj => hu j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert hi] using c2_add (hu i (Finset.mem_insert_self i s)) hs

theorem linearOp_sum {n : ℕ} {ι : Type*} (s : Finset ι) {Q : Set (Point n)}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {u : ι → Point n → ℝ}
    (hu : ∀ i ∈ s, C2 Q (u i)) {p : Point n} (hp : p ∈ Q) :
    linearOp Q a b (fun q => ∑ i ∈ s, u i q) p = ∑ i ∈ s, linearOp Q a b (u i) p := by
  classical
  revert hu
  induction s using Finset.induction_on with
  | empty => intro hu; simp only [Finset.sum_empty,linearOp_zero]
  | @insert i s hi ih =>
    intro hu
    have hs : ∀ j ∈ s, C2 Q (u j) := fun j hj => hu j (Finset.mem_insert_of_mem hj)
    simp only [Finset.sum_insert hi]
    rw [linearOp_add (hu i (Finset.mem_insert_self i s)) (c2_sum s hs) hp,ih hs]

def frozenPatchResidual {n : ℕ} (Q : Set (Point n)) (a : Point n → Mat n)
    (b : Point n → Yau.RIdx n → ℝ) (A : Mat n) (φ : Space n → ℝ) (v : Point n → ℝ)
    (p : Point n) : ℝ :=
  φ p.1*(∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n,
    (A i j-a p i j)*spatialDD v p (Yau.realVec i) (Yau.realVec j))-
  φ p.1*(∑ i : Yau.RIdx n, b p i*spatialD v p (Yau.realVec i))-
  (∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n, a p i j *
    (fderiv ℝ φ p.1 (Yau.realVec i)*spatialD v p (Yau.realVec j)+
      fderiv ℝ φ p.1 (Yau.realVec j)*spatialD v p (Yau.realVec i)+
      v p*fderiv ℝ (fderiv ℝ φ) p.1 (Yau.realVec i) (Yau.realVec j)))-
  v p*(∑ i : Yau.RIdx n, b p i*fderiv ℝ φ p.1 (Yau.realVec i))

theorem linearOp_change_coefficients {n : ℕ} (Q : Set (Point n)) (a : Point n → Mat n)
    (b : Point n → Yau.RIdx n → ℝ) (A : Mat n) (v : Point n → ℝ) (p : Point n) :
    linearOp Q a b v p = linearOp Q (fun _ => A) (fun _ _ => 0) v p+
      (∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n,
        (A i j-a p i j)*spatialDD v p (Yau.realVec i) (Yau.realVec j))-
      ∑ i : Yau.RIdx n, b p i*spatialD v p (Yau.realVec i) := by
  simp only [linearOp,zero_mul,Finset.sum_const_zero,sub_zero,sub_mul,Finset.sum_sub_distrib]
  ring

theorem linearOp_frozen_patch {n : ℕ} {Q : Set (Point n)} {a : Point n → Mat n}
    {b : Point n → Yau.RIdx n → ℝ} {A : Mat n} {φ : Space n → ℝ} {v : Point n → ℝ}
    {p : Point n} (hφ : ContDiffAt ℝ 2 φ p.1)
    (hv : ContDiffAt ℝ 2 (fun y => v (y,p.2)) p.1) :
    linearOp Q a b (fun q => φ q.1*v q) p =
      φ p.1*linearOp Q (fun _ => A) (fun _ _ => 0) v p+
        frozenPatchResidual Q a b A φ v p := by
  rw [linearOp_spatial_mul hφ hv,linearOp_change_coefficients Q a b A v p]
  dsimp [frozenPatchResidual]
  ring

def finiteParametrix {n : ℕ} {ι : Type*} (s : Finset ι) (φ : ι → Space n → ℝ)
    (v : ι → Point n → ℝ) (p : Point n) : ℝ := ∑ i ∈ s, φ i p.1*v i p

theorem finiteParametrix_C2 {n : ℕ} {ι : Type*} (s : Finset ι) {Q : Set (Point n)}
    {φ : ι → Space n → ℝ} {v : ι → Point n → ℝ}
    (hφ : ∀ i ∈ s, ContDiff ℝ 2 (φ i)) (hv : ∀ i ∈ s, C2 Q (v i)) :
    C2 Q (finiteParametrix s φ v) :=
  c2_sum s (fun i hi => c2_spatial_mul (hφ i hi) (hv i hi))

theorem finiteParametrix_linearOp {n : ℕ} {ι : Type*} (s : Finset ι)
    {Q : Set (Point n)} {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    {A : ι → Mat n} {φ ψ : ι → Space n → ℝ} {v : ι → Point n → ℝ} {f : Point n → ℝ}
    (hφ : ∀ i ∈ s, ContDiff ℝ 2 (φ i)) (hv : ∀ i ∈ s, C2 Q (v i))
    (hPDE : ∀ i ∈ s, ∀ p ∈ Q,
      linearOp Q (fun _ => A i) (fun _ _ => 0) (v i) p = ψ i p.1*f p)
    (hPartition : ∀ p ∈ Q, (∑ i ∈ s, φ i p.1*ψ i p.1) = 1)
    {p : Point n} (hp : p ∈ Q) :
    linearOp Q a b (finiteParametrix s φ v) p = f p+
      ∑ i ∈ s, frozenPatchResidual Q a b (A i) (φ i) (v i) p := by
  change linearOp Q a b (fun q => ∑ i ∈ s, φ i q.1*v i q) p = _
  rw [linearOp_sum s (fun i hi => c2_spatial_mul (hφ i hi) (hv i hi)) hp]
  calc
    _ = ∑ i ∈ s, (φ i p.1*(ψ i p.1*f p)+frozenPatchResidual Q a b (A i) (φ i) (v i) p) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [linearOp_frozen_patch (hφ i hi).contDiffAt ((hv i hi).2.2.2.2.1 p hp),hPDE i hi p hp]
    _ = f p+∑ i ∈ s, frozenPatchResidual Q a b (A i) (φ i) (v i) p := by
      rw [Finset.sum_add_distrib]
      congr 1
      simp only [← mul_assoc,← Finset.sum_mul,hPartition p hp,one_mul]


def quadraticBarrierSpace {n : ℕ} (x : Space n) : ℝ := 1+‖x‖^2

theorem quadraticBarrierSpace_contDiff {n : ℕ} :
    ContDiff ℝ ∞ (quadraticBarrierSpace (n := n)) :=
  contDiff_const.add (contDiff_id.norm_sq ℝ)

set_option backward.isDefEq.respectTransparency.types false in
theorem quadraticBarrierSpace_fderiv {n : ℕ} :
    fderiv ℝ (quadraticBarrierSpace (n := n)) =
      fun x => (2 : ℝ) • innerSL ℝ x := by
  funext x
  have hNorm : HasFDerivAt (fun y : Space n => ‖y‖^2) ((2 : ℝ) • innerSL ℝ x) x := by
    simpa only [two_smul] using (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  change fderiv ℝ ((fun _ : Space n => (1 : ℝ))+(fun y => ‖y‖^2)) x = _
  simpa only [zero_add] using
    ((hasFDerivAt_const (1 : ℝ) x).add hNorm).fderiv

set_option backward.isDefEq.respectTransparency.types false in
theorem quadraticBarrierSpace_secondFDeriv {n : ℕ} :
    fderiv ℝ (fderiv ℝ (quadraticBarrierSpace (n := n))) =
      fun _ => (2 : ℝ) • realInnerBilinear (n := n) := by
  rw [quadraticBarrierSpace_fderiv]
  have hFun : (fun x : Space n => (2 : ℝ) • innerSL ℝ x) =
      fun x : Space n => (2 : ℝ) • realInnerBilinear x := by
    funext x
    ext v
    rfl
  rw [hFun]
  funext x
  exact ((realInnerBilinear (n := n)).hasFDerivAt.const_smul (2 : ℝ)).fderiv

theorem realCoord_abs_le_norm {n : ℕ} (x : Space n) (i : Yau.RIdx n) :
    |Yau.realCoord x i| ≤ ‖x‖ := by
  simpa only [real_inner_realVec,realVec_norm,mul_one] using
    abs_real_inner_le_norm x (Yau.realVec i)

def barrierTime (δ K : ℝ) (p : Point n) : ℝ := δ*Real.exp (K*p.2)

theorem barrierTime_hasDerivAt {n : ℕ} (δ K : ℝ) (x : Space n) (t : ℝ) :
    HasDerivAt (fun s => barrierTime δ K (x,s)) (δ*K*Real.exp (K*t)) t := by
  change HasDerivAt (fun s : ℝ => δ*Real.exp (K*s)) (δ*K*Real.exp (K*t)) t
  convert (((hasDerivAt_id t).const_mul K).exp.const_mul δ) using 1 <;> simp only [id_eq]
  ring

theorem barrierTime_spatialD {n : ℕ} (δ K : ℝ) :
    spatialD (barrierTime (n := n) δ K) = 0 := by
  funext p
  simp only [spatialD,barrierTime,fderiv_const_apply,Pi.zero_apply]

theorem barrierTime_spatialDD {n : ℕ} (δ K : ℝ) :
    spatialDD (barrierTime (n := n) δ K) = 0 := by
  funext p
  simp only [spatialDD,barrierTime,fderiv_const_apply,Pi.zero_apply]

theorem barrierTime_timeD {n : ℕ} {S : Set (Space n)} {T : ℝ} (hT : 0 < T)
    (δ K : ℝ) {p : Point n} (hp : p ∈ cylinder S 0 T) :
    timeD (cylinder S 0 T) (barrierTime δ K) p = δ*K*Real.exp (K*p.2) := by
  have hFiber : {t | (p.1,t) ∈ cylinder S 0 T} = Set.Icc 0 T := by
    ext t
    simp [Yau.Parabolic.cylinder,hp.1]
  simp only [timeD,hFiber]
  exact (barrierTime_hasDerivAt δ K p.1 p.2).hasDerivWithinAt.derivWithin
    (uniqueDiffOn_Icc hT p.2 hp.2)

theorem barrierTime_C2 {n : ℕ} {S : Set (Space n)} {T : ℝ} (hT : 0 < T) (δ K : ℝ) :
    C2 (cylinder S 0 T) (barrierTime δ K) := by
  have hCont : Continuous (barrierTime (n := n) δ K) := by
    unfold barrierTime
    fun_prop
  have hTimeCont : Continuous (fun p : Point n => δ*K*Real.exp (K*p.2)) := by fun_prop
  refine ⟨hCont.continuousOn,?_,?_,?_,?_,?_⟩
  · rw [barrierTime_spatialD]
    exact continuousOn_const
  · rw [barrierTime_spatialDD]
    exact continuousOn_const
  · exact hTimeCont.continuousOn.congr (fun p hp => barrierTime_timeD hT δ K hp)
  · intro p _
    change ContDiffAt ℝ 2 (fun _ : Space n => δ*Real.exp (K*p.2)) p.1
    exact contDiffAt_const
  · intro p _
    exact (barrierTime_hasDerivAt δ K p.1 p.2).differentiableAt.differentiableWithinAt

theorem timeD_cylinder_restrict_space {n : ℕ} {S : Set (Space n)} {T : ℝ}
    (u : Point n → ℝ) {p : Point n} (hp : p ∈ cylinder S 0 T) :
    timeD (cylinder S 0 T) u p = timeD (cylinder Set.univ 0 T) u p := by
  have hFiber : {t | (p.1,t) ∈ cylinder S 0 T} =
      {t | (p.1,t) ∈ cylinder Set.univ 0 T} := by
    ext t
    simp [Yau.Parabolic.cylinder,hp.1]
  simp only [timeD,hFiber]

theorem c2_cylinder_restrict_space {n : ℕ} {S : Set (Space n)} {T : ℝ}
    {u : Point n → ℝ} (hu : C2 (cylinder Set.univ 0 T) u) :
    C2 (cylinder S 0 T) u := by
  have hSub : cylinder S 0 T ⊆ cylinder Set.univ 0 T := by
    intro p hp
    exact ⟨Set.mem_univ _,hp.2⟩
  refine ⟨hu.1.mono hSub,hu.2.1.mono hSub,hu.2.2.1.mono hSub,?_,
    fun p hp => hu.2.2.2.2.1 p (hSub hp),?_⟩
  · exact (hu.2.2.2.1.mono hSub).congr
      (fun p hp => timeD_cylinder_restrict_space u hp)
  · intro p hp
    exact (hu.2.2.2.2.2 p (hSub hp)).mono (fun t ht => hSub ht)

theorem linearOp_cylinder_restrict_space {n : ℕ} {S : Set (Space n)} {T : ℝ}
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ) (u : Point n → ℝ)
    {p : Point n} (hp : p ∈ cylinder S 0 T) :
    linearOp (cylinder S 0 T) a b u p = linearOp (cylinder Set.univ 0 T) a b u p := by
  simp only [linearOp,timeD_cylinder_restrict_space u hp]

def quadraticBarrier {n : ℕ} (δ K : ℝ) (p : Point n) : ℝ :=
  barrierTime δ K p*quadraticBarrierSpace p.1

theorem quadraticBarrier_C2 {n : ℕ} {S : Set (Space n)} {T : ℝ} (hT : 0 < T)
    (δ K : ℝ) : C2 (cylinder S 0 T) (quadraticBarrier δ K) := by
  change C2 (cylinder S 0 T) (fun p => barrierTime δ K p*quadraticBarrierSpace p.1)
  simpa only [mul_comm] using c2_spatial_mul
    (quadraticBarrierSpace_contDiff.of_le (by simp)) (barrierTime_C2 hT δ K (S := S))

theorem quadraticBarrier_spatialD {n : ℕ} (δ K : ℝ) (p : Point n) :
    spatialD (quadraticBarrier δ K) p =
      barrierTime δ K p • fderiv ℝ quadraticBarrierSpace p.1 := by
  change fderiv ℝ (barrierTime δ K p • quadraticBarrierSpace) p.1 = _
  exact congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := quadraticBarrierSpace)
    (barrierTime δ K p)) p.1

theorem quadraticBarrier_spatialDD {n : ℕ} (δ K : ℝ) (p : Point n) :
    spatialDD (quadraticBarrier δ K) p =
      barrierTime δ K p • fderiv ℝ (fderiv ℝ quadraticBarrierSpace) p.1 := by
  change fderiv ℝ (fderiv ℝ (barrierTime δ K p • quadraticBarrierSpace)) p.1 = _
  rw [fderiv_const_smul_field (𝕜 := ℝ) (f := quadraticBarrierSpace),
    fderiv_const_smul_field (𝕜 := ℝ) (f := fderiv ℝ quadraticBarrierSpace)]
  rfl

theorem quadraticBarrier_timeD {n : ℕ} {S : Set (Space n)} {T : ℝ} (hT : 0 < T)
    (δ K : ℝ) {p : Point n} (hp : p ∈ cylinder S 0 T) :
    timeD (cylinder S 0 T) (quadraticBarrier δ K) p =
      (δ*K*Real.exp (K*p.2))*quadraticBarrierSpace p.1 := by
  have hFiber : {t | (p.1,t) ∈ cylinder S 0 T} = Set.Icc 0 T := by
    ext t
    simp [Yau.Parabolic.cylinder,hp.1]
  simp only [timeD,hFiber]
  exact ((barrierTime_hasDerivAt δ K p.1 p.2).mul_const
    (quadraticBarrierSpace p.1)).hasDerivWithinAt.derivWithin
      (uniqueDiffOn_Icc hT p.2 hp.2)

theorem quadraticBarrier_linearOp {n : ℕ} {S : Set (Space n)} {T : ℝ} (hT : 0 < T)
    (δ K : ℝ) (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
    {p : Point n} (hp : p ∈ cylinder S 0 T) :
    linearOp (cylinder S 0 T) a b (quadraticBarrier δ K) p =
      barrierTime δ K p*(K*quadraticBarrierSpace p.1-
        2*(∑ i, a p i i)-2*(∑ i, b p i*Yau.realCoord p.1 i)) := by
  classical
  have hTrace : (∑ i, a p i i*(barrierTime δ K p*2)) =
      barrierTime δ K p*2*(∑ i, a p i i) := by
    rw [← Finset.sum_mul]
    ring
  have hDrift : (∑ i, b p i*(barrierTime δ K p*(2*Yau.realCoord p.1 i))) =
      barrierTime δ K p*2*(∑ i, b p i*Yau.realCoord p.1 i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [linearOp,quadraticBarrier_timeD hT δ K hp,
    quadraticBarrier_spatialD,quadraticBarrier_spatialDD]
  rw [quadraticBarrierSpace_secondFDeriv,quadraticBarrierSpace_fderiv]
  simp only [smul_apply,smul_eq_mul,realInnerBilinear_apply,innerSL_apply_apply]
  simp only [realVec_inner]
  simp only [real_inner_realVec,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rw [hTrace,hDrift]
  dsimp only [barrierTime]
  ring

theorem elliptic_diagonal_upper {n : ℕ} {Q : Set (Point n)} {a : Point n → Mat n}
    {lam upper : ℝ} (hEll : Elliptic Q a lam upper) {p : Point n} (hp : p ∈ Q)
    (i : Yau.RIdx n) : a p i i ≤ upper := by
  classical
  have h := ((hEll.2.2 p hp).2 (Pi.single i (1 : ℝ))).2
  simpa [Pi.single_apply,mul_ite,ite_mul] using h

theorem elliptic_trace_upper {n : ℕ} {Q : Set (Point n)} {a : Point n → Mat n}
    {lam upper : ℝ} (hEll : Elliptic Q a lam upper) {p : Point n} (hp : p ∈ Q) :
    (∑ i, a p i i) ≤ (Fintype.card (Yau.RIdx n) : ℝ)*upper := by
  calc
    _ ≤ ∑ _i : Yau.RIdx n, upper :=
      Finset.sum_le_sum (fun i _ => elliptic_diagonal_upper hEll hp i)
    _ = _ := by simp

theorem drift_quadratic_upper {n : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (b : Point n → Yau.RIdx n → ℝ) (p : Point n) (hb : ∀ i, |b p i| ≤ M) :
    (∑ i, b p i*Yau.realCoord p.1 i) ≤
      (Fintype.card (Yau.RIdx n) : ℝ)*M*quadraticBarrierSpace p.1 := by
  have hNorm : ‖p.1‖ ≤ quadraticBarrierSpace p.1 := by
    dsimp only [quadraticBarrierSpace]
    nlinarith [sq_nonneg (‖p.1‖-(1/2 : ℝ))]
  calc
    _ ≤ ∑ _i : Yau.RIdx n, M*quadraticBarrierSpace p.1 := by
      apply Finset.sum_le_sum
      intro i _
      calc
        b p i*Yau.realCoord p.1 i ≤ |b p i*Yau.realCoord p.1 i| := le_abs_self _
        _ = |b p i| * |Yau.realCoord p.1 i| := abs_mul _ _
        _ ≤ M*quadraticBarrierSpace p.1 :=
          mul_le_mul (hb i) ((realCoord_abs_le_norm p.1 i).trans hNorm) (abs_nonneg _) hM
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

def barrierGrowthRate (n : ℕ) (upper M : ℝ) : ℝ :=
  1+2*(Fintype.card (Yau.RIdx n) : ℝ)*(upper+M)

theorem barrierGrowthRate_nonneg (n : ℕ) {upper M : ℝ} (hUpper : 0 ≤ upper)
    (hM : 0 ≤ M) : 0 ≤ barrierGrowthRate n upper M := by
  dsimp only [barrierGrowthRate]
  positivity

theorem quadraticBarrier_linearOp_pos {n : ℕ} {S : Set (Space n)} {T lam upper M : ℝ}
    (hT : 0 < T) {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (hEll : Elliptic (cylinder S 0 T) a lam upper) (hM : 0 ≤ M)
    (hb : ∀ p ∈ cylinder S 0 T, ∀ i, |b p i| ≤ M) {δ : ℝ} (hδ : 0 < δ)
    {p : Point n} (hp : p ∈ cylinder S 0 T) :
    0 < linearOp (cylinder S 0 T) a b
      (quadraticBarrier δ (barrierGrowthRate n upper M)) p := by
  have hUpper : 0 ≤ upper := hEll.1.le.trans hEll.2.1
  have hQuad : 1 ≤ quadraticBarrierSpace p.1 := by
    dsimp only [quadraticBarrierSpace]
    linarith [sq_nonneg ‖p.1‖]
  have hTrace : (∑ i, a p i i) ≤
      (Fintype.card (Yau.RIdx n) : ℝ)*upper*quadraticBarrierSpace p.1 :=
    (elliptic_trace_upper hEll hp).trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hQuad
        (mul_nonneg (Nat.cast_nonneg _) hUpper))
  have hDrift := drift_quadratic_upper hM b p (hb p hp)
  have hBracket : 1 ≤ barrierGrowthRate n upper M*quadraticBarrierSpace p.1-
      2*(∑ i, a p i i)-2*(∑ i, b p i*Yau.realCoord p.1 i) := by
    dsimp only [barrierGrowthRate]
    nlinarith
  rw [quadraticBarrier_linearOp hT δ (barrierGrowthRate n upper M) a b hp]
  have hPref : 0 < barrierTime δ (barrierGrowthRate n upper M) p :=
    mul_pos hδ (Real.exp_pos _)
  exact hPref.trans_le (by simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hBracket hPref.le)

theorem elliptic_mono {n : ℕ} {Q S : Set (Point n)} {a : Point n → Mat n}
    {lam upper : ℝ} (hEll : Elliptic Q a lam upper) (hSQ : S ⊆ Q) :
    Elliptic S a lam upper :=
  ⟨hEll.1,hEll.2.1,fun p hp => hEll.2.2 p (hSQ hp)⟩

/-- Whole-space comparison follows by exhausting with balls and using a
quadratic barrier. Only boundedness of the solution and drift is needed. -/
theorem bounded_wholeSpace_subsolution_bound {n : ℕ} {T lam upper M B F : ℝ}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {u : Point n → ℝ}
    (hT : 0 < T) (hu : C2 (cylinder Set.univ 0 T) u)
    (hEll : Elliptic (cylinder Set.univ 0 T) a lam upper) (hM : 0 ≤ M)
    (hb : ∀ p ∈ cylinder Set.univ 0 T, ∀ i, |b p i| ≤ M)
    (hBound : ∀ p ∈ cylinder Set.univ 0 T, u p ≤ B)
    (hInit : ∀ x, u (x,0) ≤ 0) (hF : 0 ≤ F)
    (hOp : ∀ p ∈ Set.univ ×ˢ Set.Ioc 0 T,
      linearOp (cylinder Set.univ 0 T) a b u p ≤ F) :
    ∀ p ∈ cylinder Set.univ 0 T, u p ≤ p.2*F := by
  intro p hp
  by_contra hn
  have hPos : 0 < u p-p.2*F := sub_pos.mpr (lt_of_not_ge hn)
  let K : ℝ := barrierGrowthRate n upper M
  have hK : 0 ≤ K := barrierGrowthRate_nonneg n (hEll.1.le.trans hEll.2.1) hM
  let ρ : ℝ := quadraticBarrier 1 K p
  have hρ : 0 < ρ := by
    dsimp only [ρ,quadraticBarrier,barrierTime,quadraticBarrierSpace]
    positivity
  let δ : ℝ := (u p-p.2*F)/(2*ρ)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδeq : quadraticBarrier δ K p = (u p-p.2*F)/2 := by
    have hScale : quadraticBarrier δ K p = δ*ρ := by
      dsimp only [quadraticBarrier,barrierTime,ρ]
      ring
    rw [hScale]
    dsimp only [δ]
    field_simp
  let B' : ℝ := max B 0
  have hB' : 0 ≤ B' := le_max_right _ _
  let R : ℝ := ‖p.1‖+1+B'/δ
  have hR1 : 1 ≤ R := by
    dsimp only [R]
    linarith [norm_nonneg p.1,div_nonneg hB' hδ.le]
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hpR : ‖p.1‖ < R := by
    dsimp only [R]
    linarith [div_nonneg hB' hδ.le]
  have hBR : B' ≤ δ*R^2 := by
    have hRdiv : B'/δ ≤ R := by dsimp only [R]; linarith [norm_nonneg p.1]
    have hRSq : R ≤ R^2 := by nlinarith
    have h := (div_le_iff₀ hδ).mp (hRdiv.trans hRSq)
    nlinarith
  let O : Set (Space n) := Metric.ball 0 R
  have hCompact : IsCompact (closure O) := by
    dsimp only [O]
    rw [closure_ball _ hR.ne']
    exact isCompact_closedBall _ _
  have hSub : cylinder (closure O) 0 T ⊆ cylinder Set.univ 0 T := by
    intro q hq
    exact ⟨Set.mem_univ _,hq.2⟩
  have huLoc := c2_cylinder_restrict_space (S := closure O) hu
  have hBarLoc := quadraticBarrier_C2 (S := closure O) hT δ K
  have hLift := c2_add_const (c2_sub_timeAffine hT huLoc F) F
  let w : Point n → ℝ := fun q => ((u q-F*(q.2+1))+F)-quadraticBarrier δ K q
  have hw : C2 (cylinder (closure O) 0 T) w := c2_sub hLift hBarLoc
  have hWInit : ∀ x ∈ closure O, w (x,0) ≤ 0 := by
    intro x _
    have hBar : 0 ≤ quadraticBarrier δ K (x,0) := by
      dsimp only [quadraticBarrier,barrierTime,quadraticBarrierSpace]
      positivity
    dsimp only [w]
    simp only [zero_add,mul_one]
    linarith [hInit x]
  have hWLat : ∀ x ∈ frontier O, ∀ t ∈ Set.Icc 0 T, w (x,t) ≤ 0 := by
    intro x hx t ht
    have hxR : ‖x‖ = R := by
      simpa only [Metric.mem_sphere,dist_zero_right] using Metric.frontier_ball_subset_sphere hx
    have hExp : 1 ≤ Real.exp (K*t) := Real.one_le_exp_iff.mpr (mul_nonneg hK ht.1)
    have hQuad0 : 0 ≤ quadraticBarrierSpace x := by dsimp only [quadraticBarrierSpace]; positivity
    have hBar : B' ≤ quadraticBarrier δ K (x,t) := by
      calc
        B' ≤ δ*R^2 := hBR
        _ ≤ δ*quadraticBarrierSpace x :=
          mul_le_mul_of_nonneg_left (by dsimp only [quadraticBarrierSpace]; rw [hxR]; linarith) hδ.le
        _ = δ*1*quadraticBarrierSpace x := by ring
        _ ≤ δ*Real.exp (K*t)*quadraticBarrierSpace x :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hExp hδ.le) hQuad0
        _ = quadraticBarrier δ K (x,t) := rfl
    have hUB : u (x,t) ≤ B' := (hBound (x,t) ⟨Set.mem_univ _,ht⟩).trans (le_max_left _ _)
    have htF : 0 ≤ t*F := mul_nonneg ht.1 hF
    dsimp only [w]
    linarith
  have hWOp : ∀ q ∈ O ×ˢ Set.Ioc 0 T,
      linearOp (cylinder (closure O) 0 T) a b w q ≤ 0 := by
    intro q hq
    have hqLoc : q ∈ cylinder (closure O) 0 T :=
      ⟨subset_closure hq.1,hq.2.1.le,hq.2.2⟩
    have hqUniv := hSub hqLoc
    dsimp only [w]
    rw [linearOp_sub (a := a) (b := b) hLift hBarLoc hqLoc,linearOp_add_const,
      linearOp_sub_timeAffine hT huLoc F hqLoc,
      linearOp_cylinder_restrict_space a b u hqLoc,
      linearOp_cylinder_restrict_space a b (quadraticBarrier δ K) hqLoc]
    have hBarOp := quadraticBarrier_linearOp_pos hT hEll hM hb hδ hqUniv
    have hUOp := hOp q ⟨Set.mem_univ _,hq.2⟩
    change 0 < linearOp (cylinder Set.univ 0 T) a b (quadraticBarrier δ K) q at hBarOp
    linarith
  have hMax := maximum_principle (O := O) Metric.isOpen_ball hCompact hT hw
    (elliptic_mono hEll hSub) hWInit hWLat hWOp
  have hpLoc : p ∈ cylinder (closure O) 0 T := by
    refine ⟨subset_closure ?_,hp.2⟩
    simpa only [O,Metric.mem_ball,dist_zero_right] using hpR
  have h := hMax p hpLoc
  dsimp only [w] at h
  rw [hδeq] at h
  linarith

/-- The sup residual estimate used to identify spatial derivatives by
uniform convergence, without convergence in the full Holder norm. -/
theorem bounded_wholeSpace_residual_bound {n : ℕ} {T lam upper M B F : ℝ}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {u : Point n → ℝ}
    (hT : 0 < T) (hu : C2 (cylinder Set.univ 0 T) u)
    (hEll : Elliptic (cylinder Set.univ 0 T) a lam upper) (hM : 0 ≤ M)
    (hb : ∀ p ∈ cylinder Set.univ 0 T, ∀ i, |b p i| ≤ M)
    (hBound : ∀ p ∈ cylinder Set.univ 0 T, |u p| ≤ B)
    (hInit : ∀ x, u (x,0) = 0) (hF : 0 ≤ F)
    (hOp : ∀ p ∈ Set.univ ×ˢ Set.Ioc 0 T,
      |linearOp (cylinder Set.univ 0 T) a b u p| ≤ F) :
    ∀ p ∈ cylinder Set.univ 0 T, |u p| ≤ p.2*F := by
  have hUp := bounded_wholeSpace_subsolution_bound hT hu hEll hM hb
    (fun p hp => (le_abs_self _).trans (hBound p hp))
    (fun x => (hInit x).le) hF (fun p hp => (le_abs_self _).trans (hOp p hp))
  have hNegC2 : C2 (cylinder Set.univ 0 T) (fun p => -u p) := by
    simpa only [zero_sub] using c2_sub (c2_zero (cylinder Set.univ 0 T)) hu
  have hNegOp : ∀ p ∈ cylinder Set.univ 0 T,
      linearOp (cylinder Set.univ 0 T) a b (fun q => -u q) p =
        -linearOp (cylinder Set.univ 0 T) a b u p := by
    intro p hp
    simpa only [zero_sub,linearOp_zero] using
      linearOp_sub (a := a) (b := b) (c2_zero (cylinder Set.univ 0 T)) hu hp
  have hNeg := bounded_wholeSpace_subsolution_bound hT hNegC2 hEll hM hb
    (fun p hp => (neg_le_abs _).trans (hBound p hp))
    (fun x => by simpa only [hInit x,neg_zero] using (le_rfl : (0 : ℝ) ≤ 0)) hF (by
      intro p hp
      rw [hNegOp p ⟨Set.mem_univ _,hp.2.1.le,hp.2.2⟩]
      exact (neg_le_abs _).trans (hOp p hp))
  intro p hp
  exact abs_le.mpr ⟨by linarith [hNeg p hp],hUp p hp⟩

theorem bounded_wholeSpace_unique {n : ℕ} {T lam upper M B C : ℝ}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {u v : Point n → ℝ}
    (hT : 0 < T) (hu : C2 (cylinder Set.univ 0 T) u)
    (hv : C2 (cylinder Set.univ 0 T) v)
    (hEll : Elliptic (cylinder Set.univ 0 T) a lam upper) (hM : 0 ≤ M)
    (hb : ∀ p ∈ cylinder Set.univ 0 T, ∀ i, |b p i| ≤ M)
    (hUBound : ∀ p ∈ cylinder Set.univ 0 T, |u p| ≤ B)
    (hVBound : ∀ p ∈ cylinder Set.univ 0 T, |v p| ≤ C)
    (hInit : ∀ x, u (x,0) = v (x,0))
    (hOp : ∀ p ∈ Set.univ ×ˢ Set.Ioc 0 T,
      linearOp (cylinder Set.univ 0 T) a b u p =
        linearOp (cylinder Set.univ 0 T) a b v p) :
    Set.EqOn u v (cylinder Set.univ 0 T) := by
  have hBound : ∀ p ∈ cylinder Set.univ 0 T, |u p-v p| ≤ B+C := by
    intro p hp
    have hNorm : |u p-v p| ≤ |u p|+|v p| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le (u p) (v p)
    exact hNorm.trans (add_le_add (hUBound p hp) (hVBound p hp))
  have hZero := bounded_wholeSpace_residual_bound hT (c2_sub hu hv) hEll hM hb hBound
    (fun x => by rw [hInit x,sub_self]) (by norm_num : (0 : ℝ) ≤ 0) (by
      intro p hp
      rw [linearOp_sub (a := a) (b := b) hu hv
        ⟨Set.mem_univ _,hp.2.1.le,hp.2.2⟩,hOp p hp,sub_self,abs_zero])
  intro p hp
  have h := hZero p hp
  simp only [mul_zero] at h
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))

set_option backward.isDefEq.respectTransparency.types false

local instance {n : ℕ} (α : ℝ) (Q : Set (Point n)) : NormedAddCommGroup (holderGraph α Q) :=
  inferInstance
local instance {n : ℕ} (α : ℝ) (Q : Set (Point n)) : NormedSpace ℝ (holderGraph α Q) :=
  inferInstance

theorem timeD_congr_on {n : ℕ} {Q : Set (Point n)} {u v : Point n → ℝ}
    (hEq : Set.EqOn u v Q) {p : Point n} (hp : p ∈ Q) : timeD Q u p = timeD Q v p := by
  unfold timeD
  exact derivWithin_congr (fun t ht => hEq (show (p.1,t) ∈ Q from ht)) (hEq hp)

theorem spatialD_congr_cylinder_univ {n : ℕ} {T : ℝ} {u v : Point n → ℝ}
    (hEq : Set.EqOn u v (cylinder Set.univ 0 T)) {p : Point n}
    (hp : p ∈ cylinder Set.univ 0 T) : spatialD u p = spatialD v p := by
  have hSlice : (fun x : Space n => u (x,p.2)) = fun x : Space n => v (x,p.2) := by
    funext x
    exact hEq ⟨Set.mem_univ _,hp.2⟩
  simp only [spatialD,hSlice]

theorem spatialDD_congr_cylinder_univ {n : ℕ} {T : ℝ} {u v : Point n → ℝ}
    (hEq : Set.EqOn u v (cylinder Set.univ 0 T)) {p : Point n}
    (hp : p ∈ cylinder Set.univ 0 T) : spatialDD u p = spatialDD v p := by
  have hSlice : (fun x : Space n => u (x,p.2)) = fun x : Space n => v (x,p.2) := by
    funext x
    exact hEq ⟨Set.mem_univ _,hp.2⟩
  change fderiv ℝ (fderiv ℝ (fun x => u (x,p.2))) p.1 =
    fderiv ℝ (fderiv ℝ (fun x => v (x,p.2))) p.1
  rw [hSlice]

theorem linearOp_congr_cylinder_univ {n : ℕ} {T : ℝ} {u v : Point n → ℝ}
    (hEq : Set.EqOn u v (cylinder Set.univ 0 T))
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ) {p : Point n}
    (hp : p ∈ cylinder Set.univ 0 T) :
    linearOp (cylinder Set.univ 0 T) a b u p =
      linearOp (cylinder Set.univ 0 T) a b v p := by
  simp only [linearOp,timeD_congr_on hEq hp,spatialD_congr_cylinder_univ hEq hp,
    spatialDD_congr_cylinder_univ hEq hp]

theorem c2_congr_cylinder_univ {n : ℕ} {T : ℝ} {u v : Point n → ℝ}
    (hu : C2 (cylinder Set.univ 0 T) u) (hEq : Set.EqOn u v (cylinder Set.univ 0 T)) :
    C2 (cylinder Set.univ 0 T) v := by
  refine ⟨hu.1.congr (fun p hp => (hEq hp).symm),?_,?_,?_,?_,?_⟩
  · exact hu.2.1.congr (fun p hp => (spatialD_congr_cylinder_univ hEq hp).symm)
  · exact hu.2.2.1.congr (fun p hp => (spatialDD_congr_cylinder_univ hEq hp).symm)
  · exact hu.2.2.2.1.congr (fun p hp => (timeD_congr_on hEq hp).symm)
  · intro p hp
    have hSlice : (fun x : Space n => v (x,p.2)) = fun x : Space n => u (x,p.2) := by
      funext x
      exact (show u (x,p.2) = v (x,p.2) from hEq ⟨Set.mem_univ _,hp.2⟩).symm
    rw [hSlice]
    exact hu.2.2.2.2.1 p hp
  · intro p hp
    exact (hu.2.2.2.2.2 p hp).congr (fun t ht => (hEq ht).symm) (hEq hp).symm

theorem holderBound_congr_on {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    {α C : ℝ} {Q : Set (Point n)} {f g : Point n → V}
    (hf : HolderBound α Q f C) (hEq : Set.EqOn f g Q) : HolderBound α Q g C := by
  refine ⟨hf.1,?_,?_⟩
  · intro p hp
    rw [← hEq hp]
    exact hf.2.1 p hp
  · intro p hp q hq
    rw [← hEq hp,← hEq hq]
    exact hf.2.2 p hp q hq

def holderGraphLift {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α C : ℝ} {Q : Set (Point n)} (hα : 0 < α) (F : E → Point n → ℝ)
    (hBound : ∀ x, HolderBound α Q (F x) (C*‖x‖))
    (hAdd : ∀ x y, ∀ p ∈ Q, F (x+y) p = F x p+F y p)
    (hSmul : ∀ (a : ℝ) x, ∀ p ∈ Q, F (a • x) p = a*F x p) :
    E →L[ℝ] holderGraph α Q :=
  let G : E →ₗ[ℝ] holderGraph α Q := {
    toFun := fun x => holderGraphOfBound hα (hBound x)
    map_add' := by
      intro x y
      apply holderGraph_ext
      intro p
      change F (x+y) p.val = F x p.val+F y p.val
      exact hAdd x y p.val p.property
    map_smul' := by
      intro a x
      apply holderGraph_ext
      intro p
      change F (a • x) p.val = a*F x p.val
      exact hSmul a x p.val p.property }
  G.mkContinuous C (fun x => holderGraphOfBound_norm_le hα (hBound x))

theorem holderGraphLift_apply {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α C : ℝ} {Q : Set (Point n)} (hα : 0 < α) (F : E → Point n → ℝ)
    (hBound : ∀ x, HolderBound α Q (F x) (C*‖x‖))
    (hAdd : ∀ x y, ∀ p ∈ Q, F (x+y) p = F x p+F y p)
    (hSmul : ∀ (a : ℝ) x, ∀ p ∈ Q, F (a • x) p = a*F x p) (x : E) (p : Q) :
    (holderGraphLift hα F hBound hAdd hSmul x).val.1 p = F x p.val := rfl

theorem holderGraphLift_norm_le {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α C : ℝ} {Q : Set (Point n)} (hα : 0 < α) (F : E → Point n → ℝ)
    (hBound : ∀ x, HolderBound α Q (F x) (C*‖x‖))
    (hAdd : ∀ x y, ∀ p ∈ Q, F (x+y) p = F x p+F y p)
    (hSmul : ∀ (a : ℝ) x, ∀ p ∈ Q, F (a • x) p = a*F x p) (x : E) :
    ‖holderGraphLift hα F hBound hAdd hSmul x‖ ≤ C*‖x‖ :=
  holderGraphOfBound_norm_le hα (hBound x)

theorem holderGraph_residual_correction {n : ℕ} {α : ℝ} {Q : Set (Point n)}
    (R : holderGraph α Q →L[ℝ] holderGraph α Q) (hR : ‖R‖ ≤ (1/2 : ℝ))
    (f : holderGraph α Q) : ∃ g : holderGraph α Q, g+R g = f ∧ ‖g‖ ≤ 2*‖f‖ := by
  let Φ : holderGraph α Q → holderGraph α Q := fun g => f-R g
  have hLip : LipschitzWith (1/2 : NNReal) Φ := by
    rw [lipschitzWith_iff_norm_sub_le]
    intro x y
    have hEq : Φ x-Φ y = -(R (x-y)) := by dsimp only [Φ]; rw [R.map_sub]; abel
    rw [hEq,norm_neg]
    exact (R.le_opNorm _).trans (mul_le_mul_of_nonneg_right hR (norm_nonneg _))
  have hContract : ContractingWith (1/2 : NNReal) Φ := ⟨by norm_num,hLip⟩
  let g := hContract.fixedPoint Φ
  have hFix : f-R g = g := hContract.fixedPoint_isFixedPt
  refine ⟨g,(sub_eq_iff_eq_add.mp hFix).symm,?_⟩
  have hNorm : ‖g‖ ≤ ‖f‖+‖R g‖ := by
    calc
      _ = ‖f-R g‖ := congrArg norm hFix.symm
      _ ≤ _ := norm_sub_le _ _
  have hRg : ‖R g‖ ≤ (1/2 : ℝ)*‖g‖ :=
    (R.le_opNorm _).trans (mul_le_mul_of_nonneg_right hR (norm_nonneg _))
  linarith

theorem holderBound_mul {n : ℕ} {α F G : ℝ} {Q : Set (Point n)} {f g : Point n → ℝ}
    (hf : HolderBound α Q f F) (hg : HolderBound α Q g G) :
    HolderBound α Q (fun p => f p*g p) (2*F*G) := by
  have h := holderBound_smul_refined hf hg hf.1 hg.1
    (fun p hp => by simpa only [Real.norm_eq_abs] using hf.2.1 p hp) hg.2.1
  simpa only [smul_eq_mul,← two_mul,mul_assoc] using h

def finiteHeatParametrix {n : ℕ} {ι : Type*} (s : Finset ι)
    (B : ι → Space n ≃L[ℝ] Space n) (φ ψ : ι → Space n → ℝ)
    (f : Point n → ℝ) : Point n → ℝ :=
  finiteParametrix s φ
    (fun i => constantHeatDuhamel (B i) (fun p => ψ i p.1*f p))

theorem finiteHeatParametrix_initial {n : ℕ} {ι : Type*} (s : Finset ι)
    (B : ι → Space n ≃L[ℝ] Space n) (φ ψ : ι → Space n → ℝ)
    (f : Point n → ℝ) (x : Space n) : finiteHeatParametrix s B φ ψ f (x,0) = 0 := by
  simp only [finiteHeatParametrix,finiteParametrix,constantHeatDuhamel_initial,mul_zero,
    Finset.sum_const_zero]

theorem finiteHeatParametrix_smul {n : ℕ} {ι : Type*} (s : Finset ι)
    (B : ι → Space n ≃L[ℝ] Space n) (φ ψ : ι → Space n → ℝ)
    (a : ℝ) (f : Point n → ℝ) (p : Point n) :
    finiteHeatParametrix s B φ ψ (a • f) p = a*finiteHeatParametrix s B φ ψ f p := by
  classical
  have hSource (i : ι) : (fun q : Point n => ψ i q.1*(a • f) q) =
      a • (fun q : Point n => ψ i q.1*f q) := by
    funext q
    simp only [Pi.smul_apply,smul_eq_mul]
    ring
  unfold finiteHeatParametrix finiteParametrix
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only
  rw [hSource i,constantHeatDuhamel_smul]
  ring

theorem finiteHeatParametrix_add {n : ℕ} {ι : Type*} (s : Finset ι)
    (B : ι → Space n ≃L[ℝ] Space n) (φ ψ : ι → Space n → ℝ)
    {α T F G : ℝ} {f g : Point n → ℝ} (hα : 0 < α) (hT : 0 ≤ T)
    (hf : ∀ i ∈ s, HolderBound α (cylinder Set.univ 0 T) (fun q => ψ i q.1*f q) F)
    (hg : ∀ i ∈ s, HolderBound α (cylinder Set.univ 0 T) (fun q => ψ i q.1*g q) G)
    {p : Point n} (hp : p ∈ cylinder Set.univ 0 T) :
    finiteHeatParametrix s B φ ψ (f+g) p =
      finiteHeatParametrix s B φ ψ f p+finiteHeatParametrix s B φ ψ g p := by
  classical
  have hSource (i : ι) : (fun q : Point n => ψ i q.1*(f+g) q) =
      (fun q : Point n => ψ i q.1*f q)+(fun q : Point n => ψ i q.1*g q) := by
    funext q
    simp only [Pi.add_apply]
    ring
  unfold finiteHeatParametrix finiteParametrix
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only
  rw [hSource i,constantHeatDuhamel_add_of_holder (B i) hα hT (hf i hi) (hg i hi) hp]
  ring

theorem finiteHeatParametrix_C2 {n : ℕ} {ι : Type*} (s : Finset ι)
    (B : ι → Space n ≃L[ℝ] Space n) (φ ψ : ι → Space n → ℝ)
    {α T P F : ℝ} {f : Point n → ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hT : 0 < T) (hT1 : T ≤ 1) (hφ : ∀ i ∈ s, ContDiff ℝ 2 (φ i))
    (hψ : ∀ i ∈ s, HolderBound α (cylinder Set.univ 0 T) (fun p => ψ i p.1) P)
    (hf : HolderBound α (cylinder Set.univ 0 T) f F) :
    C2 (cylinder Set.univ 0 T) (finiteHeatParametrix s B φ ψ f) := by
  obtain ⟨C,hC,hSolver⟩ := constantHeatDuhamel_schauderBound (n := n) hα hα1
  unfold finiteHeatParametrix
  apply finiteParametrix_C2 s hφ
  intro i hi
  exact (hSolver (B i) T (2*P*F) hT hT1 _ (holderBound_mul (hψ i hi) hf)).1

theorem finiteHeatParametrix_linearOp {n : ℕ} {ι : Type*} (s : Finset ι)
    (B : ι → Space n ≃L[ℝ] Space n) (φ ψ : ι → Space n → ℝ)
    (A : ι → Mat n) (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
    {α T P F : ℝ} {f : Point n → ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hT : 0 < T) (hT1 : T ≤ 1) (hφ : ∀ i ∈ s, ContDiff ℝ 2 (φ i))
    (hψ : ∀ i ∈ s, HolderBound α (cylinder Set.univ 0 T) (fun p => ψ i p.1) P)
    (hf : HolderBound α (cylinder Set.univ 0 T) f F)
    (hB : ∀ i ∈ s, ∀ H : Space n →L[ℝ] Space n →L[ℝ] ℝ,
      (∑ k : Yau.RIdx n, H (B i (Yau.realVec k)) (B i (Yau.realVec k))) =
        ∑ j : Yau.RIdx n, ∑ k : Yau.RIdx n,
          A i j k*H (Yau.realVec j) (Yau.realVec k))
    (hPartition : ∀ p ∈ cylinder Set.univ 0 T, (∑ i ∈ s, φ i p.1*ψ i p.1) = 1)
    {p : Point n} (hp : p ∈ cylinder Set.univ 0 T) :
    linearOp (cylinder Set.univ 0 T) a b (finiteHeatParametrix s B φ ψ f) p = f p+
      ∑ i ∈ s, frozenPatchResidual (cylinder Set.univ 0 T) a b (A i) (φ i)
        (constantHeatDuhamel (B i) (fun q => ψ i q.1*f q)) p := by
  obtain ⟨C,hC,hSolver⟩ := constantHeatDuhamel_schauderBound (n := n) hα hα1
  unfold finiteHeatParametrix
  apply finiteParametrix_linearOp s hφ
  · intro i hi
    exact (hSolver (B i) T (2*P*F) hT hT1 _ (holderBound_mul (hψ i hi) hf)).1
  · intro i hi q hq
    exact constantHeatDuhamel_linearOp (B i) (hB i hi) hα hα1 hT hT1
      (holderBound_mul (hψ i hi) hf) hq
  · exact hPartition
  · exact hp

theorem c2_const_smul {n : ℕ} {Q : Set (Point n)} {u : Point n → ℝ}
    (hu : C2 Q u) (c : ℝ) : C2 Q (c • u) := by
  change C2 Q (fun p => c*u p)
  exact c2_spatial_mul (φ := fun _ => c) contDiff_const hu

theorem linearOp_const_smul {n : ℕ} {Q : Set (Point n)}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {u : Point n → ℝ}
    (hu : C2 Q u) (c : ℝ) {p : Point n} (hp : p ∈ Q) :
    linearOp Q a b (c • u) p = c*linearOp Q a b u p := by
  change linearOp Q a b (fun q => c*u q) p = _
  have h := linearOp_spatial_mul (Q := Q) (a := a) (b := b) (φ := fun _ => c)
    (u := u) (p := p) contDiffAt_const (hu.2.2.2.2.1 p hp)
  simpa only [fderiv_fun_const,fderiv_zero,Pi.zero_apply,zero_apply,
    zero_mul,mul_zero,zero_add,add_zero,Finset.sum_const_zero,sub_zero] using h

def finiteHeatResidual {n : ℕ} {ι : Type*} (T : ℝ) (s : Finset ι)
    (B : ι → Space n ≃L[ℝ] Space n) (φ ψ : ι → Space n → ℝ)
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
    (f : Point n → ℝ) (p : Point n) : ℝ :=
  linearOp (cylinder Set.univ 0 T) a b (finiteHeatParametrix s B φ ψ f) p-f p

theorem finiteHeatResidual_add {n : ℕ} {ι : Type*} (s : Finset ι)
    (B : ι → Space n ≃L[ℝ] Space n) (φ ψ : ι → Space n → ℝ)
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
    {α T P F G : ℝ} {f g : Point n → ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hT : 0 < T) (hT1 : T ≤ 1) (hφ : ∀ i ∈ s, ContDiff ℝ 2 (φ i))
    (hψ : ∀ i ∈ s, HolderBound α (cylinder Set.univ 0 T) (fun p => ψ i p.1) P)
    (hf : HolderBound α (cylinder Set.univ 0 T) f F)
    (hg : HolderBound α (cylinder Set.univ 0 T) g G)
    {p : Point n} (hp : p ∈ cylinder Set.univ 0 T) :
    finiteHeatResidual T s B φ ψ a b (f+g) p =
      finiteHeatResidual T s B φ ψ a b f p+finiteHeatResidual T s B φ ψ a b g p := by
  have hKf := finiteHeatParametrix_C2 s B φ ψ hα hα1 hT hT1 hφ hψ hf
  have hKg := finiteHeatParametrix_C2 s B φ ψ hα hα1 hT hT1 hφ hψ hg
  have hAdd : Set.EqOn (finiteHeatParametrix s B φ ψ (f+g))
      (fun q => finiteHeatParametrix s B φ ψ f q+finiteHeatParametrix s B φ ψ g q)
      (cylinder Set.univ 0 T) := by
    intro q hq
    exact finiteHeatParametrix_add s B φ ψ hα hT.le
      (fun i hi => holderBound_mul (hψ i hi) hf)
      (fun i hi => holderBound_mul (hψ i hi) hg) hq
  unfold finiteHeatResidual
  rw [linearOp_congr_cylinder_univ hAdd a b hp,linearOp_add (a := a) (b := b) hKf hKg hp]
  simp only [Pi.add_apply]
  ring

theorem finiteHeatResidual_smul {n : ℕ} {ι : Type*} (s : Finset ι)
    (B : ι → Space n ≃L[ℝ] Space n) (φ ψ : ι → Space n → ℝ)
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
    {α T P F : ℝ} {f : Point n → ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hT : 0 < T) (hT1 : T ≤ 1) (hφ : ∀ i ∈ s, ContDiff ℝ 2 (φ i))
    (hψ : ∀ i ∈ s, HolderBound α (cylinder Set.univ 0 T) (fun p => ψ i p.1) P)
    (hf : HolderBound α (cylinder Set.univ 0 T) f F) (c : ℝ)
    {p : Point n} (hp : p ∈ cylinder Set.univ 0 T) :
    finiteHeatResidual T s B φ ψ a b (c • f) p =
      c*finiteHeatResidual T s B φ ψ a b f p := by
  have hKf := finiteHeatParametrix_C2 s B φ ψ hα hα1 hT hT1 hφ hψ hf
  have hScale : finiteHeatParametrix s B φ ψ (c • f) =
      c • finiteHeatParametrix s B φ ψ f := by
    funext q
    exact finiteHeatParametrix_smul s B φ ψ c f q
  unfold finiteHeatResidual
  rw [hScale,linearOp_const_smul (a := a) (b := b) hKf c hp]
  simp only [Pi.smul_apply,smul_eq_mul]
  ring

end Yau.LeafProofs.L16Aux
