import Yau.Proofs.D04Anchors

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace Yau.Proofs.D04Aux

variable {α : Type*}

/-! The Lipschitz-majorant construction used in L08 is metric: here its
proof is given in arbitrary dimension for D04, including minus infinity. -/

/-- Finite lower truncation of an extended-real potential. -/
def lowerTrunc (u : α → EReal) (n : ℕ) (z : α) : ℝ :=
  (max (u z) ((-(n : ℝ) : ℝ) : EReal)).toReal

theorem coe_lowerTrunc {u : α → EReal} (n : ℕ) {z : α} (hu : u z < ⊤) :
    (lowerTrunc u n z : EReal) = max (u z) ((-(n : ℝ) : ℝ) : EReal) := by
  apply EReal.coe_toReal
  · exact (max_lt hu (EReal.coe_lt_top _)).ne
  · exact ne_of_gt ((EReal.bot_lt_coe (-(n : ℝ))).trans_le (le_max_right _ _))

theorem le_coe_lowerTrunc {u : α → EReal} (n : ℕ) {z : α} (hu : u z < ⊤) :
    u z ≤ (lowerTrunc u n z : EReal) := by
  rw [coe_lowerTrunc n hu]
  exact le_max_left _ _

theorem lowerTrunc_le {u : α → EReal} (n : ℕ) {z : α} {C : ℝ}
    (hC : u z ≤ (C : EReal)) (hCn : -(n : ℝ) ≤ C) : lowerTrunc u n z ≤ C := by
  apply EReal.coe_le_coe_iff.mp
  rw [coe_lowerTrunc n (hC.trans_lt (EReal.coe_lt_top C))]
  exact max_le hC (EReal.coe_le_coe_iff.mpr hCn)

theorem lowerTrunc_antitone {u : α → EReal} {z : α} (hu : u z < ⊤) :
    Antitone (fun n : ℕ ↦ lowerTrunc u n z) := by
  intro n m hnm
  apply EReal.coe_le_coe_iff.mp
  rw [coe_lowerTrunc m hu, coe_lowerTrunc n hu]
  exact max_le_max_left _ (EReal.coe_le_coe_iff.mpr (neg_le_neg (Nat.cast_le.mpr hnm)))

theorem neg_nat_le_lowerTrunc {u : α → EReal} (k : ℕ) {z : α} (hu : u z < ⊤) :
    -(k : ℝ) ≤ lowerTrunc u k z := by
  apply EReal.coe_le_coe_iff.mp
  rw [coe_lowerTrunc k hu]
  exact le_max_right _ _

variable [PseudoMetricSpace α]

theorem compact_upper_bound {u : α → EReal} {K : Set α}
    (hK : IsCompact K) (hu : UpperSemicontinuousOn u K)
    (hfinite : ∀ z ∈ K, u z < ⊤) :
    ∃ C : ℝ, ∀ z ∈ K, u z ≤ (C : EReal) := by
  rcases K.eq_empty_or_nonempty with h | hne
  · exact ⟨0, fun _ hz => (h ▸ hz).elim⟩
  obtain ⟨x, hx, hmax⟩ := hu.exists_isMaxOn hne hK
  obtain ⟨C, hC, _⟩ := EReal.exists_between_coe_real (hfinite x hx)
  exact ⟨C, fun z hz => (hmax hz).trans hC.le⟩

/-- Lipschitz upper envelope of a finite lower truncation on a fixed set. -/
def majorantEnvelope (K : Set α) (u : α → EReal) (n : ℕ) (x : α) : ℝ :=
  ⨆ y : K, lowerTrunc u n y - (n : ℝ) * dist x y

theorem majorantEnvelope_bddAbove {K : Set α} {u : α → EReal} {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ z ∈ K, u z ≤ (C : EReal)) (n : ℕ) (x : α) :
    BddAbove (Set.range (fun y : K ↦ lowerTrunc u n y - (n : ℝ) * dist x y)) := by
  refine ⟨C, ?_⟩
  rintro t ⟨y, rfl⟩
  have ht := lowerTrunc_le n (hC y y.2)
    ((neg_nonpos.mpr (Nat.cast_nonneg n)).trans hC0)
  linarith [mul_nonneg (Nat.cast_nonneg n : 0 ≤ (n : ℝ)) (dist_nonneg (x := x) (y := (y : α)))]

theorem majorantEnvelope_lipschitz {K : Set α} {u : α → EReal} {C : ℝ}
    (hK : K.Nonempty) (hC0 : 0 ≤ C) (hC : ∀ z ∈ K, u z ≤ (C : EReal)) (n : ℕ) :
    LipschitzWith (n : NNReal) (majorantEnvelope K u n) := by
  let : Nonempty K := hK.to_subtype
  have haux (x x' : α) :
      majorantEnvelope K u n x ≤ majorantEnvelope K u n x' + (n : ℝ) * dist x x' := by
    apply ciSup_le
    intro y
    have hs := le_ciSup (majorantEnvelope_bddAbove hC0 hC n x') y
    have ht := mul_le_mul_of_nonneg_left (dist_triangle x' x (y : α))
      (Nat.cast_nonneg n : 0 ≤ (n : ℝ))
    rw [mul_add, dist_comm x' x] at ht
    change lowerTrunc u n y - (n : ℝ) * dist x' y ≤ majorantEnvelope K u n x' at hs
    linarith
  apply LipschitzWith.of_dist_le_mul
  intro x x'
  rw [Real.dist_eq]
  change |majorantEnvelope K u n x - majorantEnvelope K u n x'| ≤ (n : ℝ) * dist x x'
  apply abs_sub_le_iff.mpr
  constructor
  · linarith [haux x x']
  · have h := haux x' x
    rw [dist_comm x' x] at h
    linarith

theorem le_coe_majorantEnvelope {K : Set α} {u : α → EReal} {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ z ∈ K, u z ≤ (C : EReal)) (n : ℕ) {x : α} (hx : x ∈ K) :
    u x ≤ (majorantEnvelope K u n x : EReal) := by
  have hs := le_ciSup (majorantEnvelope_bddAbove hC0 hC n x) (⟨x, hx⟩ : K)
  have htrunc : lowerTrunc u n x ≤ majorantEnvelope K u n x := by
    simpa only [dist_self, mul_zero, sub_zero, majorantEnvelope] using hs
  exact (le_coe_lowerTrunc n ((hC x hx).trans_lt (EReal.coe_lt_top C))).trans
    (EReal.coe_le_coe_iff.mpr htrunc)

theorem majorantEnvelope_antitone {K : Set α} {u : α → EReal} {C : ℝ}
    (_hK : K.Nonempty) (hC0 : 0 ≤ C) (hC : ∀ z ∈ K, u z ≤ (C : EReal)) (x : α) :
    Antitone (fun n : ℕ ↦ majorantEnvelope K u n x) := by
  let : Nonempty K := _hK.to_subtype
  intro n m hnm
  apply ciSup_mono (majorantEnvelope_bddAbove hC0 hC n x)
  intro y
  have ht := lowerTrunc_antitone ((hC y y.2).trans_lt (EReal.coe_lt_top C)) hnm
  have hp := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hnm : (n : ℝ) ≤ m)
    (dist_nonneg (x := x) (y := (y : α)))
  linarith

/-- A bounded upper semicontinuous function is recovered by the decreasing
Lipschitz majorants, including at points where its value is `-∞`. -/
theorem tendsto_majorantEnvelope {K : Set α} {u : α → EReal} {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ z ∈ K, u z ≤ (C : EReal))
    (hu : UpperSemicontinuousOn u K) {x : α} (hx : x ∈ K) :
    Tendsto (fun n : ℕ ↦ (majorantEnvelope K u n x : EReal)) atTop (𝓝 (u x)) := by
  let : Nonempty K := ⟨⟨x, hx⟩⟩
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun n ↦ ha.trans_le (le_coe_majorantEnvelope hC0 hC n hx)
  · intro b hb
    obtain ⟨q, hq, hqb⟩ := EReal.exists_between_coe_real hb
    obtain ⟨δ, hδ, hlocal⟩ := Metric.mem_nhdsWithin_iff.mp (hu x hx q hq)
    obtain ⟨N, hN⟩ := exists_nat_gt (max (-q) ((C - q) / δ))
    filter_upwards [eventually_ge_atTop N] with n hn
    have hnq : -(n : ℝ) ≤ q := by
      have := (le_max_left (-q) ((C - q) / δ)).trans_lt hN
      have := (Nat.cast_le.mpr hn : (N : ℝ) ≤ n)
      linarith
    have hnδ : C - q ≤ (n : ℝ) * δ := by
      have h := (le_max_right (-q) ((C - q) / δ)).trans_lt hN
      have h' := (div_lt_iff₀ hδ).mp h
      have := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hn : (N : ℝ) ≤ n) hδ.le
      linarith
    have hbound : majorantEnvelope K u n x ≤ q := by
      apply ciSup_le
      intro y
      by_cases hy : dist x (y : α) < δ
      · have hyq : u y ≤ (q : EReal) :=
          (hlocal ⟨by simpa only [Metric.mem_ball, dist_comm] using hy, y.2⟩).le
        have ht := lowerTrunc_le n hyq hnq
        linarith [mul_nonneg (Nat.cast_nonneg n : 0 ≤ (n : ℝ))
          (dist_nonneg (x := x) (y := (y : α)))]
      · have ht := lowerTrunc_le n (hC y y.2)
          ((neg_nonpos.mpr (Nat.cast_nonneg n)).trans hC0)
        have hp := mul_le_mul_of_nonneg_left (le_of_not_gt hy) (Nat.cast_nonneg n : 0 ≤ (n : ℝ))
        linarith
    exact (EReal.coe_le_coe_iff.mpr hbound).trans_lt hqb

theorem majorantEnvelope_le {K : Set α} {u : α → EReal} {C : ℝ}
    (hK : K.Nonempty) (hC0 : 0 ≤ C) (hC : ∀ z ∈ K, u z ≤ (C : EReal))
    (n : ℕ) (x : α) : majorantEnvelope K u n x ≤ C := by
  let : Nonempty K := hK.to_subtype
  apply ciSup_le
  intro y
  have ht := lowerTrunc_le n (hC y y.2)
    ((neg_nonpos.mpr (Nat.cast_nonneg n)).trans hC0)
  linarith [mul_nonneg (Nat.cast_nonneg n : 0 ≤ (n : ℝ))
    (dist_nonneg (x := x) (y := (y : α)))]

/-- Bounded finite lower truncations are integrable before local L¹ of the
original potential has been established. This avoids assuming finiteness of
the original EReal function through `toReal`. -/
theorem integrableOn_lowerTrunc [MeasurableSpace α] [BorelSpace α]
    (μ : Measure α) {K : Set α} (hK : MeasurableSet K) (hμK : μ K < ⊤)
    {u : α → EReal} (hu : UpperSemicontinuousOn u K)
    {C : ℝ} (hC : ∀ z ∈ K, u z ≤ (C : EReal)) (k : ℕ) :
    IntegrableOn (lowerTrunc u k) K μ := by
  have hm : Measurable (fun z : K => lowerTrunc u k z) := by
    exact (((upperSemicontinuousOn_iff_restrict.mpr hu).measurable).max
      measurable_const).ereal_toReal
  have hmeas : AEStronglyMeasurable (lowerTrunc u k) (μ.restrict K) :=
    (aemeasurable_restrict_of_measurable_subtype hK hm).aestronglyMeasurable
  let B : ℝ := |C| + k
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hCB : C ≤ B := by
    dsimp [B]
    linarith [le_abs_self C, (Nat.cast_nonneg k : 0 ≤ (k : ℝ))]
  apply (integrableOn_const hμK.ne (C := B)).mono' hmeas
  filter_upwards [ae_restrict_mem hK] with z hz
  have hfinite := (hC z hz).trans_lt (EReal.coe_lt_top C)
  have hlow := neg_nat_le_lowerTrunc k hfinite
  have hupp := lowerTrunc_le k
    ((hC z hz).trans (EReal.coe_le_coe_iff.mpr hCB))
    ((neg_nonpos.mpr (Nat.cast_nonneg k)).trans hB0)
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  dsimp only [B] at *
  exact ⟨by linarith [abs_nonneg C], hupp⟩

/-- The metric upper approximation converges under any finite measure once
the same real class is integrable and finite almost everywhere. -/
theorem tendsto_integral_majorantEnvelope [MeasurableSpace α] [BorelSpace α]
    (μ : Measure α) {K : Set α} (hK : MeasurableSet K) (hμK : μ K < ⊤)
    (hKn : K.Nonempty) {u : α → EReal} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ z ∈ K, u z ≤ (C : EReal)) (hu : UpperSemicontinuousOn u K)
    (hfinite : ∀ᵐ z ∂μ.restrict K, u z ≠ ⊥ ∧ u z ≠ ⊤)
    (hi : IntegrableOn (fun z => (u z).toReal) K μ) :
    Tendsto (fun k : ℕ => ∫ z in K, majorantEnvelope K u k z ∂μ) atTop
      (𝓝 (∫ z in K, (u z).toReal ∂μ)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun z => |(u z).toReal| + C)
  · exact Filter.Eventually.of_forall fun k =>
      (majorantEnvelope_lipschitz hKn hC0 hC k).continuous.aestronglyMeasurable.restrict
  · apply Filter.Eventually.of_forall
    intro k
    filter_upwards [hfinite, ae_restrict_mem hK] with z hz hzK
    have hl := le_coe_majorantEnvelope hC0 hC k hzK
    rw [← EReal.coe_toReal hz.2 hz.1] at hl
    have hlow := EReal.coe_le_coe_iff.mp hl
    have hhigh := majorantEnvelope_le hKn hC0 hC k z
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [neg_abs_le (u z).toReal],
      by linarith [abs_nonneg (u z).toReal]⟩
  · exact hi.norm.add (integrableOn_const hμK.ne)
  · filter_upwards [hfinite, ae_restrict_mem hK] with z hz hzK
    have ht := (EReal.tendsto_toReal hz.2 hz.1).comp
      (tendsto_majorantEnvelope hC0 hC hu hzK)
    simpa only [Function.comp_def, EReal.toReal_coe] using ht

end Yau.Proofs.D04Aux
