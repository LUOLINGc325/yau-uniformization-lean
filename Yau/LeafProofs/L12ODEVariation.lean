import Yau.LeafProofs.L12Continuation
import Mathlib.Analysis.Calculus.FDeriv.Partial

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff
namespace Yau.LeafProofs.L12Aux

section ODEVariation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A Lipschitz derivative gives a uniform quadratic first-order remainder. -/
theorem norm_firstOrderRemainder_le
    {F : E → E} {D : E → E →L[ℝ] E} {s : Set E} {L : ℝ≥0}
    (hs : Convex ℝ s) (hF : ∀ x ∈ s, HasFDerivAt F (D x) x)
    (hD : LipschitzOnWith L D s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    ‖F y - F x - D x (y - x)‖ ≤ (L : ℝ) * ‖y - x‖ ^ 2 := by
  have hseg : segment ℝ x y ⊆ s := hs.segment_subset hx hy
  have hbound : ∀ w ∈ segment ℝ x y, ‖D w - D x‖ ≤ (L : ℝ) * ‖y - x‖ := by
    intro w hw
    exact (hD.norm_sub_le (hseg hw) hx).trans
      (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hw) L.coe_nonneg)
  have h := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (f := F) (f' := D) (φ := D x)
    (fun w hw => (hF w (hseg hw)).hasFDerivWithinAt)
    hbound (convex_segment (𝕜 := ℝ) x y) (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  convert h using 1 <;> ring

/-- A two-sided zero-initial-data Gronwall estimate, obtained by time reversal
on the negative half interval. -/
theorem norm_le_gronwallBound_abs {e e' : ℝ → E} {ε K q t : ℝ}
    (hε : 0 ≤ ε) (he : ∀ s ∈ Set.Icc (-ε) ε, HasDerivAt e (e' s) s)
    (he₀ : e 0 = 0)
    (hbound : ∀ s ∈ Set.Icc (-ε) ε, ‖e' s‖ ≤ K * ‖e s‖ + q)
    (ht : t ∈ Set.Icc (-ε) ε) :
    ‖e t‖ ≤ gronwallBound 0 K q |t| := by
  by_cases ht0 : 0 ≤ t
  · have hsub : Set.Icc 0 t ⊆ Set.Icc (-ε) ε := by
      intro s hs
      exact ⟨by linarith [hs.1], hs.2.trans ht.2⟩
    have hc : ContinuousOn e (Set.Icc 0 t) :=
      fun s hs => (he s (hsub hs)).continuousAt.continuousWithinAt
    have hb := norm_le_gronwallBound_of_norm_deriv_right_le
      (f := e) (f' := e') (δ := 0) (K := K) (ε := q) (a := 0) (b := t) hc
      (fun s hs => (he s (hsub (Set.Ico_subset_Icc_self hs))).hasDerivWithinAt)
      (by rw [he₀, norm_zero])
      (fun s hs => hbound s (hsub (Set.Ico_subset_Icc_self hs))) t ⟨ht0, le_rfl⟩
    simpa only [sub_zero, abs_of_nonneg ht0] using hb
  · have htneg : t < 0 := lt_of_not_ge ht0
    let eneg := fun s => e (-s)
    let eneg' := fun s => -e' (-s)
    have hsub : ∀ s ∈ Set.Icc 0 (-t), -s ∈ Set.Icc (-ε) ε := by
      intro s hs
      exact ⟨by linarith [hs.2, ht.1], by linarith [hs.1]⟩
    have hen : ∀ s ∈ Set.Icc 0 (-t), HasDerivAt eneg (eneg' s) s := by
      intro s hs
      simpa only [eneg, eneg', Function.comp_def, neg_one_smul] using
        (he (-s) (hsub s hs)).scomp s (hasDerivAt_neg s)
    have hc : ContinuousOn eneg (Set.Icc 0 (-t)) :=
      fun s hs => (hen s hs).continuousAt.continuousWithinAt
    have hb := norm_le_gronwallBound_of_norm_deriv_right_le
      (f := eneg) (f' := eneg') (δ := 0) (K := K) (ε := q) (a := 0) (b := -t) hc
      (fun s hs => (hen s (Set.Ico_subset_Icc_self hs)).hasDerivWithinAt)
      (by simp only [eneg, neg_zero, he₀, norm_zero, le_refl])
      (fun s hs => by
        simpa only [eneg, eneg', norm_neg] using hbound (-s)
          (hsub s (Set.Ico_subset_Icc_self hs))) (-t) ⟨by linarith, le_rfl⟩
    simpa only [eneg, neg_neg, sub_zero, abs_of_neg htneg] using hb

/-- Position and first variation are evolved by one autonomous ODE. -/
def odeVariationField (F : E → E) (p : E × (E →L[ℝ] E)) : E × (E →L[ℝ] E) :=
  (F p.1, (fderiv ℝ F p.1).comp p.2)

theorem odeVariationField_contDiffAt {F : E → E} {z₀ : E}
    (hF : ContDiffAt ℝ 2 F z₀) :
    ContDiffAt ℝ 1 (odeVariationField F) (z₀, ContinuousLinearMap.id ℝ E) := by
  have hD : ContDiffAt ℝ 1 (fderiv ℝ F) z₀ := hF.fderiv_right (by norm_num)
  exact ((hF.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)).comp _ contDiffAt_fst).prodMk
    ((hD.comp _ contDiffAt_fst).clm_comp contDiffAt_snd)

/-- A uniform quadratic error bound is an actual Frechet derivative criterion. -/
theorem hasFDerivAt_of_quadratic_remainder {f : E → E} {A : E →L[ℝ] E} {x : E} {B : ℝ}
    (hB : 0 ≤ B)
    (hquad : ∀ᶠ h in 𝓝 (0 : E), ‖f (x + h) - f x - A h‖ ≤ B * ‖h‖ ^ 2) :
    HasFDerivAt f A x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  have hpos : 0 < c / (B + 1) := div_pos hc (by linarith)
  filter_upwards [hquad, Metric.ball_mem_nhds (0 : E) hpos] with h hh hsmall
  rw [Metric.mem_ball, dist_zero_right] at hsmall
  have hlinear : B * ‖h‖ ≤ c := by
    have hlt := (lt_div_iff₀ (by linarith : 0 < B + 1)).mp hsmall
    nlinarith [norm_nonneg h]
  exact hh.trans (by
    calc
      B * ‖h‖ ^ 2 = (B * ‖h‖) * ‖h‖ := by ring
      _ ≤ c * ‖h‖ := mul_le_mul_of_nonneg_right hlinear (norm_nonneg h))


/-- The first variation solves the actual initial-state difference quotient:
a uniform quadratic remainder is derived from the two time equations. -/
theorem norm_ODEVariation_remainder_le
    {F : E → E} {D : E → E →L[ℝ] E} {s S : Set E}
    {φ : E → ℝ → E} {V : E → ℝ → E →L[ℝ] E}
    {L C : ℝ≥0} {ε K : ℝ}
    (hε : 0 ≤ ε) (hK : 0 < K) (hs : Convex ℝ s)
    (hF : ∀ x ∈ s, HasFDerivAt F (D x) x)
    (hD : LipschitzOnWith L D s) (hDK : ∀ x ∈ s, ‖D x‖ ≤ K)
    (hφ : ∀ z ∈ S, ∀ t ∈ Set.Icc (-ε) ε, HasDerivAt (φ z) (F (φ z t)) t)
    (hV : ∀ z ∈ S, ∀ t ∈ Set.Icc (-ε) ε,
      HasDerivAt (V z) ((D (φ z t)).comp (V z t)) t)
    (hφ0 : ∀ z ∈ S, φ z 0 = z)
    (hV0 : ∀ z ∈ S, V z 0 = ContinuousLinearMap.id ℝ E)
    (hImage : ∀ z ∈ S, ∀ t ∈ Set.Icc (-ε) ε, φ z t ∈ s)
    (hLip : ∀ z ∈ S, ∀ z' ∈ S, ∀ t ∈ Set.Icc (-ε) ε,
      ‖φ z' t - φ z t‖ ≤ (C : ℝ) * ‖z' - z‖) :
    ∀ z ∈ S, ∀ z' ∈ S, ∀ t ∈ Set.Icc (-ε) ε,
      ‖φ z' t - φ z t - V z t (z' - z)‖ ≤
        ((L : ℝ) * (C : ℝ) ^ 2 / K * Real.exp (K * ε) + 1) * ‖z' - z‖ ^ 2 := by
  intro z hz z' hz' t ht
  let h := z' - z
  let e := fun t => φ z' t - φ z t - V z t h
  let e' := fun t => F (φ z' t) - F (φ z t) - D (φ z t) (V z t h)
  let Q := (L : ℝ) * (C : ℝ) ^ 2
  have hQ : 0 ≤ Q := mul_nonneg L.coe_nonneg (sq_nonneg _)
  have he : ∀ u ∈ Set.Icc (-ε) ε, HasDerivAt e (e' u) u := by
    intro u hu
    convert ((hφ z' hz' u hu).sub (hφ z hz u hu)).sub
      ((hV z hz u hu).clm_apply (hasDerivAt_const u h)) using 1
    simp only [e', ContinuousLinearMap.comp_apply, map_zero, add_zero]

  have he0 : e 0 = 0 := by
    simp only [e, hφ0 z hz, hφ0 z' hz', hV0 z hz, ContinuousLinearMap.id_apply, h, sub_self]
  have hbound : ∀ u ∈ Set.Icc (-ε) ε, ‖e' u‖ ≤ K * ‖e u‖ + Q * ‖h‖ ^ 2 := by
    intro u hu
    have hrem := norm_firstOrderRemainder_le hs hF hD (hImage z hz u hu) (hImage z' hz' u hu)
    have hlip := hLip z hz z' hz' u hu
    have hsq : ‖φ z' u - φ z u‖ ^ 2 ≤ ((C : ℝ) * ‖h‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg C.coe_nonneg (norm_nonneg _))).mpr hlip
    have hid : e' u = D (φ z u) (e u) +
        (F (φ z' u) - F (φ z u) - D (φ z u) (φ z' u - φ z u)) := by
      dsimp only [e', e]
      simp only [map_sub]
      abel
    rw [hid]
    calc
      _ ≤ ‖D (φ z u) (e u)‖ +
          ‖F (φ z' u) - F (φ z u) - D (φ z u) (φ z' u - φ z u)‖ := norm_add_le _ _
      _ ≤ ‖D (φ z u)‖ * ‖e u‖ + (L : ℝ) * ‖φ z' u - φ z u‖ ^ 2 :=
        add_le_add ((D (φ z u)).le_opNorm (e u)) hrem
      _ ≤ K * ‖e u‖ + Q * ‖h‖ ^ 2 := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right (hDK _ (hImage z hz u hu)) (norm_nonneg _)
        · calc
            (L : ℝ) * ‖φ z' u - φ z u‖ ^ 2 ≤ (L : ℝ) * ((C : ℝ) * ‖h‖) ^ 2 :=
              mul_le_mul_of_nonneg_left hsq L.coe_nonneg
            _ = Q * ‖h‖ ^ 2 := by dsimp only [Q]; ring
  have hest := norm_le_gronwallBound_abs (K := K) (q := Q * ‖h‖ ^ 2) hε he he0 hbound ht
  have htime := gronwallBound_mono (δ := 0) (K := K) (ε := Q * ‖h‖ ^ 2)
    (by norm_num) (mul_nonneg hQ (sq_nonneg _)) hK.le (abs_le.mpr ht)
  have hlast : gronwallBound 0 K (Q * ‖h‖ ^ 2) ε ≤
      (Q / K * Real.exp (K * ε) + 1) * ‖h‖ ^ 2 := by
    rw [gronwallBound_of_K_ne_0 hK.ne']
    simp only [zero_mul, zero_add]
    calc
      Q * ‖h‖ ^ 2 / K * (Real.exp (K * ε) - 1) =
          (Q / K * (Real.exp (K * ε) - 1)) * ‖h‖ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith [div_nonneg hQ hK.le]) (sq_nonneg _)
  exact hest.trans (htime.trans hlast)


theorem hasFDerivAt_of_quadratic_remainder_on_closedBall
    {f : E → E} {A : E →L[ℝ] E} {x z₀ : E} {r B : ℝ}
    (hx : x ∈ Metric.ball z₀ r) (hB : 0 ≤ B)
    (hquad : ∀ y ∈ Metric.closedBall z₀ r,
      ‖f y - f x - A (y - x)‖ ≤ B * ‖y - x‖ ^ 2) : HasFDerivAt f A x := by
  apply hasFDerivAt_of_quadratic_remainder hB
  have hmove : ∀ᶠ h in 𝓝 (0 : E), x + h ∈ Metric.ball z₀ r := by
    have hc : ContinuousAt (fun h : E => x + h) 0 := by fun_prop
    exact hc.preimage_mem_nhds (by simpa only [add_zero] using Metric.isOpen_ball.mem_nhds hx)
  filter_upwards [hmove] with h hh
  simpa only [add_sub_cancel_left] using hquad (x + h) (Metric.ball_subset_closedBall hh)

/-- Continuous spatial and time derivatives give the actual joint C1 map,
with its explicit coprod derivative. -/
theorem contDiffOn_of_continuous_ODEVariation_partials
    {φ b : E → ℝ → E} {V : E → ℝ → E →L[ℝ] E} {Q : Set (E × ℝ)}
    (hQ : IsOpen Q)
    (hspace : ∀ p ∈ Q, HasFDerivAt (fun z => φ z p.2) (V p.1 p.2) p.1)
    (htime : ∀ p ∈ Q, HasDerivAt (φ p.1) (b p.1 p.2) p.2)
    (hVc : ContinuousOn (Function.uncurry V) Q)
    (hbc : ContinuousOn (Function.uncurry b) Q) :
    ContDiffOn ℝ 1 (Function.uncurry φ) Q ∧
      ∀ p ∈ Q, HasFDerivAt (Function.uncurry φ)
        ((V p.1 p.2).coprod (ContinuousLinearMap.toSpanSingleton ℝ (b p.1 p.2))) p := by
  let T : E → ℝ → ℝ →L[ℝ] E :=
    fun z t => ContinuousLinearMap.toSpanSingleton ℝ (b z t)
  let J : E × ℝ → (E × ℝ) →L[ℝ] E :=
    fun p => (V p.1 p.2).coprod (T p.1 p.2)
  have hTc : ContinuousOn (Function.uncurry T) Q :=
    (ContinuousLinearMap.toSpanSingletonLIE ℝ E).continuous.comp_continuousOn hbc
  have hJc : ContinuousOn J Q := hVc.continuousLinearMapCoprod hTc
  have hderiv : ∀ p ∈ Q, HasFDerivAt (Function.uncurry φ) (J p) p := by
    intro p hp
    apply HasStrictFDerivAt.hasFDerivAt
    apply hasStrictFDerivAt_uncurry_coprod (f := φ) (f₁ := V) (f₂ := T)
    · filter_upwards [hQ.mem_nhds hp] with q hq
      exact hspace q hq
    · filter_upwards [hQ.mem_nhds hp] with q hq
      exact (htime q hq).hasFDerivAt
    · exact (hVc p hp).continuousAt (hQ.mem_nhds hp)
    · exact (hTc p hp).continuousAt (hQ.mem_nhds hp)
  refine ⟨?_, hderiv⟩
  intro p hp
  exact (contDiffAt_one_iff.mpr ⟨J, Q, hQ.mem_nhds hp, hJc, hderiv⟩).contDiffWithinAt


/-- One Picard flow for position and first variation supplies uniform local
solutions, joint continuity and a single initial-data Lipschitz constant. -/
theorem exists_local_variational_ODE_solution [CompleteSpace E]
    {F : E → E} {z₀ : E} {U : Set E}
    (hF : ContDiffAt ℝ 2 F z₀) (hU : IsOpen U) (hz₀ : z₀ ∈ U) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ φ : E → ℝ → E,
      ∃ V : E → ℝ → E →L[ℝ] E, ∃ C : ℝ≥0,
      ContinuousOn (Function.uncurry φ)
        (Metric.closedBall z₀ r ×ˢ Set.Icc (-ε) ε) ∧
      ContinuousOn (Function.uncurry V)
        (Metric.closedBall z₀ r ×ˢ Set.Icc (-ε) ε) ∧
      (∀ z ∈ Metric.closedBall z₀ r, φ z 0 = z ∧ V z 0 = ContinuousLinearMap.id ℝ E) ∧
      (∀ z ∈ Metric.closedBall z₀ r, ∀ t ∈ Set.Icc (-ε) ε,
        φ z t ∈ U ∧ HasDerivAt (φ z) (F (φ z t)) t ∧
          HasDerivAt (V z) ((fderiv ℝ F (φ z t)).comp (V z t)) t) ∧
      (∀ z ∈ Metric.closedBall z₀ r, ∀ z' ∈ Metric.closedBall z₀ r,
        ∀ t ∈ Set.Icc (-ε) ε, ‖φ z' t - φ z t‖ ≤ (C : ℝ) * ‖z' - z‖) := by
  let p₀ : E × (E →L[ℝ] E) := (z₀, ContinuousLinearMap.id ℝ E)
  obtain ⟨τ, hτ, a, r₀, L₀, K₀, hr₀, hPL⟩ :=
    IsPicardLindelof.of_contDiffAt_one (odeVariationField_contDiffAt hF)
  obtain ⟨ψ, hψ, C, hψLip⟩ :=
    (hPL 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
  let φ : E → ℝ → E := fun z t => (ψ (z, ContinuousLinearMap.id ℝ E) t).1
  let V : E → ℝ → E →L[ℝ] E := fun z t => (ψ (z, ContinuousLinearMap.id ℝ E) t).2
  have hr₀R : (0 : ℝ) < r₀ := by exact_mod_cast hr₀
  have hψc : ContinuousOn (Function.uncurry ψ)
      (Metric.closedBall p₀ (r₀ : ℝ) ×ˢ Set.Icc (0 - τ) (0 + τ)) := by
    apply continuousOn_prod_of_continuousOn_lipschitzOnWith _ C _ hψLip
    exact fun p hp => HasDerivWithinAt.continuousOn (hψ p hp).2
  have hdomain : Metric.closedBall p₀ (r₀ : ℝ) ×ˢ Set.Icc (0 - τ) (0 + τ)
      ∈ 𝓝 (p₀, (0 : ℝ)) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod (Metric.closedBall_mem_nhds p₀ hr₀R)
      (Icc_mem_nhds (by linarith) (by linarith))
  have hψat : ContinuousAt (Function.uncurry ψ) (p₀, (0 : ℝ)) :=
    hψc.continuousAt hdomain
  let κ : E × ℝ → (E × (E →L[ℝ] E)) × ℝ :=
    fun q => ((q.1, ContinuousLinearMap.id ℝ E), q.2)
  have hκ : Continuous κ := by fun_prop
  have hκat : ContinuousAt κ (z₀, (0 : ℝ)) := hκ.continuousAt
  have hψatκ : ContinuousAt (Function.uncurry ψ) (κ (z₀, (0 : ℝ))) := hψat
  have hφat : ContinuousAt (Function.uncurry φ) (z₀, (0 : ℝ)) :=
    (hψatκ.comp hκat).fst
  have hφ0 : φ z₀ 0 = z₀ :=
    congrArg Prod.fst (hψ p₀ (Metric.mem_closedBall_self r₀.coe_nonneg)).1
  have hvalue : Function.uncurry φ (z₀, (0 : ℝ)) ∈ U := by
    change φ z₀ 0 ∈ U
    rw [hφ0]
    exact hz₀
  have hpre : (Function.uncurry φ) ⁻¹' U ∈ 𝓝 (z₀, (0 : ℝ)) :=
    hφat.preimage_mem_nhds (hU.mem_nhds hvalue)
  rw [nhds_prod_eq] at hpre
  obtain ⟨W, hW, J, hJ, hWJ⟩ := Filter.mem_prod_iff.mp hpre
  obtain ⟨δ, hδ, hδW⟩ := Metric.mem_nhds_iff.mp hW
  obtain ⟨η, hη, hηJ⟩ := Metric.mem_nhds_iff.mp hJ
  let r : ℝ := min (δ / 2) (r₀ : ℝ)
  let ε : ℝ := min (η / 2) (τ / 2)
  have hr : 0 < r := lt_min (half_pos hδ) hr₀R
  have hε : 0 < ε := lt_min (half_pos hη) (half_pos hτ)
  have hrδ : r < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hrr₀ : r ≤ (r₀ : ℝ) := min_le_right _ _
  have hεη : ε < η := (min_le_left _ _).trans_lt (half_lt_self hη)
  have hετ : ε < τ := (min_le_right _ _).trans_lt (half_lt_self hτ)
  have hlift : ∀ z ∈ Metric.closedBall z₀ r,
      (z, ContinuousLinearMap.id ℝ E) ∈ Metric.closedBall p₀ (r₀ : ℝ) := by
    intro z hz
    rw [Metric.mem_closedBall, Prod.dist_eq, dist_self, max_le_iff]
    exact ⟨(Metric.mem_closedBall.mp hz).trans hrr₀, r₀.coe_nonneg⟩
  have hzW : ∀ z ∈ Metric.closedBall z₀ r, z ∈ W :=
    fun z hz => hδW (Metric.closedBall_subset_ball hrδ hz)
  have htJ : ∀ t ∈ Set.Icc (-ε) ε, t ∈ J := by
    intro t ht
    apply hηJ
    rw [Real.ball_eq_Ioo]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have htτ : ∀ t ∈ Set.Icc (-ε) ε, t ∈ Set.Ioo (0 - τ) (0 + τ) := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hsmall : ContinuousOn (fun q : E × ℝ => ψ (q.1, ContinuousLinearMap.id ℝ E) q.2)
      (Metric.closedBall z₀ r ×ˢ Set.Icc (-ε) ε) :=
    hψc.comp hκ.continuousOn (fun q hq => ⟨hlift q.1 hq.1, Set.Ioo_subset_Icc_self (htτ q.2 hq.2)⟩)
  refine ⟨r, hr, ε, hε, φ, V, C, hsmall.fst, hsmall.snd, ?_, ?_, ?_⟩
  · intro z hz
    exact ⟨congrArg Prod.fst (hψ _ (hlift z hz)).1,
      congrArg Prod.snd (hψ _ (hlift z hz)).1⟩
  · intro z hz t ht
    have hd := ((hψ _ (hlift z hz)).2 t (Set.Ioo_subset_Icc_self (htτ t ht))).hasDerivAt
      (Icc_mem_nhds (htτ t ht).1 (htτ t ht).2)
    have himg : φ z t ∈ U := by
      change (z, t) ∈ (Function.uncurry φ) ⁻¹' U
      exact hWJ ⟨hzW z hz, htJ t ht⟩
    refine ⟨himg, ?_, ?_⟩
    · simpa only [φ, odeVariationField, Function.comp_def, ContinuousLinearMap.coe_fst'] using
        (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E)).hasFDerivAt.comp_hasDerivAt t hd
    · simpa only [φ, V, odeVariationField, Function.comp_def, ContinuousLinearMap.coe_snd'] using
        (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E)).hasFDerivAt.comp_hasDerivAt t hd
  · intro z hz z' hz' t ht
    have hl := (hψLip t (Set.Ioo_subset_Icc_self (htτ t ht))).norm_sub_le (hlift z' hz') (hlift z hz)
    have hnorm : ‖(z', ContinuousLinearMap.id ℝ E) - (z, ContinuousLinearMap.id ℝ E)‖ = ‖z' - z‖ := by
      rw [Prod.norm_def]
      change max ‖z' - z‖ ‖(ContinuousLinearMap.id ℝ E) - ContinuousLinearMap.id ℝ E‖ = _
      rw [sub_self, norm_zero, max_eq_left (norm_nonneg _)]
    rw [hnorm] at hl
    have hfirst : ‖φ z' t - φ z t‖ ≤
        ‖ψ (z', ContinuousLinearMap.id ℝ E) t - ψ (z, ContinuousLinearMap.id ℝ E) t‖ := by
      rw [Prod.norm_def]
      exact le_max_left _ _
    exact hfirst.trans hl


/-- A C2 autonomous vector field has a genuine C1 local flow with the actual
initial-state derivative given by its first-variation ODE. All regularity is
proved from Picard, Taylor remainder and Gronwall, without a flow premise. -/
theorem exists_C1_local_ODE_flow [CompleteSpace E]
    {F : E → E} {z₀ : E} {U : Set E}
    (hF : ContDiffAt ℝ 2 F z₀) (hU : IsOpen U) (hz₀ : z₀ ∈ U) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ φ : E → ℝ → E,
      ∃ V : E → ℝ → E →L[ℝ] E,
      ContDiffOn ℝ 1 (Function.uncurry φ) (Metric.ball z₀ r ×ˢ Set.Ioo (-ε) ε) ∧
      ContinuousOn (Function.uncurry V) (Metric.ball z₀ r ×ˢ Set.Ioo (-ε) ε) ∧
      (∀ z ∈ Metric.ball z₀ r, φ z 0 = z ∧ V z 0 = ContinuousLinearMap.id ℝ E) ∧
      (∀ z ∈ Metric.ball z₀ r, ∀ t ∈ Set.Ioo (-ε) ε,
        φ z t ∈ U ∧ HasDerivAt (φ z) (F (φ z t)) t ∧
          HasDerivAt (V z) ((fderiv ℝ F (φ z t)).comp (V z t)) t) ∧
      (∀ p ∈ Metric.ball z₀ r ×ˢ Set.Ioo (-ε) ε,
        HasFDerivAt (fun z => φ z p.2) (V p.1 p.2) p.1) ∧
      (∀ p ∈ Metric.ball z₀ r ×ˢ Set.Ioo (-ε) ε,
        HasFDerivAt (Function.uncurry φ)
          ((V p.1 p.2).coprod (ContinuousLinearMap.toSpanSingleton ℝ (F (φ p.1 p.2)))) p) := by
  let D := fderiv ℝ F
  have hDC1 : ContDiffAt ℝ 1 D z₀ := hF.fderiv_right (by norm_num)
  obtain ⟨L, W, hW, hDLip⟩ := hDC1.exists_lipschitzOnWith
  have hFderiv : ∀ᶠ x in 𝓝 z₀, HasFDerivAt F (D x) x :=
    (hF.eventually (by simp)).mono (fun x hx =>
      (hx.differentiableAt (by norm_num)).hasFDerivAt)
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (hU.mem_nhds hz₀) (Filter.inter_mem hW hFderiv))
  let B := Metric.ball z₀ ρ
  have hBU : B ⊆ U := fun x hx => (hρsub hx).1
  have hFB : ∀ x ∈ B, HasFDerivAt F (D x) x := fun x hx => (hρsub hx).2.2
  have hDB : LipschitzOnWith L D B := hDLip.mono (fun x hx => (hρsub hx).2.1)
  let K := ‖D z₀‖ + (L : ℝ) * ρ + 1
  have hK : 0 < K := by dsimp only [K]; positivity
  have hDK : ∀ x ∈ B, ‖D x‖ ≤ K := by
    intro x hx
    have hnorm : ‖x - z₀‖ ≤ ρ := by
      simpa only [dist_eq_norm] using (Metric.mem_ball.mp hx).le
    calc
      ‖D x‖ ≤ ‖D x - D z₀‖ + ‖D z₀‖ := norm_le_norm_sub_add _ _
      _ ≤ (L : ℝ) * ‖x - z₀‖ + ‖D z₀‖ :=
        add_le_add (hDB.norm_sub_le hx (Metric.mem_ball_self hρ)) le_rfl
      _ ≤ (L : ℝ) * ρ + ‖D z₀‖ := by gcongr
      _ ≤ K := by dsimp only [K]; linarith
  obtain ⟨r, hr, ε, hε, φ, V, C, hφc, hVc, hinit, hsol, hLip⟩ :=
    exists_local_variational_ODE_solution hF Metric.isOpen_ball (Metric.mem_ball_self hρ)
  let Q := Metric.ball z₀ r ×ˢ Set.Ioo (-ε) ε
  let Qc := Metric.closedBall z₀ r ×ˢ Set.Icc (-ε) ε
  have hQopen : IsOpen Q := Metric.isOpen_ball.prod isOpen_Ioo
  have hQQc : Q ⊆ Qc := fun p hp =>
    ⟨Metric.ball_subset_closedBall hp.1, Set.Ioo_subset_Icc_self hp.2⟩
  let B₀ := (L : ℝ) * (C : ℝ) ^ 2 / K * Real.exp (K * ε) + 1
  have hB₀ : 0 < B₀ := by dsimp only [B₀]; positivity
  have hquad := norm_ODEVariation_remainder_le hε.le hK (convex_ball z₀ ρ) hFB hDB hDK
    (fun z hz t ht => (hsol z hz t ht).2.1)
    (fun z hz t ht => (hsol z hz t ht).2.2)
    (fun z hz => (hinit z hz).1) (fun z hz => (hinit z hz).2)
    (fun z hz t ht => (hsol z hz t ht).1) hLip
  have hspace : ∀ p ∈ Q, HasFDerivAt (fun z => φ z p.2) (V p.1 p.2) p.1 := by
    intro p hp
    apply hasFDerivAt_of_quadratic_remainder_on_closedBall hp.1 hB₀.le
    intro z hz
    exact hquad p.1 (Metric.ball_subset_closedBall hp.1) z hz p.2 (Set.Ioo_subset_Icc_self hp.2)
  have htime : ∀ p ∈ Q, HasDerivAt (φ p.1) (F (φ p.1 p.2)) p.2 :=
    fun p hp => (hsol p.1 (hQQc hp).1 p.2 (hQQc hp).2).2.1
  have hFc : ContinuousOn F B := fun x hx => (hFB x hx).continuousAt.continuousWithinAt
  have hbc : ContinuousOn (fun p : E × ℝ => F (φ p.1 p.2)) Q :=
    hFc.comp (hφc.mono hQQc) (fun p hp => (hsol p.1 (hQQc hp).1 p.2 (hQQc hp).2).1)
  have hC1 := contDiffOn_of_continuous_ODEVariation_partials
    (φ := φ) (V := V) (b := fun z t => F (φ z t)) hQopen hspace htime
    (hVc.mono hQQc) hbc
  refine ⟨r, hr, ε, hε, φ, V, hC1.1, hVc.mono hQQc, ?_, ?_, hspace, hC1.2⟩
  · intro z hz
    exact hinit z (Metric.ball_subset_closedBall hz)
  · intro z hz t ht
    have h := hsol z (Metric.ball_subset_closedBall hz) t (Set.Ioo_subset_Icc_self ht)
    exact ⟨hBU h.1, h.2⟩

end ODEVariation
end Yau.LeafProofs.L12Aux
