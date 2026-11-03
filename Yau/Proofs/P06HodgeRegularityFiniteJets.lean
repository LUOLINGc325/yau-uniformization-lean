import Yau.Proofs.P06HodgeRegularityCalculus
import Yau.LeafProofs.L16CoordinateRegularity

/-! Finite-order Sobolev reconstruction on genuine finite real coordinates.
Only the available finite weak jet is used to obtain a finite C^q representative. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux
open Yau.LeafProofs.L16Aux

private theorem regularity_uniformLimit_exists {X : Type*} {f : ℕ → X → ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k ≥ N, ∀ l ≥ N, ∀ x,
      |f k x - f l x| < ε) :
    ∃ g : X → ℝ, TendstoUniformly f g atTop := by
  have hc (x : X) : CauchySeq (fun k => f k x) := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := h ε hε
    exact ⟨N, fun k hk l hl => by simpa only [Real.dist_eq] using hN k hk l hl x⟩
  choose g hg using fun x => cauchySeq_tendsto_of_complete (hc x)
  refine ⟨g, tendstoUniformlyOn_univ.mp ?_⟩
  apply UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto
  · apply Metric.uniformCauchySeqOn_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := h ε hε
    exact ⟨N, fun k hk l hl x _ => by simpa only [Real.dist_eq] using hN k hk l hl x⟩
  · exact fun x _ => hg x

private theorem regularity_uniformly_finite_pi {I X : Type*} [Fintype I]
    {f : ℕ → X → I → ℝ} {g : X → I → ℝ}
    (h : ∀ i, TendstoUniformly (fun k x => f k x i) (fun x => g x i) atTop) :
    TendstoUniformly f g atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have hi : ∀ i, ∀ᶠ k in atTop, ∀ x, dist (g x i) (f k x i) < ε :=
    fun i => Metric.tendstoUniformly_iff.mp (h i) ε hε
  filter_upwards [eventually_all.mpr hi] with k hk
  intro x
  exact (dist_pi_lt_iff hε).mpr (fun i => hk i x)

/-- A uniformly Cauchy finite family of actual coordinate jets reconstructs
exactly C^q regularity and every actual derivative through order q. -/
theorem regularity_finite_coordinate_uniformLimit {d q : ℕ}
    {f : ℕ → (Fin d → ℝ) → ℝ} (hf : ∀ k, ContDiff ℝ ∞ (f k))
    (hcauchy : ∀ w : List (Fin d), w.length ≤ q → ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ k ≥ N, ∀ l ≥ N, ∀ x,
        |coordinateWordDerivative (f k) w x - coordinateWordDerivative (f l) w x| < ε) :
    ∃ v : (Fin d → ℝ) → ℝ, ContDiff ℝ q v ∧
      ∀ w : List (Fin d), w.length ≤ q → TendstoUniformly
        (fun k => coordinateWordDerivative (f k) w) (coordinateWordDerivative v w) atTop := by
  classical
  have hex (w : List (Fin d)) : ∃ F : (Fin d → ℝ) → ℝ,
      w.length ≤ q → TendstoUniformly (fun k => coordinateWordDerivative (f k) w) F atTop := by
    by_cases hw : w.length ≤ q
    · obtain ⟨F, hF⟩ := regularity_uniformLimit_exists (hcauchy w hw)
      exact ⟨F, fun _ => hF⟩
    · exact ⟨0, fun h => (hw h).elim⟩
  choose F hF using hex
  let e := ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) (Fin d)
  have he (L : (Fin d → ℝ) →L[ℝ] ℝ) (i : Fin d) : e L i = L (Pi.single i 1) := rfl
  have hdlim (w : List (Fin d)) (hw : w.length < q) : TendstoUniformly
      (fun k x => fderiv ℝ (coordinateWordDerivative (f k) w) x)
      (fun x => e.symm (fun i => F (i :: w) x)) atTop := by
    have hpi : TendstoUniformly
        (fun k x i => coordinateWordDerivative (f k) (i :: w) x)
        (fun x i => F (i :: w) x) atTop :=
      regularity_uniformly_finite_pi (fun i => hF (i :: w) (by simp; omega))
    convert e.symm.toContinuousLinearMap.uniformContinuous.comp_tendstoUniformly hpi using 1
    · funext k x
      exact (e.symm_apply_apply (fderiv ℝ (coordinateWordDerivative (f k) w) x)).symm
    · rfl
  have hd (w : List (Fin d)) (hw : w.length < q) (x : Fin d → ℝ) :
      HasFDerivAt (F w) (e.symm (fun i => F (i :: w) x)) x :=
    hasFDerivAt_of_tendstoUniformly (hdlim w hw)
      (fun k x => ((contDiff_coordinateWordDerivative (hf k) w).differentiable (by simp) x).hasFDerivAt)
      (fun x => (hF w hw.le).tendsto_at x) x
  have hfd (w : List (Fin d)) (hw : w.length < q) :
      fderiv ℝ (F w) = fun x => e.symm (fun i => F (i :: w) x) :=
    funext (fun x => (hd w hw x).fderiv)
  have hCn : ∀ s : ℕ, ∀ w : List (Fin d), s + w.length ≤ q → ContDiff ℝ s (F w) := by
    intro s
    induction s with
    | zero =>
        intro w hw
        exact contDiff_zero.mpr ((hF w (by omega)).continuous
          (Eventually.of_forall fun k => (contDiff_coordinateWordDerivative (hf k) w).continuous).frequently)
    | succ s ih =>
        intro w hw
        rw [show ((s + 1 : ℕ) : ℕ∞ω) = (s : ℕ∞ω) + 1 by simp, contDiff_succ_iff_fderiv]
        refine ⟨fun x => (hd w (by omega) x).differentiableAt, by simp, ?_⟩
        rw [hfd w (by omega)]
        exact e.symm.contDiff.comp (contDiff_pi.mpr fun i => ih (i :: w) (by simp; omega))
  have hword : ∀ w : List (Fin d), w.length ≤ q → coordinateWordDerivative (F []) w = F w := by
    intro w
    induction w with
    | nil => intro _; rfl
    | cons i w ih =>
        intro hw
        have hw0 : w.length ≤ q := by simp only [List.length_cons] at hw; omega
        simp only [coordinateWordDerivative, ih hw0]
        funext x
        rw [hfd w (by simp only [List.length_cons] at hw; omega)]
        exact (he _ i).symm.trans (congrFun (e.apply_symm_apply (fun i => F (i :: w) x)) i)
  refine ⟨F [], hCn q [] (by simp), ?_⟩
  intro w hw
  rw [hword w hw]
  exact hF w hw

/-- A finite weak jet of order at least q+d has a genuine C^q representative.
The construction keeps the original raw function up to Lebesgue AE equality. -/
theorem regularity_finite_weak_jet_representative {d N q : ℕ}
    {ρ u : (Fin d → ℝ) → ℝ} {J : List (Fin d) → (Fin d → ℝ) → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hρ0 : ∀ z, 0 ≤ ρ z) (hρ1 : (∫ z, ρ z) = 1)
    (hJ : FiniteCoordinateWeakJet N u J) (hN : q + d ≤ N) :
    ∃ v : (Fin d → ℝ) → ℝ, ContDiff ℝ q v ∧ v =ᵐ[volume] u ∧
      ∀ w : List (Fin d), w.length ≤ q → TendstoUniformly
        (fun k => coordinateWordDerivative (coordinateMollify ρ k u) w)
        (coordinateWordDerivative v w) atTop := by
  have hu : MemLp u 2 volume ∧ HasCompactSupport u := by
    simpa only [List.length_nil, hJ.1] using hJ.2.1 [] (Nat.zero_le N)
  have hui := Yau.LeafProofs.L03.memLp_two_compact_integrable volume u hu.1 hu.2
  obtain ⟨v, hv, hlim⟩ := regularity_finite_coordinate_uniformLimit (q := q)
    (fun k => coordinateMollify_smooth hρ hcρ hui k)
    (fun w hw => coordinateWordDerivative_coordinateMollify_uniformCauchy
      hρ hcρ hρ0 hρ1 hJ w (by omega))
  have hL2 : Tendsto (fun k => ∫ z, (coordinateMollify ρ k u z - u z)^2)
      atTop (𝓝 0) := by
    simpa only [Real.norm_eq_abs, sq_abs] using coordinateMollify_L2_tendsto hρ hcρ hρ0 hρ1 hu.1 hu.2
  refine ⟨v, hv, ?_, hlim⟩
  exact ae_eq_of_pointwise_tendsto_of_integral_sq_sub_tendsto_zero
    (fun k => coordinateMollify_memLp hρ0 hρ1 hu.1 hu.2 k) hu.1 hv.continuous.aestronglyMeasurable
    (fun z => (hlim [] (by simp)).tendsto_at z) hL2


/-- The finite representative's actual coordinate derivatives retain the
explicit mixed-Sobolev bound. Its right side contains only genuine weak jets. -/
theorem regularity_finite_weak_jet_bound {d N q : ℕ}
    {ρ u v : (Fin d → ℝ) → ℝ} {J : List (Fin d) → (Fin d → ℝ) → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hρ0 : ∀ z, 0 ≤ ρ z) (hρ1 : (∫ z, ρ z) = 1)
    (hJ : FiniteCoordinateWeakJet N u J) (hN : q + d ≤ N)
    (hlim : ∀ w : List (Fin d), w.length ≤ q → TendstoUniformly
      (fun k => coordinateWordDerivative (coordinateMollify ρ k u) w)
      (coordinateWordDerivative v w) atTop)
    (w : List (Fin d)) (hw : w.length ≤ q) (z : Fin d → ℝ) :
    (coordinateWordDerivative v w z)^2 ≤
      ∑ s : Finset (Fin d), ∫ y, (J (s.sort (· ≤ ·) ++ w) y)^2 := by
  classical
  have hu : MemLp u 2 volume ∧ HasCompactSupport u := by
    simpa only [List.length_nil, hJ.1] using hJ.2.1 [] (Nat.zero_le N)
  have hui := Yau.LeafProofs.L03.memLp_two_compact_integrable volume u hu.1 hu.2
  let f : ℕ → (Fin d → ℝ) → ℝ :=
    fun k => coordinateWordDerivative (coordinateMollify ρ k u) w
  let W : Finset (Fin d) → List (Fin d) := fun s => s.sort (· ≤ ·) ++ w
  have hW (s : Finset (Fin d)) : (W s).length ≤ N := by
    have hs : s.card ≤ d := by simpa only [Fintype.card_fin] using s.card_le_univ
    simp only [W, List.length_append, Finset.length_sort]
    omega
  have hmix (k : ℕ) (s : Finset (Fin d)) :
      mixedDerivative (f k) s = coordinateMollify ρ k (J (W s)) := by
    change coordinateWordDerivative
      (coordinateWordDerivative (coordinateMollify ρ k u) w) (s.sort (· ≤ ·)) = _
    rw [coordinateWordDerivative_append]
    exact coordinateWordDerivative_coordinateMollify hρ hcρ hJ k (W s) (hW s)
  have hs (s : Finset (Fin d)) : Tendsto
      (fun k => ∫ y, (mixedDerivative (f k) s y)^2) atTop
      (𝓝 (∫ y, (J (W s) y)^2)) := by
    simp_rw [hmix]
    have ht := regularityToLp_tendsto volume
      (fun k => coordinateMollify ρ k (J (W s))) (J (W s))
      (fun k => coordinateMollify_memLp hρ0 hρ1 (hJ.2.1 _ (hW s)).1 (hJ.2.1 _ (hW s)).2 k)
      (hJ.2.1 _ (hW s)).1
      (coordinateMollify_L2_tendsto hρ hcρ hρ0 hρ1
        (hJ.2.1 _ (hW s)).1 (hJ.2.1 _ (hW s)).2)
    simpa only [regularityToLp_norm_sq] using ht.norm.pow 2
  have hleft := ((hlim w hw).tendsto_at z).pow 2
  have hright := tendsto_finsetSum Finset.univ (fun s _ => hs s)
  apply le_of_tendsto_of_tendsto hleft hright
  apply Eventually.of_forall
  intro k
  exact sq_le_sum_integral_sq_mixedDerivative
    (contDiff_coordinateWordDerivative (coordinateMollify_smooth hρ hcρ hui k) w)
    (hasCompactSupport_coordinateWordDerivative (coordinateMollify_compact hcρ hu.2 k) w) z

end Yau.NodeProofs.P06Aux
