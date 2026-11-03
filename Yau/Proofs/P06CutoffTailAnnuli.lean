import Yau.Proofs.P06CutoffTailGeometry

noncomputable section
open MeasureTheory Filter Finset
open scoped Topology InnerProductSpace ComplexOrder

namespace Yau.NodeProofs.P06Aux.CutoffTail
open Yau Yau.LeafProofs Yau.LeafProofs.L03 Davies
variable {n k : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

def ballProjection (g : SmoothMetric M) (μ : Measure M.Carrier) (o : M.Carrier) (m : ℕ) :
    L2FormHilbert g μ k →L[ℝ] L2FormHilbert g μ k :=
  indicator g μ (distBall g.form o (radius m)) (L12Aux.measurableSet_distBall g o (radius m))

def annulus (g : SmoothMetric M) (o : M.Carrier) (m : ℕ) : Set M.Carrier :=
  distBall g.form o (radius (m + 1)) \ distBall g.form o (radius m)

theorem annulus_measurable (g : SmoothMetric M) (o : M.Carrier) (m : ℕ) :
    MeasurableSet (annulus g o m) :=
  (L12Aux.measurableSet_distBall g o _).diff (L12Aux.measurableSet_distBall g o _)

def shell (g : SmoothMetric M) (μ : Measure M.Carrier) (o : M.Carrier) (m : ℕ) :
    L2FormHilbert g μ k →L[ℝ] L2FormHilbert g μ k :=
  indicator g μ (annulus g o m) (annulus_measurable g o m)

theorem dyadic_ball_mono (g : SmoothMetric M) (o : M.Carrier) {m q : ℕ} (hmq : m ≤ q) :
    distBall g.form o (radius m) ⊆ distBall g.form o (radius q) := by
  intro x hx
  exact (L12Aux.mem_distBall_iff g o x (radius_pos q)).mpr
    (((L12Aux.mem_distBall_iff g o x (radius_pos m)).mp hx).trans_le (radius_mono hmq))

theorem shell_eq_sub (g : SmoothMetric M) (μ : Measure M.Carrier) (o : M.Carrier)
    (m : ℕ) (u : L2FormHilbert g μ k) :
    shell g μ o m u = ballProjection g μ o (m + 1) u - ballProjection g μ o m u :=
  indicator_diff g μ _ _ _ _ (dyadic_ball_mono g o (Nat.le_succ m)) u

theorem shell_supported_outside (g : SmoothMetric M) (μ : Measure M.Carrier) (o : M.Carrier)
    (m : ℕ) (u : L2FormHilbert g μ k) :
    indicator g μ (distBall g.form o (radius m))ᶜ
      (L12Aux.measurableSet_distBall g o (radius m)).compl (shell g μ o m u) = shell g μ o m u := by
  have hsub : annulus g o m ⊆ (distBall g.form o (radius m))ᶜ := fun x hx => hx.2
  simpa only [shell, Set.inter_eq_right.mpr hsub] using
    indicator_inter g μ _ _ (L12Aux.measurableSet_distBall g o (radius m)).compl
      (annulus_measurable g o m) u

theorem shell_norm_le_ball (g : SmoothMetric M) (μ : Measure M.Carrier) (o : M.Carrier)
    (m : ℕ) (u : L2FormHilbert g μ k) :
    ‖shell g μ o m u‖ ≤ ‖ballProjection g μ o (m + 1) u‖ :=
  indicator_norm_mono g μ _ _ (annulus_measurable g o m)
    (L12Aux.measurableSet_distBall g o _) Set.sdiff_subset u

/-- Exact finite dyadic annular decomposition in the genuine completion. -/
theorem sum_shell (g : SmoothMetric M) (μ : Measure M.Carrier) (o : M.Carrier)
    (u : L2FormHilbert g μ k) (J N : ℕ) (hJN : J ≤ N) :
    ∑ m ∈ Finset.Ico J N, shell g μ o m u =
      ballProjection g μ o N u - ballProjection g μ o J u := by
  induction N, hJN using Nat.le_induction with
  | base => simp
  | succ N hJN ih =>
      rw [Finset.sum_Ico_succ_top hJN, ih, shell_eq_sub]
      abel

/-- Uniform inward heat bound for a single dyadic annulus. -/
theorem shell_heat_bound
    (g : SmoothMetric M) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (o : M.Carrier) (D : RealForm M k) (hD : L2RealForm g.form μ D)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ x, formNormSq g.form D x ≤ B ^ 2)
    (A : ℝ) (hA : 1 ≤ A)
    (htail : ∀ (r R : ℝ), 0 < r → r < R → ∀ t, 0 < t →
      ∀ f : L2FormHilbert g μ k,
      indicator g μ (distBall g.form o r) (L12Aux.measurableSet_distBall g o r) f = f →
      ‖indicator g μ (distBall g.form o R)ᶜ
        (L12Aux.measurableSet_distBall g o R).compl (hodgeHeatHilbert g μ hμ k t f)‖ ≤
        Real.exp (-(R - r) ^ 2 / (2 * A ^ 2 * t)) * ‖f‖)
    (r T : ℝ) (hr : 0 < r) (hT : 0 < T) (m : ℕ) (hsep : 2 * r ≤ radius m)
    (t : ℝ) (ht : 0 < t) (htT : t ≤ T) :
    ‖indicator g μ (distBall g.form o r) (L12Aux.measurableSet_distBall g o r)
      (hodgeHeatHilbert g μ hμ k t (shell g μ o m (realizeActualForm g μ D hD)))‖ ≤
      (B * 2 ^ n * Real.sqrt (μ.real (distBall g.form o 1))) *
        (radius m ^ n * Real.exp (-(1 / (8 * A ^ 2 * T)) * radius m)) := by
  have hApos := zero_lt_one.trans_le hA
  have he := reverse_annular_tail g μ hμ o A hA htail r (radius m) t hr
    (by linarith) ht (shell g μ o m (realizeActualForm g μ D hD))
    (shell_supported_outside g μ o m _)
  have hnorm := (shell_norm_le_ball g μ o m (realizeActualForm g μ D hD)).trans
    (indicator_realize_polynomial_bound g hK hRic μ hμ o D hD B hB hb
      (radius (m + 1)) (one_le_radius _))
  have hgauss := gaussian_le_exponential hApos hT ht htT (one_le_radius m) hsep
  calc
    _ ≤ Real.exp (-(radius m - r) ^ 2 / (2 * A ^ 2 * t)) *
        ‖shell g μ o m (realizeActualForm g μ D hD)‖ := he
    _ ≤ Real.exp (-(1 / (8 * A ^ 2 * T)) * radius m) *
        (B * radius (m + 1) ^ n * Real.sqrt (μ.real (distBall g.form o 1))) :=
      mul_le_mul hgauss hnorm (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by rw [radius_succ, mul_pow]; ring

/-- Remote compactly supported bounded data are uniformly small on the
fixed inner ball, for the entire interval `0 < t ≤ T`. -/
theorem exists_uniform_local_tail
    (g : SmoothMetric M) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (o : M.Carrier) (r T B : ℝ) (hr : 0 < r) (hT : 0 < T) (hB : 0 ≤ B)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ J : ℕ, ∀ (D : RealForm M k) (hD : L2RealForm g.form μ D),
      CompactlySupportedRealForm D → (∀ x, formNormSq g.form D x ≤ B ^ 2) →
      ballProjection g μ o J (realizeActualForm g μ D hD) = 0 →
      ∀ t, 0 < t → t ≤ T →
      ‖indicator g μ (distBall g.form o r) (L12Aux.measurableSet_distBall g o r)
        (hodgeHeatHilbert g μ hμ k t (realizeActualForm g μ D hD))‖ < ε := by
  obtain ⟨A, hA, htail⟩ := exists_uniform_annular_heat_L2_tail n
  let a := 1 / (8 * A ^ 2 * T)
  have ha : 0 < a := by dsimp only [a]; have := zero_lt_one.trans_le hA; positivity
  let C := B * 2 ^ n * Real.sqrt (μ.real (distBall g.form o 1))
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  obtain ⟨J₁, hJ₁⟩ := exists_small_finite_dyadic_tail n ha C hC hε
  obtain ⟨J₀, hJ₀⟩ := eventually_atTop.mp
    (radius_tendsto.eventually (eventually_ge_atTop (2 * r)))
  refine ⟨max J₀ J₁, ?_⟩
  intro D hD hcD hb hzero t ht htT
  let f := realizeActualForm g μ D hD
  obtain ⟨N, hN, hJN⟩ := (compactlySupported_indicator_eventually_self g μ o D hD hcD).and
    (eventually_ge_atTop (max J₀ J₁)) |>.exists
  change ballProjection g μ o N f = f at hN
  change ballProjection g μ o (max J₀ J₁) f = 0 at hzero
  have hdecomp : (∑ m ∈ Finset.Ico (max J₀ J₁) N, shell g μ o m f) = f := by
    rw [sum_shell g μ o f _ _ hJN, hN, hzero, sub_zero]
  let P := indicator (k := k) g μ (distBall g.form o r) (L12Aux.measurableSet_distBall g o r)
  let S := hodgeHeatHilbert g μ hμ k t
  calc
    ‖P (S f)‖ = ‖∑ m ∈ Finset.Ico (max J₀ J₁) N, P (S (shell g μ o m f))‖ := by
      rw [← map_sum, ← map_sum, hdecomp]
    _ ≤ ∑ m ∈ Finset.Ico (max J₀ J₁) N, ‖P (S (shell g μ o m f))‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ Finset.Ico (max J₀ J₁) N,
        C * (radius m ^ n * Real.exp (-a * radius m)) := by
      apply Finset.sum_le_sum
      intro m hm
      exact shell_heat_bound g hK hRic μ hμ o D hD B hB hb A hA
        (htail M g μ hμ k o) r T hr hT m
        (hJ₀ m ((le_max_left J₀ J₁).trans (Finset.mem_Ico.mp hm).1)) t ht htT
    _ < ε := hJ₁ _ (fun m hm => (le_max_right J₀ J₁).trans (Finset.mem_Ico.mp hm).1)

end Yau.NodeProofs.P06Aux.CutoffTail
