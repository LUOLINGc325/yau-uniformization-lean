import Yau.LeafProofs.L19HeatGaussianTailDoubleBall
import Yau.LeafProofs.L19HeatMarkovPositivity

/-! Pointwise Gaussian tails for genuine smooth nonnegative representatives
of the actual scalar heat family. The representative is an intermediate
regularity interface; its existence is proved separately. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace ComplexOrder
namespace Yau.LeafProofs.L19Aux
open L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem nonnegativeHeatSolution_harnack
    (hLY : LeafCandidates.LiYauDifferential) (g : SmoothMetric M)
    (hcomplete : IsComplete g) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef)
    {u : M.Carrier → ℝ → ℝ} (hu : SmoothSpaceTime u (Set.Ioi 0))
    (hn : ∀ x t, 0 < t → 0 ≤ u x t)
    (heq : ∀ x t, 0 < t → deriv (u x) t = laplacian g.form (fun y => u y t) x)
    {s t : ℝ} (hs : 0 < s) (hst : s < t) (x y : M.Carrier) :
    u x s ≤ (t / s) ^ n * Real.exp (inducedDistance g.form x y ^ 2 / (2 * (t - s))) * u y t := by
  let K := (t / s) ^ n * Real.exp (inducedDistance g.form x y ^ 2 / (2 * (t - s)))
  have ht : 0 < t := hs.trans hst
  have hKpos : 0 < K := by dsimp only [K]; positivity
  apply le_of_forall_pos_le_add
  intro ε hε
  have huε : LeafCandidates.PositiveHeatSolution g.form (fun x t => u x t + ε / K) := by
    constructor
    · intro a
      exact (hu a).add contDiffOn_const
    · intro z τ hτ
      refine ⟨add_pos_of_nonneg_of_pos (hn z τ hτ) (div_pos hε hKpos), ?_⟩
      rw [laplacian_add_const g.form (smoothSpaceTime_slice hu hτ) (ε / K) z]
      have hd := (smoothSpaceTime_time_contDiffAt hu z (Ioi_mem_nhds hτ)).differentiableAt
        (by simp)
      rw [hd.hasDerivAt.add_const (ε / K) |>.deriv]
      exact heq z τ hτ
  have hh := positiveHeatSolution_harnack hLY g hcomplete hK hRic huε hs hst x y
  change u x s + ε / K ≤ K * (u y t + ε / K) at hh
  have hc : K * (ε / K) = ε := mul_div_cancel₀ ε hKpos.ne'
  nlinarith [div_nonneg hε.le hKpos.le]

/-- Bishop--Gromov bounds the inverse unit-ball volume at a moving center
by a polynomial in its distance to a fixed center. -/
theorem unit_ball_sqrt_volume_comparison (g : SmoothMetric M)
    (hcomplete : IsComplete g) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (o z : M.Carrier) :
    Real.sqrt (μ (distBall g.form o 1)).toReal ≤
      (inducedDistance g.form o z + 1) ^ n * Real.sqrt (μ (distBall g.form z 1)).toReal := by
  let r := inducedDistance g.form o z
  have hr : 0 ≤ r := g.induced_distance_nonneg o z
  have hsub : distBall g.form o 1 ⊆ distBall g.form z (r + 1) := by
    intro w hw
    have hd := (L12Aux.mem_distBall_iff g o w zero_lt_one).mp hw
    apply (L12Aux.mem_distBall_iff g z w (by positivity)).mpr
    have htri := g.induced_distance_triangle z o w
    rw [g.induced_distance_symm z o] at htri
    change inducedDistance g.form z w < r + 1
    linarith
  have hBG := L12Aux.bishopGromov n M g hcomplete hK hRic μ hμ z 1 (r + 1)
    zero_lt_one (by linarith)
  have hv := (measure_mono hsub).trans hBG
  have hvreal := ENNReal.toReal_mono
    (show ENNReal.ofReal (((r + 1) / 1) ^ (2 * n)) * μ (distBall g.form z 1) ≠ ⊤ by
      apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      exact (riemannianVolume_distBall_lt_top g μ hμ z zero_lt_one).ne) hv
  simp only [div_one, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ (r + 1) ^ (2 * n))] at hvreal
  have hp : (r + 1) ^ (2 * n) = ((r + 1) ^ n) ^ 2 := by
    rw [← pow_mul]
    congr 1
    omega
  rw [hp] at hvreal
  have h₁ := Real.sq_sqrt (ENNReal.toReal_nonneg (a := μ (distBall g.form o 1)))
  have h₂ := Real.sq_sqrt (ENNReal.toReal_nonneg (a := μ (distBall g.form z 1)))
  have hnon : 0 ≤ (r + 1) ^ n * Real.sqrt (μ (distBall g.form z 1)).toReal := by positivity
  change Real.sqrt (μ (distBall g.form o 1)).toReal ≤ (r + 1) ^ n * _
  nlinarith [Real.sqrt_nonneg (μ (distBall g.form o 1)).toReal]

/-- Harnack on a unit ball controls a point by the genuine L² norm on any
measurable set containing that ball. -/
theorem nonnegativeHeatRepresentative_point_L2
    (hLY : LeafCandidates.LiYauDifferential) (g : SmoothMetric M)
    (hcomplete : IsComplete g) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {u : M.Carrier → ℝ → ℝ} (hu : SmoothSpaceTime u (Set.Ioi 0))
    (hn : ∀ x t, 0 < t → 0 ≤ u x t)
    (heq : ∀ x t, 0 < t → deriv (u x) t = laplacian g.form (fun y => u y t) x)
    (o z : M.Carrier) (t : ℝ) (ht : 0 < t) (v : Lp ℝ 2 μ)
    (hv : v =ᵐ[μ] (fun w => u w (t + 1)))
    (s : Set M.Carrier) (hs : MeasurableSet s) (hsub : distBall g.form z 1 ⊆ s) :
    u z t * Real.sqrt (μ (distBall g.form o 1)).toReal ≤
      ((t + 1) / t) ^ n * Real.exp (1 / 2) *
        (inducedDistance g.form o z + 1) ^ n * ‖scalarL2Indicator μ s hs v‖ := by
  let H := ((t + 1) / t) ^ n * Real.exp (1 / 2)
  have hH : 0 < H := by dsimp only [H]; positivity
  have hnorm : ‖u z t • scalarBallL2 g μ hμ z 1 zero_lt_one‖ ≤
      H * ‖scalarL2Indicator μ s hs v‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [Lp.coeFn_smul (u z t) (scalarBallL2 g μ hμ z 1 zero_lt_one),
      scalarBallL2_coe g μ hμ z 1 zero_lt_one, scalarL2Indicator_coe μ s hs v, hv]
      with w hsm hb hi hvw
    simp only [Pi.smul_apply, smul_eq_mul] at hsm
    rw [hsm, hb, hi]
    by_cases hw : w ∈ distBall g.form z 1
    · rw [Set.indicator_of_mem hw, Set.indicator_of_mem (hsub hw), mul_one, hvw]
      simp only [Real.norm_eq_abs, abs_of_nonneg (hn z t ht),
        abs_of_nonneg (hn w (t + 1) (by linarith))]
      have hh := nonnegativeHeatSolution_harnack hLY g hcomplete hK hRic hu hn heq ht
        (by linarith : t < t + 1) z w
      have hd := (L12Aux.mem_distBall_iff g z w zero_lt_one).mp hw
      have hd0 := g.induced_distance_nonneg z w
      have hexp : Real.exp (inducedDistance g.form z w ^ 2 / (2 * (t + 1 - t))) ≤
          Real.exp (1 / 2) := by
        apply Real.exp_le_exp.mpr
        have he : t + 1 - t = 1 := by ring
        rw [he]
        nlinarith
      exact hh.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hexp (by positivity)) (hn w (t + 1) (by linarith)))
    · rw [Set.indicator_of_notMem hw, mul_zero, norm_zero]
      positivity
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hn z t ht), scalarBallL2_norm] at hnorm
  have hvol := unit_ball_sqrt_volume_comparison g hcomplete hK hRic μ hμ o z
  have hm := mul_le_mul_of_nonneg_left hvol (hn z t ht)
  have hd0 := g.induced_distance_nonneg o z
  have hm' := mul_le_mul_of_nonneg_left hnorm
    (show 0 ≤ (inducedDistance g.form o z + 1) ^ n by positivity)
  dsimp only [H] at hnorm hm'
  nlinarith

/-- A direct quantitative absorption of the volume polynomial. -/
theorem polynomial_mul_gaussian_le (n : ℕ) (β : ℝ) (hβ : 0 < β)
    (r : ℝ) (hr : 0 ≤ r) :
    (r + 1) ^ n * Real.exp (-β * r ^ 2) ≤
      Real.exp ((n : ℝ) ^ 2 / (2 * β)) * Real.exp (-(β / 2) * r ^ 2) := by
  have hp : (r + 1) ^ n ≤ Real.exp ((n : ℝ) * r) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith) (Real.add_one_le_exp r) n
  apply (mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le).trans
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hcomp : (n : ℝ) * r ≤ (β / 2) * r ^ 2 + (n : ℝ) ^ 2 / (2 * β) := by
    apply (mul_le_mul_iff_left₀ (show 0 < 2 * β by positivity)).mp
    have hs := sq_nonneg (β * r - (n : ℝ))
    have he : ((β / 2) * r ^ 2 + (n : ℝ) ^ 2 / (2 * β)) * (2 * β) =
        β ^ 2 * r ^ 2 + (n : ℝ) ^ 2 := by field_simp <;> ring
    rw [he]
    nlinarith
  linarith

/-- Once the genuine smooth representative has been constructed, actual
L² Gaussian tails imply pointwise Gaussian tails on positive compact slabs.
This is a regularity bridge, not an added hypothesis on the L19 kernel. -/
theorem scalarHeatRepresentative_gaussian_tail
    (hLY : LeafCandidates.LiYauDifferential) (g : SmoothMetric M)
    (hcomplete : IsComplete g) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (f : Lp ℝ 2 μ) {u : M.Carrier → ℝ → ℝ}
    (hu : SmoothSpaceTime u (Set.Ioi 0)) (hn : ∀ x t, 0 < t → 0 ≤ u x t)
    (heq : ∀ x t, 0 < t → deriv (u x) t = laplacian g.form (fun y => u y t) x)
    (hrep : ∀ t, 0 < t → scalarHeatFamily g μ hμ t f =ᵐ[μ] (fun z => u z t))
    (o : M.Carrier) (l b : ℝ) (hl : 0 < l) (hlb : l ≤ b)
    (C β : ℝ) (hC : 0 < C) (hβ : 0 < β)
    (htail : ∀ R τ : ℝ, 0 < R → τ ∈ Set.Icc (l + 1) (b + 1) →
      ‖scalarL2Indicator μ (distBall g.form o R)ᶜ
        (L12Aux.measurableSet_distBall g o R).compl (scalarHeatFamily g μ hμ τ f)‖ ≤
        C * Real.exp (-β * R ^ 2)) :
    ∃ C' β' : ℝ, 0 < C' ∧ 0 < β' ∧ ∀ z t, t ∈ Set.Icc l b →
      u z t ≤ C' * Real.exp (-β' * inducedDistance g.form o z ^ 2) := by
  let V := Real.sqrt (μ (distBall g.form o 1)).toReal
  have hV : 0 < V := Real.sqrt_pos.mpr (ENNReal.toReal_pos
    (riemannianVolume_distBall_pos g μ hμ o zero_lt_one).ne'
    (riemannianVolume_distBall_lt_top g μ hμ o zero_lt_one).ne)
  let K := ((b + 1) / l) ^ n * Real.exp (1 / 2)
  have hb : 0 < b := hl.trans_le hlb
  have hKpos : 0 < K := by dsimp only [K]; positivity
  let D := C + ‖f‖ + 1
  have hD : 0 < D := by dsimp only [D]; positivity
  let Q := K * D * Real.exp β * Real.exp ((n : ℝ) ^ 2 / β)
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  refine ⟨Q / V, β / 4, div_pos hQ hV, by positivity, ?_⟩
  intro z t ht
  have htpos : 0 < t := hl.trans_le ht.1
  let r := inducedDistance g.form o z
  have hr : 0 ≤ r := g.induced_distance_nonneg o z
  let R := max (r - 1) 0
  have hR : 0 ≤ R := le_max_right _ _
  have hsub : distBall g.form z 1 ⊆ (distBall g.form o R)ᶜ := by
    intro w hw hwo
    by_cases hRp : 0 < R
    · have hdist := (L12Aux.mem_distBall_iff g o w hRp).mp hwo
      have hzw := (L12Aux.mem_distBall_iff g z w zero_lt_one).mp hw
      have htri := g.induced_distance_triangle o w z
      rw [g.induced_distance_symm w z] at htri
      have he : R = r - 1 := max_eq_left (by
        by_contra h
        have : R = 0 := max_eq_right (by linarith)
        linarith)
      rw [he] at hdist
      change r ≤ _ at htri
      linarith
    · rw [L12Aux.distBall_eq_empty_of_nonpos g.form o (le_of_not_gt hRp)] at hwo
      exact Set.notMem_empty w hwo
  have htailR : ‖scalarL2Indicator μ (distBall g.form o R)ᶜ
      (L12Aux.measurableSet_distBall g o R).compl (scalarHeatFamily g μ hμ (t + 1) f)‖ ≤
      D * Real.exp (-β * R ^ 2) := by
    by_cases hRp : 0 < R
    · exact (htail R (t + 1) hRp ⟨by linarith [ht.1], by linarith [ht.2]⟩).trans
        (mul_le_mul_of_nonneg_right (by dsimp only [D]; linarith [norm_nonneg f]) (Real.exp_pos _).le)
    · have he : R = 0 := le_antisymm (le_of_not_gt hRp) hR
      rw [he]
      simp only [zero_pow (by norm_num : 2 ≠ 0), mul_zero, neg_zero, Real.exp_zero, mul_one]
      exact ((scalarL2Indicator_norm_le _ _ _ _).trans
        (scalarHeatFamily_norm_le g μ hμ (t + 1) f)).trans (by dsimp only [D]; linarith)
  have hp := nonnegativeHeatRepresentative_point_L2 hLY g hcomplete hK hRic μ hμ
    hu hn heq o z t htpos _ (hrep (t + 1) (by linarith)) _
    (L12Aux.measurableSet_distBall g o R).compl hsub
  have hratio : (t + 1) / t ≤ (b + 1) / l := by
    apply (div_le_div_iff₀ htpos hl).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.1) (show 0 ≤ b + 1 by linarith),
      mul_nonneg hl.le (sub_nonneg.mpr ht.2)]
  have htime : ((t + 1) / t) ^ n * Real.exp (1 / 2) ≤ K :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hratio n) (Real.exp_pos _).le
  have hpoly : 0 ≤ (r + 1) ^ n := by positivity
  have hp' : u z t * V ≤ K * D * ((r + 1) ^ n * Real.exp (-β * R ^ 2)) := by
    calc
      _ ≤ (((t + 1) / t) ^ n * Real.exp (1 / 2)) * (r + 1) ^ n *
        ‖scalarL2Indicator μ (distBall g.form o R)ᶜ
          (L12Aux.measurableSet_distBall g o R).compl (scalarHeatFamily g μ hμ (t + 1) f)‖ := hp
      _ ≤ K * (r + 1) ^ n * (D * Real.exp (-β * R ^ 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_right htime hpoly) htailR (norm_nonneg _)
          (mul_nonneg hKpos.le hpoly)
      _ = _ := by ring
  have hshift : Real.exp (-β * R ^ 2) ≤ Real.exp β * Real.exp (-(β / 2) * r ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hsq : r ^ 2 / 2 - 1 ≤ R ^ 2 := by
      by_cases hrr : 1 ≤ r
      · have he : R = r - 1 := max_eq_left (by linarith)
        rw [he]
        nlinarith [sq_nonneg (r - 2)]
      · have he : R = 0 := max_eq_right (by linarith)
        rw [he]
        nlinarith
    nlinarith [mul_nonneg hβ.le (sub_nonneg.mpr hsq)]
  have habs := polynomial_mul_gaussian_le n (β / 2) (by positivity) r hr
  have hfull : (r + 1) ^ n * Real.exp (-β * R ^ 2) ≤
      Real.exp β * Real.exp ((n : ℝ) ^ 2 / β) * Real.exp (-(β / 4) * r ^ 2) := by
    calc
      _ ≤ (r + 1) ^ n * (Real.exp β * Real.exp (-(β / 2) * r ^ 2)) :=
        mul_le_mul_of_nonneg_left hshift hpoly
      _ = Real.exp β * ((r + 1) ^ n * Real.exp (-(β / 2) * r ^ 2)) := by ring
      _ ≤ Real.exp β * (Real.exp ((n : ℝ) ^ 2 / (2 * (β / 2))) *
          Real.exp (-((β / 2) / 2) * r ^ 2)) := mul_le_mul_of_nonneg_left habs (Real.exp_pos _).le
      _ = _ := by
        have he₁ : 2 * (β / 2) = β := by ring
        have he₂ : (β / 2) / 2 = β / 4 := by ring
        rw [he₁, he₂]
        ring
  have hfinal : u z t * V ≤ Q * Real.exp (-(β / 4) * r ^ 2) := by
    exact hp'.trans (by
      convert mul_le_mul_of_nonneg_left hfull (mul_nonneg hKpos.le hD.le) using 1 <;> dsimp only [Q] <;> ring)
  apply (mul_le_mul_iff_left₀ hV).mp
  calc
    _ ≤ Q * Real.exp (-(β / 4) * r ^ 2) := hfinal
    _ = _ := by dsimp only [r]; field_simp <;> ring

/-- The actual Markov positivity and full support of the original volume
force every continuous heat representative of a nonnegative input to be nonnegative. -/
theorem scalarHeatRepresentative_nonneg (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (f : Lp ℝ 2 μ) (hf : ∀ᵐ z ∂μ, 0 ≤ f z) {u : M.Carrier → ℝ → ℝ}
    (hu : SmoothSpaceTime u (Set.Ioi 0))
    (hrep : ∀ t, 0 < t → scalarHeatFamily g μ hμ t f =ᵐ[μ] (fun z => u z t)) :
    ∀ z t, 0 < t → 0 ≤ u z t := by
  letI : μ.IsOpenPosMeasure := riemannianVolume_isOpenPosMeasure g μ hμ
  intro z t ht
  have ha : ∀ᵐ w ∂μ, 0 ≤ u w t := by
    filter_upwards [scalarHeatFamily_nonneg g μ hμ ht.le f hf, hrep t ht] with w hw he
    rwa [he] at hw
  have hdense := Measure.dense_of_ae ha
  have hclosed : IsClosed {w | 0 ≤ u w t} :=
    isClosed_le continuous_const (continuous_of_smoothFn (smoothSpaceTime_slice hu ht))
  have hz : z ∈ closure {w | 0 ≤ u w t} := by rw [hdense.closure_eq]; trivial
  rwa [hclosed.closure_eq] at hz

/-- Gaussian initial data have pointwise Gaussian tails after the genuine
smooth representative is supplied by the independent regularity construction.
All positivity and L² tail estimates here are proved from the actual heat family. -/
theorem scalarGaussianHeatRepresentative_gaussian_tail
    (g : SmoothMetric M) (hcomplete : IsComplete g) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (o : M.Carrier) (a : ℝ) (ha : 0 < a) {u : M.Carrier → ℝ → ℝ}
    (hu : SmoothSpaceTime u (Set.Ioi 0))
    (heq : ∀ x t, 0 < t → deriv (u x) t = laplacian g.form (fun y => u y t) x)
    (hrep : ∀ t, 0 < t → scalarHeatFamily g μ hμ t
      (scalarGaussianL2 g hK hRic μ hμ o a ha) =ᵐ[μ] (fun z => u z t))
    (l b : ℝ) (hl : 0 < l) (hlb : l ≤ b) :
    ∃ C β : ℝ, 0 < C ∧ 0 < β ∧ ∀ z t, t ∈ Set.Icc l b →
      u z t ≤ C * Real.exp (-β * inducedDistance g.form o z ^ 2) := by
  have hf : ∀ᵐ z ∂μ, 0 ≤ scalarGaussianL2 g hK hRic μ hμ o a ha z := by
    filter_upwards [scalarGaussianL2_coe g hK hRic μ hμ o a ha] with z hz
    rw [hz]
    exact (Real.exp_pos _).le
  have hn := scalarHeatRepresentative_nonneg g μ hμ _ hf hu hrep
  obtain ⟨A, _, htail⟩ := exists_uniform_gaussian_heat_L2_tail n
  obtain ⟨C, β, hC, hβ, hbound⟩ := htail M g hK hRic μ hμ o a (b + 1) ha (by linarith)
  exact scalarHeatRepresentative_gaussian_tail liYauDifferential g hcomplete hK hRic μ hμ
    _ hu hn heq hrep o l b hl hlb C β hC hβ (fun R τ hR hτ =>
      hbound R τ hR (by linarith [hτ.1]) hτ.2)

/-- The same pointwise tail holds for nonnegative actual L² data supported
in a fixed ball, including the compact smooth tests used in duality. -/
theorem scalarCompactHeatRepresentative_gaussian_tail
    (g : SmoothMetric M) (hcomplete : IsComplete g) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (o : M.Carrier) (r : ℝ) (hr : 0 < r) (f : Lp ℝ 2 μ)
    (hf : ∀ᵐ z ∂μ, 0 ≤ f z)
    (hfs : ∀ᵐ z ∂μ, z ∉ distBall g.form o r → f z = 0)
    {u : M.Carrier → ℝ → ℝ} (hu : SmoothSpaceTime u (Set.Ioi 0))
    (heq : ∀ x t, 0 < t → deriv (u x) t = laplacian g.form (fun y => u y t) x)
    (hrep : ∀ t, 0 < t → scalarHeatFamily g μ hμ t f =ᵐ[μ] (fun z => u z t))
    (l b : ℝ) (hl : 0 < l) (hlb : l ≤ b) :
    ∃ C β : ℝ, 0 < C ∧ 0 < β ∧ ∀ z t, t ∈ Set.Icc l b →
      u z t ≤ C * Real.exp (-β * inducedDistance g.form o z ^ 2) := by
  have hn := scalarHeatRepresentative_nonneg g μ hμ f hf hu hrep
  obtain ⟨C, β, hC, hβ, hbound⟩ := scalarHeatFamily_compact_support_gaussian_L2_tail
    g μ hμ o r (b + 1) hr (by linarith) f hfs
  exact scalarHeatRepresentative_gaussian_tail liYauDifferential g hcomplete hK hRic μ hμ
    f hu hn heq hrep o l b hl hlb C β hC hβ (fun R τ hR hτ =>
      hbound R τ hR (by linarith [hτ.1]) hτ.2)

end Yau.LeafProofs.L19Aux
