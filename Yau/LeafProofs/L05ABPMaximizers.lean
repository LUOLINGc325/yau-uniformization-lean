import Yau.LeafProofs.L05ABPConvexSupport

noncomputable section

open Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

def supSpatialSlope {n : ℕ} (epsilon : ℝ) (y q : Point n) : Space n :=
  epsilon⁻¹ • (q.1-y.1)

theorem supRegularize_eq_displacement {n : ℕ} {v : Point n → ℝ} {B epsilon : ℝ}
    (hv : Continuous v) (hB : 0 ≤ B) (hb : ∀ r, |v r| ≤ B) (hepsilon : 0 < epsilon)
    {y q : Point n} (hq : supRegularize epsilon v y=v q-qnorm2 (y-q)/(2*epsilon)) :
    qnorm2 (y-q) ≤ 4*B*epsilon := by
  have hy := (supRegularize_bounds hv hB hb hepsilon y).2
  have hvq := (abs_le.mp (hb q)).2
  have hlo := (abs_le.mp hy).1
  rw [hq] at hlo
  have hquot : qnorm2 (y-q)/(2*epsilon) ≤ 2*B := by linarith
  have he := (div_le_iff₀ (by positivity : 0<2*epsilon)).mp hquot
  nlinarith

/-- If all maximizers at the center have the same spatial slope, every
maximizer nearby has a nearby spatial slope. Compact projections avoid any
choice of a continuous maximizer. -/
theorem supRegularize_maximizer_slopes_near {n : ℕ} {v : Point n → ℝ} {B epsilon : ℝ}
    (hv : Continuous v) (hB : 0 ≤ B) (hb : ∀ r, |v r| ≤ B) (hepsilon : 0 < epsilon)
    {y0 : Point n} {p : Space n}
    (hcenter : ∀ q, supRegularize epsilon v y0=v q-qnorm2 (y0-q)/(2*epsilon) →
      supSpatialSlope epsilon y0 q=p) {eta : ℝ} (heta : 0<eta) :
    ∀ᶠ y in 𝓝 y0, ∀ q,
      supRegularize epsilon v y=v q-qnorm2 (y-q)/(2*epsilon) →
        ‖supSpatialSlope epsilon y q-p‖<eta := by
  let R := 4*B*epsilon+2
  let D := Metric.closedBall y0 1
  let K := Metric.closedBall y0 R
  let Bad : Set (Point n × Point n) := (D ×ˢ K) ∩
    {r | supRegularize epsilon v r.1=v r.2-qnorm2 (r.1-r.2)/(2*epsilon)} ∩
    {r | eta ≤ ‖supSpatialSlope epsilon r.1 r.2-p‖}
  have hU : Continuous (supRegularize epsilon v) := supRegularize_continuous hv hB hb hepsilon
  have hEq : IsClosed {r : Point n × Point n |
      supRegularize epsilon v r.1=v r.2-qnorm2 (r.1-r.2)/(2*epsilon)} := by
    apply isClosed_eq (hU.comp continuous_fst)
    exact (hv.comp continuous_snd).sub
      ((qnorm2_continuous.comp (continuous_fst.sub continuous_snd)).div_const _)
  have hSlope : Continuous (fun r : Point n × Point n => ‖supSpatialSlope epsilon r.1 r.2-p‖) := by
    unfold supSpatialSlope
    fun_prop
  have hBad : IsCompact Bad :=
    (((isCompact_closedBall y0 1).prod (isCompact_closedBall y0 R)).inter_right hEq).inter_right
      (isClosed_le continuous_const hSlope)
  have hy0 : y0 ∉ Prod.fst '' Bad := by
    rintro ⟨r,hr,hr0⟩
    rcases r with ⟨y,q⟩
    change y=y0 at hr0
    subst y
    have hq := hcenter q hr.1.2
    have ht := hr.2
    change eta ≤ ‖supSpatialSlope epsilon y0 q-p‖ at ht
    rw [hq,sub_self,norm_zero] at ht
    exact (not_le.mpr heta) ht
  have hgood : (Prod.fst '' Bad)ᶜ ∈ 𝓝 y0 :=
    (hBad.image continuous_fst).isClosed.isOpen_compl.mem_nhds hy0
  filter_upwards [hgood,Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num : (0:ℝ)<1))]
    with y hy hyD
  intro q hq
  by_contra hfail
  have hdist : qnorm2 (y-q) ≤ 4*B*epsilon := supRegularize_eq_displacement hv hB hb hepsilon hq
  have hn : ‖y-q‖≤4*B*epsilon+1 := by
    have hh := norm_sq_le_qnorm2 (y-q)
    nlinarith [sq_nonneg (‖y-q‖-1)]
  have hy1 : ‖y-y0‖≤1 := by
    simpa only [dist_eq_norm] using (Metric.mem_ball.mp hyD).le
  have hqK : q ∈ K := by
    change dist q y0≤R
    rw [dist_eq_norm]
    have ht := norm_sub_le_norm_sub_add_norm_sub q y y0
    rw [norm_sub_rev q y] at ht
    dsimp [R]
    linarith
  apply hy
  refine ⟨(y,q),?_,rfl⟩
  exact ⟨⟨⟨Metric.ball_subset_closedBall hyD,hqK⟩,hq⟩,le_of_not_gt hfail⟩

theorem spatialInf_contact_slope_unique {n : ℕ} {u : Point n → ℝ} {B epsilon delta R : ℝ}
    (hu : Continuous u) (hB : 0 ≤ B) (hb : ∀ r, |u r| ≤ B)
    (hdelta : 0 < delta) (hde : delta < epsilon) {y p r : Space n} {t : ℝ}
    (hp : ∀ h : Space n, u (y,t)+inner ℝ p h-‖h‖^2/(2*epsilon) ≤ u (y+h,t))
    (hr : ∀ h : Space n, u (y,t)+inner ℝ r h-‖h‖^2/(2*epsilon) ≤ u (y+h,t))
    (hz : y+delta • p ∈ Metric.ball (0 : Space n) R)
    (hcontact : ∀ x ∈ Metric.closedBall (0 : Space n) R,
      spatialInfRegularize delta u (x,t) ≤ spatialInfRegularize delta u (y+delta • p,t)+
        inner ℝ p (x-(y+delta • p))) : r=p := by
  have hpath : Tendsto (fun s : ℝ => y+delta • ((1-s) • p+s • r))
      (𝓝[>] 0) (𝓝 (y+delta • p)) := by
    have hc : Continuous (fun s : ℝ => y+delta • ((1-s) • p+s • r)) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hnear := hpath (Metric.isOpen_ball.mem_nhds hz)
  have hlt : ∀ᶠ s in 𝓝[>] (0:ℝ), s<1 :=
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ s in 𝓝[>] (0:ℝ), 0<s := self_mem_nhdsWithin
  obtain ⟨s,hs0,hs1,hxs⟩ := (hpos.and (hlt.and hnear)).exists
  have hs : 0<s := hs0
  have hpr := spatial_lower_support_convexCombination hp hr (sub_nonneg.mpr hs1.le) hs.le
    (by ring : (1-s)+s=1)
  have hval := spatialInf_eq_of_lower_support hu hB hb hdelta hde y ((1-s) • p+s • r) t hpr
  have hval0 := spatialInf_eq_of_lower_support hu hB hb hdelta hde y p t hp
  have hc := hcontact (y+delta • ((1-s) • p+s • r)) (Metric.ball_subset_closedBall hxs)
  rw [hval,hval0] at hc
  have hmix : (1-s) • p+s • r = p+s • (r-p) := by module
  have hdiff : y+delta • ((1-s) • p+s • r)-(y+delta • p)=(delta*s) • (r-p) := by module
  rw [hdiff,hmix,norm_add_sq_real,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,
    inner_smul_right,inner_smul_right] at hc
  have hnon : 0 ≤ ‖r-p‖^2 := sq_nonneg _
  have hzsq : ‖r-p‖^2=0 := by
    have hpos : 0<delta*s^2 := mul_pos hdelta (sq_pos_of_pos hs)
    nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hzsq))

end Yau.LeafProofs.L05Aux
