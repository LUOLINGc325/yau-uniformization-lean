import Yau.LeafProofs.L23FieldMetricExponentialFirstJet
import Yau.LeafProofs.L23FieldMetricGeodesicScale

/-! The actual exponential endpoint agrees with rescaled genuine geodesics on a radial line. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux L23LocalDistanceContract
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1000000

theorem fieldExp_radial_eq_of_geodesic
    (h : HermitianField M) (hh : MetricSmooth h) (x : M.Carrier)
    (V : TangentSpace 𝓘(ℝ, ComplexVector n) x) (γ : ℝ → M.Carrier)
    (ε : ℝ) (hε : 0 < ε) (hγ : FieldGeodesicOn h γ (Set.Ioo (-ε) ε))
    (hγ0 : γ 0 = x)
    (hphase : ∀ c : M.Carrier, x ∈ (chartAt (ComplexVector n) c).source →
      geoChartState γ c 0 = (chartPt c x,realTangentCoords c x V)) :
    (fun r => fieldExp h x (r • V)) =ᶠ[𝓝 (0 : ℝ)] γ := by
  have Hnear : Set.Ioo (-ε/2) (ε/2) ∈ 𝓝 (0 : ℝ) := isOpen_Ioo.mem_nhds (by constructor <;> linarith)
  filter_upwards [Hnear] with r hr
  have habsr : |r| < ε/2 := abs_lt.mpr ⟨by linarith [hr.1],hr.2⟩
  let β := fun u : ℝ => γ (r*u)
  have hsub : Set.Ioo (-(1/2 : ℝ)) (1+1/2) ⊆ {u : ℝ | r*u ∈ Set.Ioo (-ε) ε} := by
    intro u hu
    have habsu : |u| < 2 := abs_lt.mpr ⟨by linarith [hu.1],by linarith [hu.2]⟩
    have Hprod : |r*u| < ε := by
      rw [abs_mul]
      nlinarith [abs_nonneg r,abs_nonneg u]
    exact abs_lt.mp Hprod
  have Hgeo := fieldGeodesicOn_mul h γ _ hγ r
  have Hβ : FieldGeodesicOn h β (Set.Ioo (-(1/2 : ℝ)) (1+1/2)) :=
    ⟨Hgeo.1.mono hsub,fun c u hu hc => Hgeo.2 c u (hsub hu) hc⟩
  apply fieldExp_eq_of_endpoint h hh x (r • V) (γ r)
  refine ⟨1/2,β,by norm_num,Hβ,?_,?_,?_⟩
  · simpa only [β,mul_zero] using hγ0
  · simp only [β,mul_one]
  · intro c hc
    have H := geoChartState_mul γ c r 0
    rw [mul_zero,hphase c hc] at H
    simpa only [β,map_smul] using H

theorem exists_radial_fieldExp_geodesic
    (h : HermitianField M) (hh : MetricSmooth h) (x : M.Carrier)
    (V : TangentSpace 𝓘(ℝ, ComplexVector n) x) :
    ∃ δ : ℝ, 0 < δ ∧
      FieldGeodesicOn h (fun r => fieldExp h x (r • V)) (Set.Ioo (-δ) δ) ∧
      ∀ c : M.Carrier, x ∈ (chartAt (ComplexVector n) c).source →
        geoChartState (fun r => fieldExp h x (r • V)) c 0 =
          (chartPt c x,realTangentCoords c x V) := by
  obtain ⟨B,ρ,ε,X,e,H⟩ := exists_fieldNormalEndpointData h hh x Set.univ isOpen_univ (Set.mem_univ _)
  rcases H with ⟨hB,hxB,hBsub,hρ,hε,hsource,heq,hX,hinv,hdata,hzero⟩
  have Hfull : FieldNormalEndpointData h x Set.univ B ρ ε X e :=
    ⟨hB,hxB,hBsub,hρ,hε,hsource,heq,hX,hinv,hdata,hzero⟩
  let W := realTangentCoords x x V
  let κ := ρ / (2*(‖W‖+1))
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  have hW : κ • W ∈ Metric.ball (0 : ComplexVector n) ρ := by
    rw [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hκ]
    dsimp only [κ]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : 0 < 2*(‖W‖+1))).mpr
    nlinarith [norm_nonneg W]
  have hp : (chartPt x x,realTangentCoords x x (κ • V)) ∈ e.source := by
    rw [hsource,map_smul]
    exact ⟨hxB,hW⟩
  have HW := fieldExpEndpoint_normal_coordinates h hh x x Set.univ B ρ ε X e Hfull (mem_chart_source _ _) (κ • V) hp
  rcases HW with ⟨e₀,β,he₀,hβ,hβ0,hβ1,hβphase⟩
  have hsub : Set.Ioo (-e₀) e₀ ⊆ Set.Ioo (-e₀) (1+e₀) := by intro u hu; exact ⟨hu.1,by linarith [hu.2]⟩
  have Hβ : FieldGeodesicOn h β (Set.Ioo (-e₀) e₀) :=
    ⟨hβ.1.mono hsub,fun c u hu hc => hβ.2 c u (hsub hu) hc⟩
  have Hrad := fieldExp_radial_eq_of_geodesic h hh x (κ • V) β e₀ he₀ Hβ hβ0 hβphase
  let γ := fun r : ℝ => β (κ⁻¹*r)
  have Hγ := fieldGeodesicOn_mul h β _ hβ κ⁻¹
  have Heq : (fun r => fieldExp h x (r • V)) =ᶠ[𝓝 (0 : ℝ)] γ := by
    have Hcont : Tendsto (fun r : ℝ => κ⁻¹*r) (𝓝 0) (𝓝 0) := by
      have HC : ContinuousAt (fun r : ℝ => κ⁻¹*r) 0 := (continuous_const.mul continuous_id).continuousAt
      change Tendsto (fun r : ℝ => κ⁻¹*r) (𝓝 0) (𝓝 (κ⁻¹*0)) at HC
      simpa only [mul_zero] using HC
    have Hcomp := Hcont.eventually Hrad
    filter_upwards [Hcomp] with r hr
    convert! hr using 1
    rw [smul_smul]
    congr 1
    field_simp
  obtain ⟨d,hd,hdsub⟩ := Metric.mem_nhds_iff.mp Heq
  let δ := min d (κ*e₀/2)
  have hδ : 0 < δ := lt_min hd (by positivity)
  have htime : Set.Ioo (-δ) δ ⊆ {r : ℝ | κ⁻¹*r ∈ Set.Ioo (-e₀) (1+e₀)} := by
    intro r hr
    have Hr : -κ*e₀ < r ∧ r < κ*e₀ := by constructor <;> linarith [hr.1,hr.2,min_le_right d (κ*e₀/2)]
    change -e₀ < κ⁻¹*r ∧ κ⁻¹*r < 1+e₀
    rw [← div_eq_inv_mul]
    constructor
    · exact (lt_div_iff₀ hκ).mpr (by nlinarith [Hr.1])
    · exact (div_lt_iff₀ hκ).mpr (by nlinarith [Hr.2])
  have Hnear : ∀ r ∈ Set.Ioo (-δ) δ, (fun s => fieldExp h x (s • V)) =ᶠ[𝓝 r] γ := by
    intro r hr
    have Hrd : r ∈ Metric.ball (0 : ℝ) d := by
      rw [Real.ball_eq_Ioo]
      constructor <;> linarith [hr.1,hr.2,min_le_left d (κ*e₀/2)]
    exact eventually_of_mem (Metric.isOpen_ball.mem_nhds Hrd) (fun s hs => hdsub hs)
  refine ⟨δ,hδ,?_,?_⟩
  · apply fieldGeodesicOn_of_locally_eq
    intro r hr
    exact ⟨γ,{r : ℝ | κ⁻¹*r ∈ Set.Ioo (-e₀) (1+e₀)},
      isOpen_Ioo.preimage (continuous_const.mul continuous_id),htime hr,Hγ,Hnear r hr⟩
  · intro c hc
    have H := geoChartState_mul β c κ⁻¹ 0
    rw [mul_zero,hβphase c hc] at H
    have Hstate := geoChartState_congr_eventuallyEq (fun r => fieldExp h x (r • V)) γ c 0 (Hnear 0 (by constructor <;> linarith))
    rw [Hstate]
    convert! H using 1
    simp only [map_smul,smul_smul,inv_mul_cancel₀ (ne_of_gt hκ),one_smul]

end Yau.LeafProofs.L23Aux
