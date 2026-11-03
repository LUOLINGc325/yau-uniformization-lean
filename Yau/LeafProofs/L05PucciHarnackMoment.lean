import Yau.LeafProofs.L05PucciHarnackScaledDensity

open Filter MeasureTheory Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

def harnackMomentTerm (H0 K p : ℝ) (k : ℕ) (v : ℝ) : ℝ :=
  if H0*K^k < v then (H0*K^(k+1))^p else 0

theorem harnack_momentTerm_nonneg {H0 K : ℝ} (hH0 : 0 ≤ H0) (hK : 0 ≤ K)
    (p : ℝ) (k : ℕ) (v : ℝ) : 0 ≤ harnackMomentTerm H0 K p k v := by
  unfold harnackMomentTerm
  split_ifs
  · exact Real.rpow_nonneg (mul_nonneg hH0 (pow_nonneg hK _)) _
  · exact le_rfl

theorem harnack_moment_majorant {H0 K p : ℝ} (hH0 : 0 < H0) (hK : 1 < K) (hp : 0 < p)
    (N : ℕ) {v : ℝ} (hv0 : 0 ≤ v) (hv : v ≤ H0*K^N) :
    v^p ≤ H0^p+∑ k∈Finset.range N, harnackMomentTerm H0 K p k v := by
  have hKpos : 0 < K := lt_trans (by norm_num) hK
  induction N generalizing v with
  | zero =>
    simpa only [pow_zero,mul_one,Finset.sum_range_zero,add_zero] using
      Real.rpow_le_rpow hv0 (by simpa only [pow_zero,mul_one] using hv) hp.le
  | succ N ih =>
    rw [Finset.sum_range_succ]
    by_cases hLow : v ≤ H0*K^N
    · have hIh := ih hv0 hLow
      have hT := harnack_momentTerm_nonneg hH0.le hKpos.le p N v
      linarith
    · have hTerm : harnackMomentTerm H0 K p N v=(H0*K^(N+1))^p := by
        rw [harnackMomentTerm,ite_eq_left (lt_of_not_ge hLow)]
      have hBound := Real.rpow_le_rpow hv0 hv hp.le
      have hSum : 0 ≤ ∑ k∈Finset.range N, harnackMomentTerm H0 K p k v :=
        Finset.sum_nonneg (fun k _ => harnack_momentTerm_nonneg hH0.le hKpos.le p k v)
      have hHpow := (Real.rpow_pos_of_pos hH0 p).le
      rw [hTerm]
      linarith

theorem harnack_geometric_sum_bound {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    ∑ k∈Finset.range N, r^k ≤ 1/(1-r) := by
  apply (le_div_iff₀ (sub_pos.mpr hr1)).mpr
  rw [geom_sum_mul_neg]
  linarith [pow_nonneg hr0 N]

theorem harnack_moment_coefficient {H0 K : ℝ} (hH0 : 0 ≤ H0) (hK : 0 ≤ K)
    (p A q : ℝ) (k : ℕ) :
    (H0*K^(k+1))^p*(A*q^k)=H0^p*K^p*A*(q*K^p)^k := by
  rw [Real.mul_rpow hH0 (pow_nonneg hK _),← Real.rpow_pow_comm hK p (k+1),pow_succ,mul_pow]
  ring

def harnackMomentExponent (q K : ℝ) : ℝ := min (1/2) (-Real.log q/(2*Real.log K))

theorem harnack_momentExponent_bounds {q K : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hK : 1 < K) :
    0 < harnackMomentExponent q K ∧ harnackMomentExponent q K < 1 ∧
      q*K^(harnackMomentExponent q K) < 1 := by
  have hLogQ := Real.log_neg hq0 hq1
  have hLogK := Real.log_pos hK
  have hp0 : 0 < harnackMomentExponent q K :=
    lt_min (by norm_num) (div_pos (neg_pos.mpr hLogQ) (mul_pos (by norm_num) hLogK))
  have hp1 : harnackMomentExponent q K < 1 :=
    lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hpBound := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hLogK)).mp
    (min_le_right (1/2 : ℝ) (-Real.log q/(2*Real.log K)))
  change harnackMomentExponent q K*(2*Real.log K) ≤ -Real.log q at hpBound
  have hArg : Real.log q+Real.log K*harnackMomentExponent q K < 0 := by nlinarith
  have hEq : q*K^(harnackMomentExponent q K)=
      Real.exp (Real.log q+Real.log K*harnackMomentExponent q K) := by
    rw [Real.exp_add,Real.exp_log hq0,Real.rpow_def_of_pos (lt_trans (by norm_num) hK)]
  exact ⟨hp0,hp1,by rw [hEq]; exact Real.exp_lt_one_iff.mpr hArg⟩

theorem harnack_geometric_moment_bound {n : ℕ} {u : Point n → ℝ}
    (hu : ContinuousOn u (unitClosed n)) (hu0 : ∀ z∈unitClosed n, 0 ≤ u z)
    {E : Set (Point n)} (hE : MeasurableSet E) (hEQ : E ⊆ unitClosed n)
    {H0 K q A p : ℝ} (hH0 : 0 < H0) (hK : 1 < K) (hq : 0 ≤ q) (hA : 0 ≤ A) (hp : 0 < p)
    (hGeom : q*K^p < 1)
    (hTail : ∀ k : ℕ, harnackMu (E ∩ {z | H0*K^k < u z}) ≤ A*q^k) :
    (∫ z in E, (u z)^p) ≤ H0^p*(harnackMu E+K^p*A/(1-q*K^p)) := by
  have hKpos : 0 < K := lt_trans (by norm_num) hK
  have hCompact : IsCompact (unitClosed n) :=
    (isCompact_closedBall (0 : Space n) 1).prod isCompact_Icc
  have hUCont : ContinuousOn (fun z => (u z)^p) (unitClosed n) :=
    hu.rpow_const (fun _ _ => Or.inr hp.le)
  have hUint : IntegrableOn (fun z => (u z)^p) E :=
    (hUCont.integrableOn_compact hCompact).mono_set hEQ
  have hConstInt : IntegrableOn (fun _ : Point n => H0^p) E :=
    (continuousOn_const.integrableOn_compact hCompact).mono_set hEQ
  obtain ⟨B,hB⟩ := (hCompact.image_of_continuousOn hu).bddAbove
  obtain ⟨N,hN⟩ := pow_unbounded_of_one_lt (B/H0) hK
  have hLevelBound (z : Point n) (hz : z∈E) : u z ≤ H0*K^N := by
    have hUz : u z ≤ B := hB ⟨z,hEQ hz,rfl⟩
    have hBH := (div_lt_iff₀ hH0).mp hN
    nlinarith only [hUz,hBH]
  let T := fun k : ℕ => E ∩ {z | H0*K^k < u z}
  let c := fun k : ℕ => (H0*K^(k+1))^p
  let f := fun k : ℕ => (T k).indicator (fun _ : Point n => c k)
  have hTMeas (k : ℕ) : MeasurableSet (T k) :=
    (harnack_relative_level_measurable hCompact.isClosed hu hE hEQ _).2
  have hCpos (k : ℕ) : 0 ≤ c k := (Real.rpow_pos_of_pos (mul_pos hH0 (pow_pos hKpos _)) p).le
  have hFint (k : ℕ) : IntegrableOn (f k) E :=
    ((continuousOn_const.integrableOn_compact hCompact).mono_set hEQ).indicator (hTMeas k)
  have hFIntegral (k : ℕ) : (∫ z in E, f k z)=c k*harnackMu (T k) := by
    rw [integral_indicator (hTMeas k),Measure.restrict_restrict (hTMeas k),
      inter_eq_left.mpr (show T k ⊆ E from inter_subset_left),setIntegral_const]
    change ((volume : Measure (Point n)) (T k)).toReal*c k=c k*((volume : Measure (Point n)) (T k)).toReal
    ring
  have hPoint (z : Point n) (hz : z∈E) : (u z)^p ≤ H0^p+∑ k∈Finset.range N, f k z := by
    have h := harnack_moment_majorant hH0 hK hp N (hu0 z (hEQ hz)) (hLevelBound z hz)
    have hSum : (∑ k∈Finset.range N, f k z)=∑ k∈Finset.range N, harnackMomentTerm H0 K p k (u z) := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hzHigh : H0*K^k < u z
      · have hzT : z∈T k := ⟨hz,hzHigh⟩
        simp only [f,indicator_of_mem hzT,harnackMomentTerm,ite_eq_left hzHigh,c]
      · have hzT : z∉T k := fun h => hzHigh h.2
        simp only [f,indicator_of_notMem hzT,harnackMomentTerm,ite_eq_right hzHigh]
    rw [hSum]
    exact h
  have hSumInt : IntegrableOn (fun z => ∑ k∈Finset.range N, f k z) E :=
    integrable_finsetSum _ (fun k _ => hFint k)
  have hIle : (∫ z in E, (u z)^p) ≤ H0^p*harnackMu E+
      ∑ k∈Finset.range N, c k*harnackMu (T k) := by
    calc
      _ ≤ ∫ z in E, H0^p+∑ k∈Finset.range N, f k z := by
        apply integral_mono_ae hUint (hConstInt.add hSumInt)
        filter_upwards [ae_restrict_mem hE] with z hz
        exact hPoint z hz
      _ = _ := by
        rw [integral_add hConstInt hSumInt,integral_finsetSum _ (fun k _ => hFint k),setIntegral_const]
        simp_rw [hFIntegral]
        change ((volume : Measure (Point n)) E).toReal*H0^p+
          ∑ k∈Finset.range N, c k*harnackMu (T k)=_
        unfold harnackMu
        ring
  have hR0 : 0 ≤ q*K^p := mul_nonneg hq (Real.rpow_pos_of_pos hKpos p).le
  have hCoefficient : 0 ≤ H0^p*K^p*A :=
    mul_nonneg (mul_nonneg (Real.rpow_pos_of_pos hH0 p).le (Real.rpow_pos_of_pos hKpos p).le) hA
  have hSumBound : (∑ k∈Finset.range N, c k*harnackMu (T k)) ≤
      H0^p*K^p*A/(1-q*K^p) := by
    calc
      _ ≤ ∑ k∈Finset.range N, c k*(A*q^k) := Finset.sum_le_sum
        (fun k _ => mul_le_mul_of_nonneg_left (hTail k) (hCpos k))
      _ = H0^p*K^p*A*∑ k∈Finset.range N, (q*K^p)^k := by
        simp_rw [c,harnack_moment_coefficient hH0.le hKpos.le]
        rw [Finset.mul_sum]
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left (harnack_geometric_sum_bound hR0 hGeom N) hCoefficient
        simpa only [one_div,div_eq_mul_inv,mul_one,one_mul] using h
  calc
    _ ≤ H0^p*harnackMu E+∑ k∈Finset.range N, c k*harnackMu (T k) := hIle
    _ ≤ H0^p*harnackMu E+H0^p*K^p*A/(1-q*K^p) := by linarith only [hSumBound]
    _ = _ := by ring

def harnackMomentNormConstant (H0 K q A p V : ℝ) : ℝ :=
  (H0^p*(V+K^p*A/(1-q*K^p))/V)^(1/p)

theorem harnack_momentNormConstant_pos {H0 K q A p V : ℝ}
    (hH0 : 0 < H0) (hK : 1 < K) (hA : 0 ≤ A) (hV : 0 < V) (hGeom : q*K^p < 1) :
    0 < harnackMomentNormConstant H0 K q A p V := by
  have hKpos : 0 < K := lt_trans (by norm_num) hK
  have hTerm : 0 ≤ K^p*A/(1-q*K^p) := div_nonneg
    (mul_nonneg (Real.rpow_pos_of_pos hKpos p).le hA) (sub_pos.mpr hGeom).le
  exact Real.rpow_pos_of_pos (div_pos
    (mul_pos (Real.rpow_pos_of_pos hH0 p) (by linarith)) hV) _

theorem harnack_geometric_moment_norm {n : ℕ} {u : Point n → ℝ}
    (hu : ContinuousOn u (unitClosed n)) (hu0 : ∀ z∈unitClosed n, 0 ≤ u z)
    {E : Set (Point n)} (hE : MeasurableSet E) (hEQ : E ⊆ unitClosed n)
    (hV : 0 < harnackMu E) {H0 K q A p : ℝ}
    (hH0 : 0 < H0) (hK : 1 < K) (hq : 0 ≤ q) (hA : 0 ≤ A) (hp : 0 < p)
    (hGeom : q*K^p < 1)
    (hTail : ∀ k : ℕ, harnackMu (E ∩ {z | H0*K^k < u z}) ≤ A*q^k) :
    ((∫ z in E, (u z)^p)/harnackMu E)^(1/p) ≤
      harnackMomentNormConstant H0 K q A p (harnackMu E) := by
  have hBound := harnack_geometric_moment_bound hu hu0 hE hEQ hH0 hK hq hA hp hGeom hTail
  have hDiv := div_le_div_of_nonneg_right hBound hV.le
  have hInt : 0 ≤ ∫ z in E, (u z)^p := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem hE] with z hz
    exact Real.rpow_nonneg (hu0 z (hEQ hz)) p
  exact Real.rpow_le_rpow (div_nonneg hInt hV.le) hDiv (one_div_pos.mpr hp).le

theorem harnack_moment_norm_scale {n : ℕ} {u v : Point n → ℝ}
    (hu : ContinuousOn u (unitClosed n)) (hv : ContinuousOn v (unitClosed n))
    (hu0 : ∀ z∈unitClosed n, 0 ≤ u z) (hv0 : ∀ z∈unitClosed n, 0 ≤ v z)
    {E : Set (Point n)} (hE : MeasurableSet E) (hEQ : E ⊆ unitClosed n)
    (hV : 0 < harnackMu E) {h p : ℝ} (hh : 0 < h) (hp : 0 < p)
    (hCompare : ∀ z∈E, v z ≤ h*u z) :
    ((∫ z in E, (v z)^p)/harnackMu E)^(1/p) ≤
      h*((∫ z in E, (u z)^p)/harnackMu E)^(1/p) := by
  have hCompact : IsCompact (unitClosed n) :=
    (isCompact_closedBall (0 : Space n) 1).prod isCompact_Icc
  have hUint : IntegrableOn (fun z => (u z)^p) E :=
    ((hu.rpow_const (fun _ _ => Or.inr hp.le)).integrableOn_compact hCompact).mono_set hEQ
  have hVint : IntegrableOn (fun z => (v z)^p) E :=
    ((hv.rpow_const (fun _ _ => Or.inr hp.le)).integrableOn_compact hCompact).mono_set hEQ
  have hScaled : (∫ z in E, (v z)^p) ≤ h^p*(∫ z in E, (u z)^p) := by
    calc
      _ ≤ ∫ z in E, h^p*(u z)^p := by
        apply integral_mono_ae hVint (hUint.const_mul _)
        filter_upwards [ae_restrict_mem hE] with z hz
        have hRpow := Real.rpow_le_rpow (hv0 z (hEQ hz)) (hCompare z hz) hp.le
        rwa [Real.mul_rpow hh.le (hu0 z (hEQ hz))] at hRpow
      _ = _ := integral_const_mul _ _
  have hUInt0 : 0 ≤ ∫ z in E, (u z)^p := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem hE] with z hz
    exact Real.rpow_nonneg (hu0 z (hEQ hz)) p
  have hVInt0 : 0 ≤ ∫ z in E, (v z)^p := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem hE] with z hz
    exact Real.rpow_nonneg (hv0 z (hEQ hz)) p
  have hMean : (∫ z in E, (v z)^p)/harnackMu E ≤ h^p*((∫ z in E, (u z)^p)/harnackMu E) := by
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hScaled hV.le
  have hUmean0 := div_nonneg hUInt0 hV.le
  have hPower := Real.rpow_le_rpow (div_nonneg hVInt0 hV.le) hMean (one_div_pos.mpr hp).le
  rw [Real.mul_rpow (Real.rpow_pos_of_pos hh p).le hUmean0,← Real.rpow_mul hh.le p (1/p),
    show p*(1/p)=1 from by field_simp [hp.ne'],Real.rpow_one] at hPower
  exact hPower

end Yau.LeafProofs.L05Aux
