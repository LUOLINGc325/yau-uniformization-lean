import spec.CHAIN.CONTRACTS

/-! Finite compositions propagate genuine local flow regularity along compact
time segments. The proof uses the same given flow and its actual group law. -/

noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff
namespace Yau.Blueprint.C02Proof

variable {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace N] [ChartedSpace H N]
  {I : ModelWithCorners ℝ E H} [IsManifold I ∞ N]

def LocalFlowRegularity (m : ℕ) (φ : N → ℝ → N) : Prop :=
  ∀ p, ∃ U : Set N, IsOpen U ∧ p ∈ U ∧ ∃ ε > (0 : ℝ),
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I m
      (fun q : N × ℝ => φ q.1 q.2) (U ×ˢ Ioo (-ε) ε)

theorem uniform_local_flow_regularity {m : ℕ} {φ : N → ℝ → N}
    (hlocal : LocalFlowRegularity (I := I) m φ) {K : Set N} (hK : IsCompact K) :
    ∃ ε > (0 : ℝ), ∀ p ∈ K, ∀ t ∈ Ioo (-ε) ε,
      ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I m (fun q : N × ℝ => φ q.1 q.2) (p, t) := by
  classical
  choose U hU hpU ε hε hreg using hlocal
  let O := ⋃ p, U p ×ˢ Ioo (-ε p) (ε p)
  have hO : IsOpen O := isOpen_iUnion (fun p => (hU p).prod isOpen_Ioo)
  have hKO : K ×ˢ ({0} : Set ℝ) ⊆ O := by
    intro q hq
    have hq0 : q.2 = 0 := hq.2
    exact mem_iUnion.mpr ⟨q.1, hpU q.1, by rw [hq0]; constructor <;> linarith [hε q.1]⟩
  obtain ⟨u, v, hu, hv, hKu, h0v, huv⟩ :=
    generalized_tube_lemma hK isCompact_singleton hO hKO
  have hzero : (0 : ℝ) ∈ v := h0v (by simp)
  obtain ⟨δ, hδ, hδv⟩ := Metric.mem_nhds_iff.mp (hv.mem_nhds hzero)
  refine ⟨δ, hδ, ?_⟩
  intro p hp t ht
  have htv : t ∈ v := hδv (by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using abs_lt.mpr ht)
  have hptO : (p, t) ∈ O := huv (show (p, t) ∈ u ×ˢ v from ⟨hKu hp, htv⟩)
  obtain ⟨a, ha⟩ := mem_iUnion.mp hptO
  exact (hreg a).contMDiffAt (((hU a).prod isOpen_Ioo).mem_nhds ha)

theorem flow_initial_contMDiffAt {m : ℕ} {φ : N → ℝ → N}
    (hzero : ∀ p, φ p 0 = p)
    (hadd : ∀ p s t, φ p (s + t) = φ (φ p s) t)
    (hcurve : ∀ p, Continuous (φ p))
    (hlocal : LocalFlowRegularity (I := I) m φ) (p : N) (t : ℝ) :
    ContMDiffAt I I m (fun q => φ q t) p := by
  let K := φ p '' Icc (-|t|) |t|
  have hK : IsCompact K := isCompact_Icc.image (hcurve p)
  obtain ⟨ε, hε, hreg⟩ := uniform_local_flow_regularity hlocal hK
  obtain ⟨k, hk⟩ := exists_nat_gt (|t| / ε)
  let d := t / (k + 1 : ℝ)
  have hden : (0 : ℝ) < k + 1 := by positivity
  have hd : |d| < ε := by
    dsimp only [d]
    rw [abs_div, abs_of_pos hden]
    apply (div_lt_iff₀ hden).mpr
    have h := (div_lt_iff₀ hε).mp hk
    nlinarith
  have hstep : ∀ j : ℕ, j ≤ k + 1 → |(j : ℝ) * d| ≤ |t| := by
    intro j hj
    have hj' : (j : ℝ) ≤ k + 1 := by exact_mod_cast hj
    dsimp only [d]
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg j), abs_div, abs_of_pos hden]
    have hmul := mul_le_mul_of_nonneg_right hj' (abs_nonneg t)
    rw [← mul_div_assoc]
    exact (div_le_iff₀ hden).mpr (by nlinarith)
  have hiter : ∀ j : ℕ, j ≤ k + 1 →
      ContMDiffAt I I m (fun q => φ q ((j : ℝ) * d)) p := by
    intro j
    induction j with
    | zero =>
        intro hj
        have heq : (fun q : N => φ q ((0 : ℕ) * d)) = id := by
          funext q
          simp only [Nat.cast_zero, zero_mul, hzero, id_eq]
        rw [heq]
        exact contMDiffAt_id
    | succ j ih =>
        intro hj
        have hj' : j ≤ k + 1 := Nat.le_trans (Nat.le_succ j) hj
        have hpj : φ p ((j : ℝ) * d) ∈ K :=
          ⟨(j : ℝ) * d, abs_le.mp (hstep j hj'), rfl⟩
        have hsmall := hreg _ hpj d (abs_lt.mp hd)
        have hc := hsmall.comp p ((ih hj').prodMk contMDiffAt_const)
        convert hc using 1
        funext q
        simp only [Function.comp_apply, hadd, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
  have htime : ((k + 1 : ℕ) : ℝ) * d = t := by
    push_cast
    dsimp only [d]
    field_simp
  simpa only [htime] using hiter (k + 1) le_rfl

theorem flow_joint_contMDiff {m : ℕ} {φ : N → ℝ → N}
    (hzero : ∀ p, φ p 0 = p)
    (hadd : ∀ p s t, φ p (s + t) = φ (φ p s) t)
    (hcurve : ∀ p, Continuous (φ p))
    (hlocal : LocalFlowRegularity (I := I) m φ) :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) I m (fun q : N × ℝ => φ q.1 q.2) := by
  intro q
  obtain ⟨U, hU, hpU, ε, hε, hreg⟩ := hlocal (φ q.1 q.2)
  have hz : (0 : ℝ) ∈ Ioo (-ε) ε := by constructor <;> linarith
  have hbase : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I m
      (fun a : N × ℝ => φ a.1 a.2) (φ q.1 q.2, 0) :=
    hreg.contMDiffAt ((hU.prod isOpen_Ioo).mem_nhds ⟨hpU, hz⟩)
  have hfirst : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I m
      (fun a : N × ℝ => φ a.1 q.2) q :=
    (flow_initial_contMDiffAt hzero hadd hcurve hlocal q.1 q.2).comp q contMDiffAt_fst
  have hsecond : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) m
      (fun a : N × ℝ => a.2 - q.2) q :=
    (contMDiffAt_snd (I := I) (J := 𝓘(ℝ, ℝ))).sub contMDiffAt_const
  have hbase' : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I m
      (fun a : N × ℝ => φ a.1 a.2) (φ q.1 q.2, q.2 - q.2) := by
    simpa only [sub_self] using hbase
  have hc := hbase'.comp q (hfirst.prodMk hsecond)
  convert hc using 1
  funext a
  simp only [Function.comp_apply, ← hadd, add_sub_cancel]

end Yau.Blueprint.C02Proof
