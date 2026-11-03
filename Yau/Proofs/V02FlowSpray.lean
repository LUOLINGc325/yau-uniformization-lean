import Yau.Proofs.V02FlowFirstJet
import Yau.Proofs.V02FlowFiniteCover

/-! Compact native complex sprays from actual holomorphic fields, with actual coordinate jets. -/

open scoped Manifold Topology ContDiff Matrix
open Filter Metric Set

noncomputable section
namespace Yau.Blueprint.V02FlowProof
open Yau Yau.Blueprint V03Proof

variable {n b : ℕ} {M : ComplexManifold n}

def nativeSprayCoordinate
    (Ψ : NativeCotangentPoint M × (Fin b → ℂ) → NativeCotangentPoint M)
    (x : M.Carrier) (p : CotangentCoord n × (Fin b → ℂ)) : CotangentCoord n :=
  cotangentChart x (Ψ (NativeCotangentPoint.mk (cotangentChartInv x p.1), p.2)).val

set_option maxHeartbeats 1000000 in
theorem exists_native_compact_complex_spray [T2Space (NativeCotangentPoint M)]
    (Z : Fin b → CotangentPoint M → CotangentIndex n → ℂ)
    (hZ : ∀ k x i, DifferentiableOn ℂ
      (fun z => (cotangentTransition (chartInv x z.1) x (cotangentChartInv x z) *ᵥ
        Z k (cotangentChartInv x z)) i) (cotangentTarget x))
    {K : Set (CotangentPoint M)} (hK : CotangentCompact K) :
    ∃ (N : ℕ) (x : Fin N → M.Carrier) (a : Fin N → CotangentCoord n) (δ R : ℝ)
      (U : Set (NativeCotangentPoint M)) (Kplus : Set (CotangentPoint M))
      (Ψ : NativeCotangentPoint M × (Fin b → ℂ) → NativeCotangentPoint M),
      0 < δ ∧ 0 < R ∧ IsOpen U ∧ (NativeCotangentPoint.mk '' K) ⊆ U ∧
      CotangentCompact Kplus ∧
      (∀ j, closedBall (a j) (8 * δ) ⊆ cotangentTarget (x j)) ∧
      (K ⊆ ⋃ j, cotangentChartInv (x j) '' ball (a j) δ) ∧
      U = ⋃ j, nativeCotangentChartBall (x j) (a j) (2 * δ) ∧
      (∀ y, Ψ (y, 0) = y) ∧
      ContMDiffOn ((𝓘(ℂ, CotangentCoord n)).prod 𝓘(ℂ, Fin b → ℂ))
        𝓘(ℂ, CotangentCoord n) ∞ Ψ (U ×ˢ ball 0 R) ∧
      (∀ y, y.val ∈ K → ∀ τ ∈ closedBall (0 : Fin b → ℂ) (R / 2),
        (Ψ (y, τ)).val ∈ Kplus) ∧
      (∀ y ∈ U, ∀ k : Fin b,
        fderiv ℂ (fun τ : Fin b → ℂ => cotangentChart y.val.1 (Ψ (y, τ)).val)
          0 (Pi.single k 1) = cotangentVectorOfCoords (Z k y.val)) ∧
      (∀ j, ContDiffOn ℂ ∞ (nativeSprayCoordinate Ψ (x j))
        (ball (a j) (2 * δ) ×ˢ ball (0 : Fin b → ℂ) R)) ∧
      (∃ C4 : ℝ, 0 ≤ C4 ∧ ∀ j m, m ≤ 4 →
        ∀ p ∈ closedBall (a j) δ ×ˢ closedBall (0 : Fin b → ℂ) (R / 2),
          ‖iteratedFDeriv ℝ m (nativeSprayCoordinate Ψ (x j)) p‖ ≤ C4) := by
  classical
  obtain ⟨N, x, a, δ, hδ, hball, hcover⟩ := exists_cotangent_buffered_finite_cover hK
  obtain ⟨R₀, A, φ, Φ, hR₀, hA, hRA, hφ, hΦ⟩ :=
    exists_native_finite_chart_flows Z hZ x a hδ hball
  let R := R₀ / (2 * ((b : ℝ) + 1))
  have hden : 0 < 2 * ((b : ℝ) + 1) := by positivity
  have hR : 0 < R := div_pos hR₀ hden
  have hR_eq : 2 * ((b : ℝ) + 1) * R = R₀ := by
    dsimp [R]
    field_simp
  have hRlt : R < R₀ := by
    have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
    nlinarith [mul_nonneg hb hR.le]
  have hbudget : (b : ℝ) * R * A ≤ δ / 8 := by
    have heq := congrArg (fun v : ℝ => v * A) hR_eq
    have hn : 0 ≤ R * A := mul_nonneg hR.le hA
    nlinarith
  let Vj : Fin N → Set (NativeCotangentPoint M) :=
    fun j => nativeCotangentChartBall (x j) (a j) (2 * δ)
  let U : Set (NativeCotangentPoint M) := ⋃ j, Vj j
  let Kplus : Set (CotangentPoint M) :=
    ⋃ j, cotangentChartInv (x j) '' closedBall (a j) (3 * δ)
  let Ψ := finiteFlowCompose b Φ
  let ψ : Fin N → CotangentCoord n × (Fin b → ℂ) → CotangentCoord n :=
    fun j => finiteFlowCompose b (fun k => φ (j, k))
  have hball4 : ∀ j, ball (a j) (4 * δ) ⊆ cotangentTarget (x j) := fun j =>
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))).trans (hball j)
  have hball2 : ∀ j, ball (a j) (2 * δ) ⊆ cotangentTarget (x j) := fun j =>
    (ball_subset_ball (by linarith)).trans (hball4 j)
  have hV : ∀ j, IsOpen (Vj j) := fun j => nativeCotangentChartBall_isOpen (hball2 j)
  have hU : IsOpen U := isOpen_iUnion hV
  have hzero : ∀ k y, Φ k (0, y) = y := fun k => (hΦ k).1
  have htimes : ∀ τ : Fin b → ℂ, ‖τ‖ ≤ R → ∀ k, ‖τ k‖ ≤ R ∧ τ k ∈ ball (0 : ℂ) R₀ := by
    intro τ hτ k
    have hk : ‖τ k‖ ≤ R := (norm_le_pi_norm τ k).trans hτ
    exact ⟨hk, by simpa only [mem_ball, dist_zero_right] using hk.trans_lt hRlt⟩
  have hstep : ∀ j k t u, ‖t‖ ≤ R → u ∈ ball (a j) (4 * δ) →
      dist (φ (j, k) (t, u)) u ≤ R * A := by
    intro j k t u ht hu
    rw [dist_eq_norm]
    exact ((hφ (j, k)).2.2.1 (t, u)
      ⟨by simpa only [mem_closedBall, dist_zero_right] using ht.trans hRlt.le,
        ball_subset_closedBall hu⟩).trans (mul_le_mul_of_nonneg_right ht hA)
  have hstart : ∀ j u, u ∈ ball (a j) (2 * δ) →
      dist u (a j) + (b : ℝ) * R * A < 4 * δ := by
    intro j u hu
    have hd := mem_ball.mp hu
    linarith
  have hdispl : ∀ j u, u ∈ ball (a j) (2 * δ) → ∀ τ : Fin b → ℂ, ‖τ‖ ≤ R →
      dist (ψ j (u, τ)) u ≤ (b : ℝ) * R * A := by
    intro j u hu τ hτ
    exact finiteFlowCompose_displacement (a := a j) (d := 4 * δ) (ρ := R) (A := A)
      (u := u) (τ := τ) b (fun k => φ (j, k)) hR.le hA
      (fun k => (htimes τ hτ k).1) (hstep j) (hstart j u hu)
  have hψimage : ∀ j u, u ∈ ball (a j) (2 * δ) → ∀ τ : Fin b → ℂ, ‖τ‖ ≤ R →
      ψ j (u, τ) ∈ ball (a j) (4 * δ) := by
    intro j u hu τ hτ
    apply mem_ball.mpr
    exact ((dist_triangle (ψ j (u, τ)) u (a j)).trans
      (add_le_add (hdispl j u hu τ hτ) (le_refl (dist u (a j))))).trans_lt (by
        have hd := mem_ball.mp hu
        linarith)
  have hψsmooth : ∀ j, ContDiffOn ℂ ∞ (ψ j)
      (ball (a j) (2 * δ) ×ˢ ball (0 : Fin b → ℂ) R) := by
    intro j p hp
    exact (finiteFlowCompose_contDiffAt (a := a j) (d := 4 * δ) (T := R₀) (ρ := R) (A := A)
      (u := p.1) (τ := p.2) b (fun k => φ (j, k)) hR.le hA
      (fun k => (htimes p.2 (by simpa using (mem_ball.mp hp.2).le) k).1)
      (fun k => (htimes p.2 (by simpa using (mem_ball.mp hp.2).le) k).2)
      (fun k => (hφ (j, k)).2.1) (hstep j) (hstart j p.1 hp.1)).contDiffWithinAt
  have hdecode : ∀ j u, u ∈ ball (a j) (2 * δ) → ∀ τ : Fin b → ℂ, ‖τ‖ ≤ R →
      Ψ (NativeCotangentPoint.mk (cotangentChartInv (x j) u), τ) =
        NativeCotangentPoint.mk (cotangentChartInv (x j) (ψ j (u, τ))) := by
    intro j u hu τ hτ
    exact finiteFlowCompose_native_decode (d := 4 * δ) (T := R₀) (ρ := R) (A := A)
      (u := u) (τ := τ) b (x j) (a j) (fun k => φ (j, k)) Φ
      (hball4 j) hR.le hA (fun k => (hΦ k).2.2 j) (hstep j)
      (fun k => (htimes τ hτ k).1) (fun k => (htimes τ hτ k).2) (hstart j u hu)
  have hpatchEq : ∀ j p, p ∈ Vj j ×ˢ ball (0 : Fin b → ℂ) R →
      Ψ p = NativeCotangentPoint.mk (cotangentChartInv (x j)
        (ψ j (cotangentChart (x j) p.1.val, p.2))) := by
    intro j p hp
    have hy := (nativeCotangentChartBall_mem_iff (hball2 j)).mp hp.1
    have hinv : NativeCotangentPoint.mk (cotangentChartInv (x j)
        (cotangentChart (x j) p.1.val)) = p.1 :=
      NativeCotangentPoint.ext (cotangentChart_left_inv (x j) hy.1)
    simpa only [hinv] using hdecode j _ hy.2 p.2 (by simpa using (mem_ball.mp hp.2).le)
  have hΨpatch : ∀ j, ContMDiffOn ((𝓘(ℂ, CotangentCoord n)).prod 𝓘(ℂ, Fin b → ℂ))
      𝓘(ℂ, CotangentCoord n) ∞ Ψ (Vj j ×ˢ ball (0 : Fin b → ℂ) R) := by
    intro j
    exact (native_decode_parameter_map_contMDiffOn (x j) (hball2 j) (hψsmooth j)
      (fun p hp => hball4 j (hψimage j p.1 hp.1 p.2
        (by simpa using (mem_ball.mp hp.2).le)))).congr (hpatchEq j)
  have hΨsmooth : ContMDiffOn ((𝓘(ℂ, CotangentCoord n)).prod 𝓘(ℂ, Fin b → ℂ))
      𝓘(ℂ, CotangentCoord n) ∞ Ψ (U ×ˢ ball (0 : Fin b → ℂ) R) := by
    intro p hp
    obtain ⟨j, hy⟩ := mem_iUnion.mp hp.1
    exact ((hΨpatch j p ⟨hy, hp.2⟩).contMDiffAt
      (((hV j).prod isOpen_ball).mem_nhds ⟨hy, hp.2⟩)).contMDiffWithinAt
  have hactualEq : ∀ j p, p ∈ ball (a j) (2 * δ) ×ˢ ball (0 : Fin b → ℂ) R →
      nativeSprayCoordinate Ψ (x j) p = ψ j p := by
    intro j p hp
    unfold nativeSprayCoordinate
    rw [hdecode j p.1 hp.1 p.2 (by simpa using (mem_ball.mp hp.2).le)]
    exact cotangentChart_right_inv (x j) (hball4 j
      (hψimage j p.1 hp.1 p.2 (by simpa using (mem_ball.mp hp.2).le)))
  have hactualSmooth : ∀ j, ContDiffOn ℂ ∞ (nativeSprayCoordinate Ψ (x j))
      (ball (a j) (2 * δ) ×ˢ ball (0 : Fin b → ℂ) R) :=
    fun j => (hψsmooth j).congr (hactualEq j)
  have hKplus : CotangentCompact Kplus := by
    refine ⟨N, x, fun j => closedBall (a j) (3 * δ), fun j => ⟨isCompact_closedBall _ _, ?_⟩, rfl⟩
    exact (closedBall_subset_closedBall (by linarith)).trans (hball j)
  have hKU : (NativeCotangentPoint.mk '' K) ⊆ U := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨j, z, hz, rfl⟩ := mem_iUnion.mp (hcover hy)
    exact mem_iUnion.mpr ⟨j, z, (ball_subset_ball (by linarith)) hz, rfl⟩
  have hKimage : ∀ y : NativeCotangentPoint M, y.val ∈ K →
      ∀ τ ∈ closedBall (0 : Fin b → ℂ) (R / 2), (Ψ (y, τ)).val ∈ Kplus := by
    intro y hy τ hτ
    obtain ⟨j, z, hz, hzy⟩ := mem_iUnion.mp (hcover hy)
    have hyEq : NativeCotangentPoint.mk (cotangentChartInv (x j) z) = y :=
      NativeCotangentPoint.ext hzy
    have hz2 : z ∈ ball (a j) (2 * δ) := (ball_subset_ball (by linarith)) hz
    have htR : ‖τ‖ ≤ R := (by simpa using mem_closedBall.mp hτ : ‖τ‖ ≤ R / 2).trans (by linarith)
    have hout : ψ j (z, τ) ∈ closedBall (a j) (3 * δ) := by
      apply mem_closedBall.mpr
      have hd := hdispl j z hz2 τ htR
      have htri := dist_triangle (ψ j (z, τ)) z (a j)
      have hza := mem_ball.mp hz
      linarith
    rw [← hyEq, hdecode j z hz2 τ htR]
    exact mem_iUnion.mpr ⟨j, ψ j (z, τ), hout, rfl⟩
  have hfirst : ∀ y ∈ U, ∀ k, HasDerivAt
      (fun z : ℂ => cotangentChart y.val.1 (Φ k (z, y)).val)
      (cotangentVectorOfCoords (Z k y.val)) 0 := by
    intro y hy k
    obtain ⟨j, hyj⟩ := mem_iUnion.mp hy
    have hycoord := (nativeCotangentChartBall_mem_iff (hball2 j)).mp hyj
    have hy4 : y ∈ nativeCotangentChartBall (x j) (a j) (4 * δ) :=
      (nativeCotangentChartBall_mem_iff (hball4 j)).mpr
        ⟨hycoord.1, (ball_subset_ball (by linarith)) hycoord.2⟩
    have hc := nativeChartFlow_integralCurve (x j) isOpen_ball y
      (fun t ht => hball j (ball_subset_closedBall
        ((hφ (j, k)).2.2.2 t ht _ ((ball_subset_ball (by linarith)) hycoord.2)).1))
      (fun t ht => ((hφ (j, k)).2.2.2 t ht _
        ((ball_subset_ball (by linarith)) hycoord.2)).2)
    have hzbranch := nativeChartFlow_zero (x j) (hφ (j, k)).1 hycoord.1
    have hd := hc.2 0 (mem_ball_self hR₀) y.val.1 (by
      change (nativeChartFlow (x j) (φ (j, k)) (0, y)).val ∈ cotangentSource y.val.1
      rw [hzbranch]
      exact mem_extChartAt_source _)
    dsimp only at hd
    rw [hzbranch, cotangentChartField_centered] at hd
    apply hd.congr_of_eventuallyEq
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hR₀)] with z hz
    exact congrArg (fun p : NativeCotangentPoint M => cotangentChart y.val.1 p.val)
      ((hΦ k).2.2 j z hz y hy4)
  have hjets : ∀ j, ∃ C : ℝ, 0 ≤ C ∧ ∀ m ≤ 4,
      ∀ p ∈ closedBall (a j) δ ×ˢ closedBall (0 : Fin b → ℂ) (R / 2),
        ‖iteratedFDeriv ℝ m (nativeSprayCoordinate Ψ (x j)) p‖ ≤ C := by
    intro j
    apply compact_iteratedFDeriv_finite_bound (f := nativeSprayCoordinate Ψ (x j))
      (O := ball (a j) (2 * δ) ×ˢ ball (0 : Fin b → ℂ) R)
      (K := closedBall (a j) δ ×ˢ closedBall (0 : Fin b → ℂ) (R / 2))
      (isOpen_ball.prod isOpen_ball)
      ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
      (fun p hp => ⟨mem_ball.mpr ((mem_closedBall.mp hp.1).trans_lt (by linarith)),
        mem_ball.mpr ((mem_closedBall.mp hp.2).trans_lt (by linarith))⟩)
      ((hactualSmooth j).restrict_scalars ℝ) 4
  choose C hC hjbound using hjets
  refine ⟨N, x, a, δ, R, U, Kplus, Ψ, hδ, hR, hU, hKU, hKplus, hball, hcover, rfl,
    finiteFlowCompose_zero b Φ hzero, hΨsmooth, hKimage,
    fun y hy k => finiteFlowCompose_first_time_jet Φ hzero Z hU hR hΨsmooth hfirst y hy k,
    hactualSmooth, ∑ j, C j, Finset.sum_nonneg (fun j _ => hC j), ?_⟩
  intro j m hm p hp
  exact (hjbound j m hm p hp).trans
    (Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ j))

end Yau.Blueprint.V02FlowProof
