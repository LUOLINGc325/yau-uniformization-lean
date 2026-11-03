import Yau.Proofs.U02LocalChartInjective
import Yau.Proofs.U02AnalyticSeries
import Yau.Proofs.V03HolomorphicSmooth

/-! Germ identities extend only along the actual holomorphic transition
domain on its indicated shrinking coordinate ball. -/

open scoped Manifold Topology ContDiff
open Filter Metric

noncomputable section
namespace Yau.NodeProofs.U02Proof
open Yau Blueprint

theorem holomorphic_analyticOnNhd {n m : ℕ} {O : Set (ComplexVector n)}
    (hO : IsOpen O) {f : ComplexVector n → ComplexVector m}
    (hf : DifferentiableOn ℂ f O) : AnalyticOnNhd ℂ f O :=
  U02AnalyticAux.analyticOnNhd_of_complex_contDiffOn_infty hO
    (V03Proof.complex_holomorphic_contDiffOn hO hf)

theorem shrinking_transition_self {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {h : Flow X} {rho : STF X} {r0 r1 sigma C Cb t0 : ℝ}
    {Phi : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {f : ℝ → Pt X → ComplexVector n}
    (hc : ShrinkingCharts X o h rho r0 r1 sigma C Cb t0 Phi F f)
    {t : ℝ} (ht : t0 ≤ t) : Set.EqOn (F t t) id (ball 0 r1) := by
  rcases hc with ⟨hr1, hr10, _hs, _hC, hcharts, htrans, _hcomp, _hz, _hinv, _hdec, _hj, _hreg⟩
  obtain ⟨hW, hW0, hinj⟩ := unitaryChart_local_injective (hcharts t ht)
    (mem_ball_self (hr1.trans hr10))
  obtain ⟨hF, _hB, hF0, hPhi, _hD, _hdet, _hI⟩ := htrans t t ht le_rfl
  have hcont : Tendsto (F t t) (𝓝 0) (𝓝 0) := by
    simpa only [ContinuousAt, hF0] using
      ((hF 0 (mem_ball_self hr1)).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr1))).continuousAt
  have hgem : F t t =ᶠ[𝓝 0] id := by
    filter_upwards [hW0, hcont.eventually hW0, hPhi] with z hz hFz heq
    exact hinj hFz hz heq
  exact (holomorphic_analyticOnNhd isOpen_ball hF).eqOn_of_preconnected_of_eventuallyEq
    analyticOnNhd_id (convex_ball (0 : ComplexVector n) r1).isPreconnected
    (mem_ball_self hr1) hgem

theorem shrinking_transition_cocycle_closedBall {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {h : Flow X} {rho : STF X} {r0 r1 sigma C Cb t0 : ℝ}
    {Phi : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {f : ℝ → Pt X → ComplexVector n}
    (hc : ShrinkingCharts X o h rho r0 r1 sigma C Cb t0 Phi F f)
    {a b c r : ℝ} (ha : t0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hr : 0 ≤ r) (hrr : r < r1)
    (himage : ∀ z ∈ closedBall (0 : ComplexVector n) r, F a b z ∈ ball 0 r1) :
    ∀ z ∈ closedBall (0 : ComplexVector n) r, F b c (F a b z) = F a c z := by
  rcases hc with ⟨_hr1, _hr10, _hs, _hC, _hcharts, htrans, hcomp, _hz, _hinv, _hdec, _hj, _hreg⟩
  have hsub : closedBall (0 : ComplexVector n) r ⊆ ball 0 r1 := closedBall_subset_ball hrr
  have hAB := holomorphic_analyticOnNhd isOpen_ball (htrans a b ha hab).1
  have hBC := holomorphic_analyticOnNhd isOpen_ball (htrans b c (ha.trans hab) hbc).1
  have hAC := holomorphic_analyticOnNhd isOpen_ball (htrans a c ha (hab.trans hbc)).1
  have hleft : AnalyticOnNhd ℂ (fun z => F b c (F a b z)) (closedBall 0 r) := by
    intro z hz
    exact (hBC _ (himage z hz)).comp (hAB z (hsub hz))
  exact hleft.eqOn_of_preconnected_of_eventuallyEq (hAC.mono hsub)
    (convex_closedBall (0 : ComplexVector n) r).isPreconnected (mem_closedBall_self hr)
    (hcomp a b c ha hab hbc)

theorem shrinking_inverse_transition_germ {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {h : Flow X} {rho : STF X} {r0 r1 sigma C Cb t0 : ℝ}
    {Phi : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {f : ℝ → Pt X → ComplexVector n}
    (hc : ShrinkingCharts X o h rho r0 r1 sigma C Cb t0 Phi F f)
    {t t' : ℝ} (ht : t0 ≤ t) (htt : t ≤ t')
    {V : Set (Pt X)} (hV : IsOpen V) (ho : o ∈ V)
    (hdf : MDifferentiableOn (ComplexModel n) 𝓘(ℂ, ComplexVector n) (f t') V)
    (hinv : ∀ x ∈ V, Phi t' (f t' x) = x) :
    (fun z => f t' (Phi t z)) =ᶠ[𝓝 0] F t t' := by
  rcases hc with ⟨hr1, hr10, _hs, _hC, hcharts, htrans, _hcomp, hzero, _hinv, _hdec, _hj, _hreg⟩
  have hr0 := hr1.trans hr10
  have hc0 := hcharts t ht
  have hc1 := hcharts t' (ht.trans htt)
  have hPhi : Tendsto (Phi t) (𝓝 0) (𝓝 o) := by
    simpa only [ContinuousAt, hc0.2.1] using
      ((hc0.1.1 0 (mem_ball_self hr0)).contMDiffAt
        (isOpen_ball.mem_nhds (mem_ball_self hr0))).continuousAt
  have hraw : Tendsto (f t') (𝓝 o) (𝓝 0) := by
    simpa only [ContinuousAt, hzero t' (ht.trans htt)] using
      ((hdf o ho).mdifferentiableAt (hV.mem_nhds ho)).continuousAt
  obtain ⟨hF, _hB, hF0, hgem, _hD, _hdet, _hI⟩ := htrans t t' ht htt
  have hFcont : Tendsto (F t t') (𝓝 0) (𝓝 0) := by
    simpa only [ContinuousAt, hF0] using
      ((hF 0 (mem_ball_self hr1)).differentiableAt
        (isOpen_ball.mem_nhds (mem_ball_self hr1))).continuousAt
  obtain ⟨W, hW, hInj⟩ := unitaryChart_local_injective hc1 (mem_ball_self hr0)
  have hleft : ∀ᶠ y in 𝓝 o, Phi t' (f t' y) = y := by
    filter_upwards [hV.mem_nhds ho] with y hy
    exact hinv y hy
  filter_upwards [(hraw.comp hPhi).eventually hW, hFcont.eventually hW,
    hPhi.eventually hleft, hgem] with z hrawz hFz hleftz hgemz
  exact hInj hrawz hFz (hleftz.trans hgemz.symm)

theorem shrinking_inverse_transition_closedBall {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {h : Flow X} {rho : STF X} {r0 r1 sigma C Cb t0 : ℝ}
    {Phi : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {f : ℝ → Pt X → ComplexVector n}
    (hc : ShrinkingCharts X o h rho r0 r1 sigma C Cb t0 Phi F f)
    {t t' r : ℝ} (ht : t0 ≤ t) (htt : t ≤ t') (hr : 0 ≤ r) (hrr : r < r1)
    {V : Set (Pt X)} (hV : IsOpen V) (ho : o ∈ V)
    (hdf : MDifferentiableOn (ComplexModel n) 𝓘(ℂ, ComplexVector n) (f t') V)
    (hinv : ∀ x ∈ V, Phi t' (f t' x) = x)
    (himage : ∀ z ∈ closedBall (0 : ComplexVector n) r, Phi t z ∈ V) :
    ∀ z ∈ closedBall (0 : ComplexVector n) r, f t' (Phi t z) = F t t' z := by
  have hgem := shrinking_inverse_transition_germ hc ht htt hV ho hdf hinv
  have hPhi := (hc.2.2.2.2.1 t ht).1.1
  let O := ball (0 : ComplexVector n) r0 ∩ (Phi t) ⁻¹' V
  have hO : IsOpen O := hPhi.continuousOn.isOpen_inter_preimage isOpen_ball hV
  have hPhiO : MDifferentiableOn 𝓘(ℂ, ComplexVector n) (ComplexModel n) (Phi t) O :=
    (hPhi.mdifferentiableOn (by simp)).mono Set.inter_subset_left
  have hraw : DifferentiableOn ℂ (fun z => f t' (Phi t z)) O :=
    (hdf.comp hPhiO (fun z hz => hz.2)).differentiableOn
  have hsub : closedBall (0 : ComplexVector n) r ⊆ O := by
    intro z hz
    exact ⟨closedBall_subset_ball (hrr.trans hc.2.1) hz, himage z hz⟩
  have hF := holomorphic_analyticOnNhd isOpen_ball
    (hc.2.2.2.2.2.1 t t' ht htt).1
  exact ((holomorphic_analyticOnNhd hO hraw).mono hsub).eqOn_of_preconnected_of_eventuallyEq
    (hF.mono (closedBall_subset_ball hrr))
    (convex_closedBall (0 : ComplexVector n) r).isPreconnected
    (mem_closedBall_self hr) hgem

end Yau.NodeProofs.U02Proof
