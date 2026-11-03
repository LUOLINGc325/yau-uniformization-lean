import Yau.Proofs.P06HodgeRegularitySmoothLift
import Yau.Proofs.P06HodgeRegularitySchwarz

/-! The chart jet lift has a genuinely closed graph: uniform jet limits
are identified by the actual transposed compact-test pairings in L². -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BoundedContinuousFunction InnerProductSpace

namespace Yau.NodeProofs.P06Aux

variable {E H ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (ν : Measure E) [ν.IsAddHaarMeasure] [ν.IsOpenPosMeasure]

theorem regularityLp_integral_pairing (u : Lp ℝ 2 ν) (ψ : E → ℝ) (hψ : MemLp ψ 2 ν) :
    inner ℝ u (hψ.toLp ψ) = ∫ z, u z * ψ z ∂ν := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hψ.coeFn_toLp] with z hz
  simp only [hz,RCLike.inner_apply,conj_trivial,mul_comm]

theorem regularitySmoothLiftJetLinear_continuous
    (P : H →L[ℝ] Lp ℝ 2 ν) (R : H → E → ℝ)
    (hR : ∀ f, ContDiff ℝ ∞ (R f))
    {K : Set E} (hK : IsCompact K) (hRK : ∀ f, tsupport (R f) ⊆ K)
    (hRAE : ∀ f, R f =ᵐ[ν] (P f : E → ℝ)) (v : ι → E) (w : List ι) :
    Continuous (regularitySmoothLiftJetLinear ν P R hR
      (fun f => hK.of_isClosed_subset (isClosed_tsupport _) (hRK f)) hRAE v w) := by
  let hcR := fun f => hK.of_isClosed_subset (isClosed_tsupport (R f)) (hRK f)
  let L := regularitySmoothLiftJetLinear ν P R hR hcR hRAE v w
  have hword f := regularityCoefficientWord_regular v (hR f) (hcR f) w
  have hwordK f : tsupport (regularityCoefficientWord v w (R f)) ⊆ K :=
    (hword f).2.2.trans (hRK f)
  apply L.continuous_of_seq_closed_graph
  intro us f y hus hy
  have hy0 (z : E) (hz : z ∉ K) : y z = 0 := by
    have heval : Tendsto (fun m => L (us m) z) atTop (𝓝 (y z)) :=
      ((BoundedContinuousFunction.lipschitz_eval_const z).continuous.tendsto y).comp hy
    have hzero (m : ℕ) : L (us m) z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hz (hwordK (us m) h))
    have ht : Tendsto (fun m => L (us m) z) atTop (𝓝 0) := by
      simpa only [hzero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    exact tendsto_nhds_unique heval ht
  have hyK : tsupport (y : E → ℝ) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro z hz
    by_contra hzK
    exact hz (hy0 z hzK)
  have hyc : HasCompactSupport (y : E → ℝ) := hK.of_isClosed_subset (isClosed_tsupport _) hyK
  have hyL : MemLp (y : E → ℝ) 2 (ν.restrict Set.univ) :=
    (y.continuous.memLp_of_hasCompactSupport hyc).restrict Set.univ
  have hfL : MemLp (regularityCoefficientWord v w (R f)) 2 (ν.restrict Set.univ) :=
    ((hword f).1.continuous.memLp_of_hasCompactSupport (hword f).2.1).restrict Set.univ
  have hAE : (y : E → ℝ) =ᵐ[ν] regularityCoefficientWord v w (R f) := by
    have hh := regularity_ae_eq_of_test_integrals ν isOpen_univ hyL hfL (fun φ hφ => by
      simp only [Measure.restrict_univ]
      have hφI : Integrable φ ν := hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1
      have htest := regularityCoefficientWord_regular v hφ.1 hφ.2.1 w.reverse
      have htestL : MemLp (regularityCoefficientWord v w.reverse φ) 2 ν :=
        htest.1.continuous.memLp_of_hasCompactSupport htest.2.1
      have hsource0 : Tendsto (fun m => inner ℝ (P (us m)) (htestL.toLp _)) atTop
          (𝓝 (inner ℝ (P f) (htestL.toLp _))) :=
        ((P.continuous.tendsto f).comp hus).inner
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => htestL.toLp _) atTop (𝓝 (htestL.toLp _)))
      have hsource : Tendsto (fun m => (-1 : ℝ)^w.length *
          ∫ z, (P (us m)) z * regularityCoefficientWord v w.reverse φ z ∂ν) atTop
          (𝓝 ((-1 : ℝ)^w.length * ∫ z, (P f) z * regularityCoefficientWord v w.reverse φ z ∂ν)) := by
        simpa only [regularityLp_integral_pairing] using tendsto_const_nhds.mul hsource0
      have htarget := ((regularityBCFPairing ν φ hφI).continuous.tendsto y).comp hy
      have hpair (b : H) : (∫ z, L b z * φ z ∂ν) = (-1 : ℝ)^w.length *
          ∫ z, (P b) z * regularityCoefficientWord v w.reverse φ z ∂ν := by
        change (∫ z, regularityCoefficientWord v w (R b) z * φ z ∂ν) = _
        rw [regularityCoefficientWord_integral_transpose ν v (R b) (hR b) w hφ.1 hφ.2.1]
        congr 1
        exact integral_congr_ae ((hRAE b).mono fun z hz => by dsimp only; rw [hz])
      have hsource' : Tendsto (fun m => ∫ z, L (us m) z * φ z ∂ν) atTop
          (𝓝 ((-1 : ℝ)^w.length * ∫ z, (P f) z * regularityCoefficientWord v w.reverse φ z ∂ν)) :=
        hsource.congr' (Eventually.of_forall fun m => (hpair (us m)).symm)
      have hh : (∫ z, y z * φ z ∂ν) = (-1 : ℝ)^w.length *
          ∫ z, (P f) z * regularityCoefficientWord v w.reverse φ z ∂ν :=
        tendsto_nhds_unique htarget hsource'
      exact hh.trans (hpair f).symm)
    simpa only [Measure.restrict_univ] using hh
  apply BoundedContinuousFunction.ext
  intro z
  exact congrFun (Measure.eq_of_ae_eq hAE y.continuous (hword f).1.continuous) z

def regularitySmoothLiftJetCLM
    (P : H →L[ℝ] Lp ℝ 2 ν) (R : H → E → ℝ)
    (hR : ∀ f, ContDiff ℝ ∞ (R f))
    {K : Set E} (hK : IsCompact K) (hRK : ∀ f, tsupport (R f) ⊆ K)
    (hRAE : ∀ f, R f =ᵐ[ν] (P f : E → ℝ)) (v : ι → E) (w : List ι) : H →L[ℝ] (E →ᵇ ℝ) where
  toLinearMap := regularitySmoothLiftJetLinear ν P R hR
    (fun f => hK.of_isClosed_subset (isClosed_tsupport _) (hRK f)) hRAE v w
  cont := regularitySmoothLiftJetLinear_continuous ν P R hR hK hRK hRAE v w

end Yau.NodeProofs.P06Aux
