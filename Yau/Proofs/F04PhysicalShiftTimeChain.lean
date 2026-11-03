import Yau.Proofs.F04ShiftBochner
import Yau.Proofs.F04SmoothPhysicalShiftTime
import Yau.Proofs.F04SameTraceApproximation
import Yau.Proofs.F04DualPairing

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace ENNReal

noncomputable section

set_option maxHeartbeats 1000000

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.LeafProofs.L03 Yau.HeatConcreteBindings
  Yau.LeafProofs.L16HilbertTimeRegularization Yau.LeafProofs.L16LionsApproximation
  Yau.LeafProofs.L16LionsLimit Yau.LeafProofs.L16LionsTimeTrace

variable {n : ℕ} {M : ComplexManifold n}

/-- The actual supported shifted test satisfies the closed-time chain for
the original continuous trace when b is only C1 on the physical closed slab.
Its derivative is the actual derivWithin on that slab. -/
theorem dirichlet_shift_posPart_physical_time_chain
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : IsOpen O)
    (r : ℝ → M.Carrier → ℝ) (hr : ∀ t, SmoothFn (r t)) (hr0 : ∀ t x, x ∈ O → 0 ≤ r t x)
    (hr2 : ∀ t, ScalarL2 (μ.restrict O) (r t))
    (hdr2 : ∀ t, L2RealForm g.form (μ.restrict O) (scalarExterior (r t)))
    (hRH : Continuous (fun t => scalarToLp (hr2 t)))
    (hRD : Continuous (fun t => realizeL2Form g (μ.restrict O)
      (L2FormSpace.ofSection (scalarExterior (r t)) (hdr2 t))))
    {T : ℝ} (hT : 0 < T) (b : ℝ → Lp ℝ 2 (μ.restrict O))
    (hb : ContDiffOn ℝ 1 b (Icc 0 T)) (hbval : ∀ t ∈ Icc 0 T, b t = scalarToLp (hr2 t))
    {U : ℝ → DirichletEnergy g μ hμ O}
    {R : ℝ → StrongDual ℝ (DirichletEnergy g μ hμ O)}
    (hU : MemLp U 2 (volume.restrict (Ioo 0 T)))
    (hR : MemLp R 2 (volume.restrict (Ioo 0 T)))
    (hw : ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ Ioo 0 T →
      (∫ t in Ioo 0 T, deriv η t • hilbertEmbedding (dirichletL2 g μ hμ O) (U t)) =
        -(∫ t in Ioo 0 T, η t • R t))
    (a : ℝ → Lp ℝ 2 (μ.restrict O)) (ha : ContinuousOn a (Icc 0 T))
    (hae : ∀ᵐ t ∂volume.restrict (Ioo 0 T), dirichletL2 g μ hμ O (U t) = a t) :
    let W := fun t => dirichletShiftPosPart g μ hμ O hO (r t) (hr t) (hr0 t) (hr2 t) (hdr2 t) (U t)
    IntegrableOn (fun t => R t (W t)) (Ioo 0 T) ∧
      IntegrableOn (fun t => inner ℝ (derivWithin b (Icc 0 T) t) (dirichletL2 g μ hμ O (W t))) (Ioo 0 T) ∧
      ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
        ‖Lp.posPart (a t - b t)‖ ^ 2 - ‖Lp.posPart (a s - b s)‖ ^ 2 =
          2 * ∫ q in s..t, R q (W q) - inner ℝ (derivWithin b (Icc 0 T) q) (dirichletL2 g μ hμ O (W q)) := by
  let := dirichletEnergy_completeSpace g μ hμ O
  let J := dirichletL2 g μ hμ O
  let z : ℕ → ℝ → DirichletEnergy g μ hμ O := reflectedSmooth T U
  let Q : ℕ → ℝ → StrongDual ℝ (DirichletEnergy g μ hμ O) := reflectedDualSmooth T R
  let W : ℝ → DirichletEnergy g μ hμ O := fun t =>
    dirichletShiftPosPart g μ hμ O hO (r t) (hr t) (hr0 t) (hr2 t) (hdr2 t) (U t)
  let Wk : ℕ → ℝ → DirichletEnergy g μ hμ O := fun k t =>
    dirichletShiftPosPart g μ hμ O hO (r t) (hr t) (hr0 t) (hr2 t) (hdr2 t) (z k t)
  let d : ℝ → StrongDual ℝ (DirichletEnergy g μ hμ O) := fun t => hilbertPivot J (derivWithin b (Icc 0 T) t)
  let S : ℝ → StrongDual ℝ (DirichletEnergy g μ hμ O) := fun t => R t - d t
  let Sk : ℕ → ℝ → StrongDual ℝ (DirichletEnergy g μ hμ O) := fun k t => Q k t - d t
  have hdval (q : ℝ) (v : DirichletEnergy g μ hμ O) :
      d q v = inner ℝ (derivWithin b (Icc 0 T) q) (J v) := rfl
  have hSval (q : ℝ) (v : DirichletEnergy g μ hμ O) :
      S q v = R q v - inner ℝ (derivWithin b (Icc 0 T) q) (J v) := rfl
  have hSkval (k : ℕ) (q : ℝ) (v : DirichletEnergy g μ hμ O) :
      Sk k q v = Q k q v - inner ℝ (derivWithin b (Icc 0 T) q) (J v) := rfl
  have hJ : ‖J‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun v => by simpa only [one_mul] using dirichletL2_norm_le g μ hμ O v)
  have hDr : MemLp (fun t => realizeL2Form g (μ.restrict O)
      (L2FormSpace.ofSection (scalarExterior (r t)) (hdr2 t))) 2 (volume.restrict (Ioo 0 T)) := by
    rw [restrict_Ioo_eq_restrict_Icc]
    exact continuousOn_memLp_two hRD.continuousOn
  have hbLp : MemLp (derivWithin b (Icc 0 T)) 2 (volume.restrict (Ioo 0 T)) := by
    rw [restrict_Ioo_eq_restrict_Icc]
    exact continuousOn_memLp_two (hb.continuousOn_derivWithin (uniqueDiffOn_Icc hT) le_rfl)
  have hdLp : MemLp d 2 (volume.restrict (Ioo 0 T)) := hbLp.continuousLinearMap_comp (hilbertPivot J)
  have hzLp (k : ℕ) : MemLp (z k) 2 (volume.restrict (Ioo 0 T)) :=
    (reflectedSmooth_memLp hT hU k).restrict (Ioo 0 T)
  have hQLp (k : ℕ) : MemLp (Q k) 2 (volume.restrict (Ioo 0 T)) :=
    (reflectedDualSmooth_memLp hT hR k).restrict (Ioo 0 T)
  have hWLp : MemLp W 2 (volume.restrict (Ioo 0 T)) :=
    dirichletShiftPosPart_family_memLp g hK μ hμ O hO r hr hr0 hr2 hdr2 hRH hRD
      (volume.restrict (Ioo 0 T)) U hU hDr
  have hWkLp (k : ℕ) : MemLp (Wk k) 2 (volume.restrict (Ioo 0 T)) :=
    dirichletShiftPosPart_family_memLp g hK μ hμ O hO r hr hr0 hr2 hdr2 hRH hRD
      (volume.restrict (Ioo 0 T)) (z k) (hzLp k) hDr
  have hPairR := dualPairing_integrable_L2 hWLp hR
  have hPairB : IntegrableOn (fun t => inner ℝ (derivWithin b (Icc 0 T) t) (J (W t))) (Ioo 0 T) := by
    change Integrable (fun t => inner ℝ (derivWithin b (Icc 0 T) t) (J (W t))) (volume.restrict (Ioo 0 T))
    simpa only [hdval] using dualPairing_integrable_L2 hWLp hdLp
  refine ⟨hPairR, hPairB, ?_⟩
  have huni := reflectedSmooth_uniform_to_same_trace J hJ hT hU hR hw a ha hae
  have hWlim := dirichlet_shift_posPart_strongL2_family g hK μ hμ O hO r hr hr0 hr2 hdr2 hRH hRD
    (volume.restrict (Ioo 0 T)) hDr z U hzLp hU (reflectedSmooth_L2_tendsto hT hU)
  have hprodR := strongL2_duality_L1 hWkLp hQLp hWLp hR hWlim
    (reflectedDualSmooth_L2_tendsto hT hR)
  have hdlim : Tendsto (fun _ : ℕ => ∫ t in Ioo 0 T, ‖d t - d t‖ ^ 2) atTop (𝓝 0) := by
    have hz (q : ℝ) : ‖d q - d q‖ = 0 := by
      rw [sub_self]
      exact ContinuousLinearMap.opNorm_zero
    simp only [hz, zero_pow (by decide : 2 ≠ 0), integral_zero]
    exact tendsto_const_nhds
  have hprodD := strongL2_duality_L1 hWkLp (fun _ => hdLp) hWLp hdLp hWlim hdlim
  intro s hs t ht
  have hIntR := intervalIntegral_tendsto_of_L1
    (fun k => dualPairing_integrable_L2 (hWkLp k) (hQLp k)) hPairR hprodR hs ht
  have hPairD := dualPairing_integrable_L2 hWLp hdLp
  have hPairDk (k : ℕ) := dualPairing_integrable_L2 (hWkLp k) hdLp
  have hIntD := intervalIntegral_tendsto_of_L1 hPairDk hPairD hprodD hs ht
  have toInt (f : ℝ → ℝ) (hf : IntegrableOn f (Ioo 0 T)) : IntervalIntegrable f volume s t := by
    have hfc : IntegrableOn f (Icc 0 T) := by
      simpa only [IntegrableOn, restrict_Ioo_eq_restrict_Icc] using hf
    exact (hfc.mono_set (uIcc_subset_Icc hs ht)).intervalIntegrable
  have hInt : Tendsto (fun k => ∫ q in s..t, Sk k q (Wk k q)) atTop
      (𝓝 (∫ q in s..t, S q (W q))) := by
    have h := hIntR.sub hIntD
    simp only [← intervalIntegral.integral_sub
      (toInt _ hPairR) (toInt _ hPairD)] at h
    convert h using 1
    funext k
    exact intervalIntegral.integral_sub
      (toInt _ (dualPairing_integrable_L2 (hWkLp k) (hQLp k))) (toInt _ (hPairDk k))
  have hzt := (huni.tendsto_at ht).sub
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => b t) atTop (𝓝 (b t)))
  have hzs := (huni.tendsto_at hs).sub
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => b s) atTop (𝓝 (b s)))
  have hEnd := (((Lp.continuous_posPart.tendsto (a t - b t)).comp hzt).norm.pow 2).sub
    (((Lp.continuous_posPart.tendsto (a s - b s)).comp hzs).norm.pow 2)
  have he (k : ℕ) : ‖Lp.posPart (J (z k t) - b t)‖ ^ 2 - ‖Lp.posPart (J (z k s) - b s)‖ ^ 2 =
      2 * ∫ q in s..t, Sk k q (Wk k q) := by
    have h := smooth_physical_shifted_positive_energy_increment g hK μ hμ O hO r hr hr0 hr2 hdr2 hRH hRD
      hT b hb hbval ((reflectedSmooth_contDiff hT hU k).of_le (by simp))
      (reflectedDualSmooth_contDiff hT hR k).continuous.continuousOn
      (fun q hq => reflectedSmooth_derivative (hilbertEmbedding J) hT hU hR hw k hq) hs ht
    simpa only [hSkval, Wk, z, Q] using h
  have hEnd' : Tendsto (fun k => 2 * ∫ q in s..t, Sk k q (Wk k q)) atTop
      (𝓝 (‖Lp.posPart (a t - b t)‖ ^ 2 - ‖Lp.posPart (a s - b s)‖ ^ 2)) := by
    convert hEnd using 1
    funext k
    exact (he k).symm
  have hfinal := tendsto_nhds_unique hEnd' (hInt.const_mul 2)
  simpa only [hSval] using hfinal

end Yau.F04Proof
