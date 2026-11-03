import Yau.Proofs.F01NativeRestartWholeIntervalSmooth
import Yau.Proofs.F01FieldHeatPenalty

/-! The explicitly pasted native potential satisfies the original
closed-domain determinant clock equation, including the joined face.
The joined derivative follows from proved joint smoothness and the
actual right derivative; it is not a new hypothesis. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem native_restart_paste_closed_time_equation
    (g : HermitianField M) (h hR : ℝ → HermitianField M)
    (U : M.Carrier → ℝ → ℝ) (u : M.Carrier → ℝ) (W : M.Carrier → ℝ → ℝ)
    {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε) (hW0 : ∀ y, W y 0 = u y)
    (hpde : ∀ s, 0 ≤ s → s < T → ∀ x t, t ∈ Icc 0 s →
      HasDerivWithinAt (U x) (flowLogDetRatio g h x t) (Icc 0 s) t)
    (hRPde : ∀ x s, s ∈ Icc 0 ε → HasDerivWithinAt (W x)
      (flowLogDetRatio g hR x s) (Icc 0 ε) s)
    (hSmooth : SmoothSpaceTime (nativePastedRestartPotential U u W T) (Icc 0 (T + ε / 2))) :
    ∀ x t, t ∈ Icc 0 (T + ε / 2) →
      HasDerivWithinAt (nativePastedRestartPotential U u W T x)
        (flowLogDetRatio g (nativePastedRestartFlow h hR T) x t) (Icc 0 (T + ε / 2)) t := by
  let V := nativePastedRestartPotential U u W T
  intro x t ht
  rcases lt_trichotomy t T with hlt | he | hgt
  · let θ : ℝ := (t + T) / 2
    have htθ : t < θ := by dsimp only [θ]; linarith
    have hθT : θ < T := by dsimp only [θ]; linarith
    have hθ0 : 0 ≤ θ := ht.1.trans htθ.le
    have hOld : HasDerivWithinAt (U x) (flowLogDetRatio g h x t) (Ici 0) t := by
      apply (hasDerivWithinAt_inter (Iic_mem_nhds htθ)).mp
      simpa only [Ici_inter_Iic] using hpde θ hθ0 hθT x t ⟨ht.1, htθ.le⟩
    have hEq : V x =ᶠ[𝓝[Ici 0] t] U x := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hlt)] with s hs
      exact nativePastedRestartPotential_before U u W T x hs
    have hh : HasDerivWithinAt (V x) (flowLogDetRatio g h x t) (Icc 0 (T + ε / 2)) t :=
      (hOld.congr_of_eventuallyEq hEq
        (nativePastedRestartPotential_before U u W T x hlt)).mono Icc_subset_Ici_self
    simpa only [flowLogDetRatio, nativePastedRestartFlow, if_pos hlt] using hh
  · subst t
    have hMap : MapsTo (fun s : ℝ => s - T) (Icc T (T + ε)) (Icc 0 ε) := by
      intro s hs
      constructor <;> linarith [hs.1, hs.2]
    have hShift : HasDerivWithinAt (fun s : ℝ => s - T) 1 (Icc T (T + ε)) T :=
      ((hasDerivAt_id T).sub_const T).hasDerivWithinAt
    have hRightClock : HasDerivWithinAt (fun s => W x (s - T))
        (flowLogDetRatio g hR x 0) (Icc T (T + ε)) T := by
      have hAt : HasDerivWithinAt (W x) (flowLogDetRatio g hR x 0) (Icc 0 ε) (T - T) := by
        simpa only [sub_self] using hRPde x 0 ⟨le_rfl, hε.le⟩
      have hh := hAt.comp T (h := fun s : ℝ => s - T) hShift hMap
      simpa only [sub_self, Function.comp_def, mul_one] using hh
    have hRightLE : HasDerivWithinAt (fun s => W x (s - T))
        (flowLogDetRatio g hR x 0) (Ici T) T := by
      apply (hasDerivWithinAt_inter (Iic_mem_nhds (by linarith : T < T + ε))).mp
      simpa only [Ici_inter_Iic] using hRightClock
    have hRight : HasDerivWithinAt (V x) (flowLogDetRatio g hR x 0) (Ici T) T :=
      hRightLE.congr_of_mem
        (fun s hs => nativePastedRestartPotential_after U u W T hW0 x hs) (by simp)
    have hN : Icc 0 (T + ε / 2) ∈ 𝓝 T := Icc_mem_nhds hT (by linarith)
    have hFull := ((smoothSpaceTime_time_slice hSmooth x T ⟨hT.le, by linarith⟩).differentiableWithinAt
      (by simp)).hasDerivWithinAt.hasDerivAt hN
    have hFullValue := (hFull.hasDerivWithinAt (s := Ici T)).derivWithin (uniqueDiffWithinAt_Ici T)
    have hRightValue := hRight.derivWithin (uniqueDiffWithinAt_Ici T)
    have hValue := hFullValue.symm.trans hRightValue
    have hh := (hFull.congr_deriv hValue).hasDerivWithinAt (s := Icc 0 (T + ε / 2))
    simpa only [flowLogDetRatio, nativePastedRestartFlow, lt_self_iff_false, ite_false, sub_self] using hh
  · have hs0 : 0 < t - T := sub_pos.mpr hgt
    have hsε : t - T < ε := by linarith [ht.2]
    have hOld := (hRPde x (t - T) ⟨hs0.le, hsε.le⟩).hasDerivAt (Icc_mem_nhds hs0 hsε)
    have hShift := (hasDerivAt_id t).sub_const T
    have hBase : HasDerivAt (fun s => W x (s - T)) (flowLogDetRatio g hR x (t - T)) t := by
      simpa only [Function.comp_def, mul_one, id_eq] using hOld.comp t hShift
    have hEq : V x =ᶠ[𝓝 t] (fun s => W x (s - T)) := by
      filter_upwards [Ioi_mem_nhds hgt] with s hs
      exact nativePastedRestartPotential_after U u W T hW0 x hs.le
    have hh := (hBase.congr_of_eventuallyEq hEq).hasDerivWithinAt (s := Icc 0 (T + ε / 2))
    simpa only [flowLogDetRatio, nativePastedRestartFlow, if_neg (not_lt.mpr hgt.le)] using hh

end Yau.NodeProofs.F01Aux
