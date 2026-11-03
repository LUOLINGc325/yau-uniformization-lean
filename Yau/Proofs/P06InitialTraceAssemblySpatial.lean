import Yau.Proofs.P06InitialTraceAssemblyDecay
import Yau.Blueprint.HodgeContracts

/-! The initial-trace triangle argument after positive-time spatial jet limits.
No remote estimate or compact-data heat construction is assumed as a solver. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold

namespace Yau.NodeProofs.P06Aux.InitialTrace
open Yau Yau.Blueprint
variable {n k : ℕ} {M : ComplexManifold n}

def SpatialJetLimit (Us : ℕ → ℝ → RealForm M k) (U : ℝ → RealForm M k) : Prop :=
  ∀ x z, z ∈ chartTarget x → ∀ t, 0 < t → ∀ m (I : Fin k → RIdx n),
    Tendsto (fun l => iteratedFDeriv ℝ m (fun w => formComponents (Us l t) x w I) z)
      atTop (𝓝 (iteratedFDeriv ℝ m (fun w => formComponents (U t) x w I) z))

theorem component_contDiffAt (A : RealForm M k) (hA : SmoothRealForm A)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x)
    (m : ℕ) (I : Fin k → RIdx n) :
    ContDiffAt ℝ m (fun w => formComponents A x w I) z :=
  ((hA x I).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).of_le (by simp)

theorem spatialJet_difference_tendsto
    (Us : ℕ → ℝ → RealForm M k) (U : ℝ → RealForm M k)
    (hpos : SpatialJetLimit Us U)
    (hUs : ∀ l, 1 ≤ l → ∀ t, 0 < t → SmoothRealForm (Us l t))
    (hU : ∀ t, 0 < t → SmoothRealForm (U t))
    {J : ℕ} (hJ : 1 ≤ J) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (m : ℕ) (I : Fin k → RIdx n) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun l => iteratedFDeriv ℝ m (fun w =>
      formComponents (Us l t) x w I - formComponents (Us J t) x w I) z) atTop
      (𝓝 (iteratedFDeriv ℝ m (fun w =>
        formComponents (U t) x w I - formComponents (Us J t) x w I) z)) := by
  have hJsm := component_contDiffAt (Us J t) (hUs J hJ t ht) x hz m I
  have hUsm := component_contDiffAt (U t) (hU t ht) x hz m I
  have hh := (hpos x z hz t ht m I).sub_const
    (iteratedFDeriv ℝ m (fun w => formComponents (Us J t) x w I) z)
  rw [← iteratedFDeriv_sub_apply hUsm hJsm] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with l hl
  change _ = iteratedFDeriv ℝ m
    ((fun w => formComponents (Us l t) x w I) - fun w => formComponents (Us J t) x w I) z
  exact (iteratedFDeriv_sub_apply
    (component_contDiffAt (Us l t) (hUs l hl t ht) x hz m I) hJsm).symm

/-- This is only the natural quantified remote estimate to be proved by the
cylinder and Gaussian-tail estimates; it is not an extra P06 premise. -/
def RemoteJetBounds (As : ℕ → RealForm M k) (A : RealForm M k)
    (Us : ℕ → ℝ → RealForm M k) : Prop :=
  ∀ x (K : Set (ComplexVector n)), IsCompact K → K ⊆ chartTarget x →
    ∀ m (I : Fin k → RIdx n), ∃ (J N p : ℕ) (a C τ0 : ℝ),
      1 ≤ J ∧ 1 ≤ N ∧ 0 < a ∧ 0 ≤ C ∧ 0 < τ0 ∧
      (∀ z ∈ K, (fun w => formComponents (As J) x w I) =ᶠ[𝓝 z]
        (fun w => formComponents A x w I)) ∧
      ∀ l, N ≤ l → ∀ t, 0 < t → t < τ0 → ∀ z ∈ K,
        ‖iteratedFDeriv ℝ m (fun w =>
          formComponents (Us l t) x w I - formComponents (Us J t) x w I) z‖ ≤
          (C / t ^ p) * Real.exp (-a / t)

theorem formSmoothInitial_of_spatialJetLimit_remoteBounds
    (As : ℕ → RealForm M k) (A : RealForm M k)
    (Us : ℕ → ℝ → RealForm M k) (U : ℝ → RealForm M k)
    (hA : SmoothRealForm A) (hzero : U 0 = A)
    (hUs : ∀ l, 1 ≤ l → ∀ t, 0 < t → SmoothRealForm (Us l t))
    (hU : ∀ t, 0 < t → SmoothRealForm (U t))
    (hinit : ∀ J, 1 ≤ J → FormSmoothInitial (Us J) (As J))
    (hpos : SpatialJetLimit Us U) (hremote : RemoteJetBounds As A Us) :
    FormSmoothInitial U A := by
  refine ⟨hzero, ?_⟩
  intro x K hK hKO m I ε hε
  obtain ⟨J, N, p, a, C, τ0, hJ, hN, ha, hC, hτ0, hgerm, htail⟩ := hremote x K hK hKO m I
  obtain ⟨τ1, hτ1, hr⟩ := remoteRate_small C a p ha (half_pos hε)
  obtain ⟨τ2, hτ2, hi⟩ := (hinit J hJ).2 x K hK hKO m I (ε / 2) (half_pos hε)
  refine ⟨min τ0 (min τ1 τ2), lt_min hτ0 (lt_min hτ1 hτ2), ?_⟩
  intro t ht htτ z hz
  obtain ⟨ht0, ht12⟩ := lt_min_iff.mp htτ
  obtain ⟨ht1, ht2⟩ := lt_min_iff.mp ht12
  have hremoteLimit : ‖iteratedFDeriv ℝ m (fun w =>
      formComponents (U t) x w I - formComponents (Us J t) x w I) z‖ ≤
      (C / t ^ p) * Real.exp (-a / t) := by
    apply le_of_tendsto (spatialJet_difference_tendsto Us U hpos hUs hU hJ x (hKO hz) m I ht).norm
    filter_upwards [eventually_ge_atTop N] with l hl
    exact htail l hl t ht ht0 z hz
  have heq : (fun w => formComponents (Us J t) x w I - formComponents A x w I) =ᶠ[𝓝 z]
      (fun w => formComponents (Us J t) x w I - formComponents (As J) x w I) := by
    filter_upwards [hgerm z hz] with w hw
    rw [hw]
  have hsmall : ‖iteratedFDeriv ℝ m (fun w =>
      formComponents (Us J t) x w I - formComponents A x w I) z‖ < ε / 2 := by
    rw [(heq.iteratedFDeriv ℝ m).eq_of_nhds]
    exact hi t ht ht2 z hz
  have hsmU := component_contDiffAt (U t) (hU t ht) x (hKO hz) m I
  have hsmJ := component_contDiffAt (Us J t) (hUs J hJ t ht) x (hKO hz) m I
  have hsmA := component_contDiffAt A hA x (hKO hz) m I
  have hsplit : iteratedFDeriv ℝ m (fun w =>
      formComponents (U t) x w I - formComponents A x w I) z =
      iteratedFDeriv ℝ m (fun w =>
        formComponents (U t) x w I - formComponents (Us J t) x w I) z +
      iteratedFDeriv ℝ m (fun w =>
        formComponents (Us J t) x w I - formComponents A x w I) z := by
    change iteratedFDeriv ℝ m
      ((fun w => formComponents (U t) x w I) - fun w => formComponents A x w I) z =
      iteratedFDeriv ℝ m
        ((fun w => formComponents (U t) x w I) - fun w => formComponents (Us J t) x w I) z +
      iteratedFDeriv ℝ m
        ((fun w => formComponents (Us J t) x w I) - fun w => formComponents A x w I) z
    rw [iteratedFDeriv_sub_apply hsmU hsmA,
      iteratedFDeriv_sub_apply hsmU hsmJ, iteratedFDeriv_sub_apply hsmJ hsmA]
    abel
  rw [hsplit]
  exact (norm_add_le _ _).trans_lt (by
    have hsmallRemote := hremoteLimit.trans_lt (hr t ht ht1)
    linarith)

end Yau.NodeProofs.P06Aux.InitialTrace
