import Yau.Proofs.P06ScalarSmoothHeatDistribution
import Yau.Proofs.P06HodgeRegularityCoordinateJets

/-! Only finitely many genuine weak derivatives are needed for a
continuous representative of one prescribed spatial derivative. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BoundedContinuousFunction

namespace Yau.NodeProofs.P06Aux.ScalarSmooth
open Yau.LeafProofs.L16Aux

theorem finiteWeakJet_shift {d N s : ℕ} {u : (Fin d → ℝ) → ℝ}
    {J : List (Fin d) → (Fin d → ℝ) → ℝ}
    (hJ : FiniteCoordinateWeakJet N u J) (w : List (Fin d))
    (hs : s + w.length ≤ N) :
    FiniteCoordinateWeakJet s (J w) (fun v => J (v ++ w)) := by
  refine ⟨by simp,?_,?_⟩
  · intro v hv
    exact hJ.2.1 (v ++ w) (by simp only [List.length_append]; omega)
  · intro v hv i φ hφ hcφ
    simpa only [List.cons_append] using
      hJ.2.2 (v ++ w) (by simp only [List.length_append]; omega) i φ hφ hcφ

theorem finiteWeakJet_word_continuous {d N : ℕ} {u : (Fin d → ℝ) → ℝ}
    {J : List (Fin d) → (Fin d → ℝ) → ℝ}
    (hJ : FiniteCoordinateWeakJet N u J) (w : List (Fin d))
    (hN : w.length + d ≤ N) :
    ∃ v : (Fin d → ℝ) → ℝ, Continuous v ∧ v =ᵐ[volume] J w ∧
      tsupport v ⊆ tsupport (J w) := by
  let B : ContDiffBump (0 : Fin d → ℝ) := ⟨1,2,by norm_num,by norm_num⟩
  have hshift := finiteWeakJet_shift hJ w (s := d) (by omega)
  obtain ⟨v,hv,hAE,_⟩ := regularity_finite_weak_jet_representative (q := 0)
    B.contDiff_normed B.hasCompactSupport_normed B.nonneg_normed B.integral_normed hshift (by omega)
  refine ⟨v,hv.continuous,hAE,?_⟩
  apply closure_minimal _ (isClosed_tsupport _)
  intro z hz
  by_contra hzK
  have hzero : v =ᵐ[volume.restrict (tsupport (J w))ᶜ] (fun _ => (0 : ℝ)) := by
    filter_upwards [ae_restrict_mem (isClosed_tsupport (J w)).measurableSet.compl,
      ae_restrict_of_ae hAE] with y hy hae
    rw [hae]
    exact image_eq_zero_of_notMem_tsupport hy
  exact hz (Measure.eqOn_open_of_ae_eq hzero (isClosed_tsupport (J w)).isOpen_compl
    hv.continuous.continuousOn continuousOn_const hzK)

theorem finiteWeakJet_word_transpose {d N : ℕ} {u : (Fin d → ℝ) → ℝ}
    {J : List (Fin d) → (Fin d → ℝ) → ℝ}
    (hJ : FiniteCoordinateWeakJet N u J) (w : List (Fin d)) (hw : w.length ≤ N)
    {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) :
    (∫ z, J w z * φ z) = (-1 : ℝ)^w.length * ∫ z, u z *
      regularityCoefficientWord (fun i : Fin d => Pi.single i 1) w.reverse φ z := by
  induction w generalizing φ with
  | nil => simp only [hJ.1,List.length_nil,List.reverse_nil,regularityCoefficientWord,pow_zero,one_mul]
  | cons i w ih =>
    have hw' : w.length < N := by simp only [List.length_cons] at hw; omega
    have hweak := hJ.2.2 w hw' i φ hφ hcφ
    have hdir : ContDiff ℝ ∞ (regularityDirection (Pi.single i 1) φ) :=
      regularityDirection_contDiff hφ _
    have hcdir : HasCompactSupport (regularityDirection (Pi.single i 1) φ) :=
      hcφ.fderiv_apply ℝ _
    have hrev : regularityCoefficientWord (fun i : Fin d => Pi.single i 1)
        (i::w).reverse φ = regularityCoefficientWord (fun i : Fin d => Pi.single i 1)
          w.reverse (regularityDirection (Pi.single i 1) φ) := by
      rw [List.reverse_cons,regularityCoefficientWord_append]
      rfl
    have htail := ih hw'.le hdir hcdir
    rw [hrev,List.length_cons,pow_succ]
    change (∫ z, J w z * regularityDirection (Pi.single i 1) φ z) =
      -(∫ z, J (i::w) z * φ z) at hweak
    linarith

/-- The finite weak jet supplies an actual bounded continuous representative
of each prescribed derivative, retaining its original compact support and
the exact distributional transpose identity. -/
theorem finiteWeakJet_word_bcf {d N : ℕ} {u : (Fin d → ℝ) → ℝ}
    {J : List (Fin d) → (Fin d → ℝ) → ℝ}
    (hJ : FiniteCoordinateWeakJet N u J) (w : List (Fin d))
    (hN : w.length + d ≤ N) {K : Set (Fin d → ℝ)} (hK : IsCompact K)
    (hJK : tsupport (J w) ⊆ K) :
    ∃ v : (Fin d → ℝ) →ᵇ ℝ, tsupport (v : (Fin d → ℝ) → ℝ) ⊆ K ∧
      ∀ φ, regularityTest Set.univ φ → (∫ z, v z * φ z) =
        (-1 : ℝ)^w.length * ∫ z, u z *
          regularityCoefficientWord (fun i : Fin d => Pi.single i 1) w.reverse φ z := by
  obtain ⟨v,hv,hAE,hvK⟩ := finiteWeakJet_word_continuous hJ w hN
  have hc : HasCompactSupport v :=
    hK.of_isClosed_subset (isClosed_tsupport _) (hvK.trans hJK)
  refine ⟨ofCompactSupport v hv hc,hvK.trans hJK,?_⟩
  intro φ hφ
  change (∫ z, v z * φ z) = _
  rw [integral_congr_ae (hAE.mono fun z hz => congrArg (· * φ z) hz)]
  exact finiteWeakJet_word_transpose hJ w (by omega) hφ.1 hφ.2.1

/-- On any Banach domain, existence of genuine finite weak jets gives a
bounded map for the chosen word. The pairing on the right uses the original
L² map, so arbitrary choices of raw representatives disappear. -/
theorem finiteWeakJet_boundedLift {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] [CompleteSpace H] {d N : ℕ}
    (P : H →L[ℝ] Lp ℝ 2 (volume : Measure (Fin d → ℝ)))
    (w : List (Fin d)) (hN : w.length + d ≤ N)
    {K : Set (Fin d → ℝ)} (hK : IsCompact K)
    (hfinite : ∀ f : H, ∃ u J, FiniteCoordinateWeakJet N u J ∧
      u =ᵐ[volume] (P f : (Fin d → ℝ) → ℝ) ∧ tsupport (J w) ⊆ K) :
    ∃ L : H →L[ℝ] ((Fin d → ℝ) →ᵇ ℝ),
      (∀ f, tsupport (L f : (Fin d → ℝ) → ℝ) ⊆ K) ∧ ∀ f φ,
      regularityTest Set.univ φ → (∫ z, L f z * φ z) =
        (-1 : ℝ)^w.length * ∫ z, P f z *
          regularityCoefficientWord (fun i : Fin d => Pi.single i 1) w.reverse φ z := by
  have hex (f : H) : ∃ v : (Fin d → ℝ) →ᵇ ℝ,
      tsupport (v : (Fin d → ℝ) → ℝ) ⊆ K ∧
      ∀ φ, regularityTest Set.univ φ → (∫ z, v z * φ z) =
        (-1 : ℝ)^w.length * ∫ z, P f z *
          regularityCoefficientWord (fun i : Fin d => Pi.single i 1) w.reverse φ z := by
    obtain ⟨u,J,hJ,hAE,hJK⟩ := hfinite f
    obtain ⟨v,hv,hpair⟩ := finiteWeakJet_word_bcf hJ w hN hK hJK
    refine ⟨v,hv,fun φ hφ => (hpair φ hφ).trans ?_⟩
    congr 1
    exact integral_congr_ae (hAE.mono fun z hz => congrArg (· * _) hz)
  choose R hRK hpair using hex
  let D (φ : (Fin d → ℝ) → ℝ) (hφ : regularityTest Set.univ φ) :
      Lp ℝ 2 (volume : Measure (Fin d → ℝ)) :=
    (-1 : ℝ)^w.length •
      (((regularityCoefficientWord_regular (fun i : Fin d => Pi.single i 1)
        hφ.1 hφ.2.1 w.reverse).1.continuous.memLp_of_hasCompactSupport
          (regularityCoefficientWord_regular (fun i : Fin d => Pi.single i 1)
            hφ.1 hφ.2.1 w.reverse).2.1).toLp _)
  have hpair' (f : H) (φ : (Fin d → ℝ) → ℝ) (hφ : regularityTest Set.univ φ) :
      (∫ z, R f z * φ z) = inner ℝ (P f) (D φ hφ) := by
    rw [hpair f φ hφ]
    simp only [D,real_inner_smul_right,regularityLp_integral_pairing]
  exact ⟨distributionLiftCLM volume P D R hK hRK hpair',hRK,hpair⟩

end Yau.NodeProofs.P06Aux.ScalarSmooth
