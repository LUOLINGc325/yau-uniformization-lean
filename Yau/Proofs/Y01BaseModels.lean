import Yau.Proofs.Y01ModelCenters
import Yau.Proofs.Y01ModelGrowth
import Yau.Proofs.Y01TransitionJetBounds
import Yau.Proofs.Y01TransitionRegularity
import Yau.Proofs.Y01GridModels

/-! Full polynomial models on one canonical base grid, constructed from the
original Y02/Y03/Y05/Y06 outputs. The same R/Rinv remain visible for exact tail
restriction; Cd is the geometry-independent original realization constant. -/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Yau.Proofs.Y01Aux

open Filter Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux
open scoped ContDiff

variable {n d : ℕ}

theorem base_polynomial_models_from_original_outputs
    {Dd Dsix Dtotal : ℕ} {Craw : ℝ} (hd : 1 ≤ d)
    (hDd : d ≤ Dtotal) (hDrealize : Dd ≤ Dtotal) (hDsix : Dsix ≤ Dtotal)
    (hrealize : ∀ P : PolyMap n, IsConstantVolumeJet P d →
      ∃ G Ginv : PolyMap n, IsPolyAutomorphism G Ginv ∧ PolyMap.JetEq G P d ∧
        G.degree ≤ Dd ∧ Ginv.degree ≤ Dd ∧
        G.coeffNorm + Ginv.coeffNorm ≤ Craw * (1 + P.coeffNorm + matOpNorm P.linearPart⁻¹) ^ Craw)
    {X : KahlerManifold n} {o : Pt X} {h : Flow X} {ρ : STF X}
    {r₀ r₁ σ Cgeo Cb t₀ : ℝ} {Φ : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {f : ℝ → Pt X → ComplexVector n}
    (hcharts : ShrinkingCharts X o h ρ r₀ r₁ σ Cgeo Cb t₀ Φ F f)
    {tk : ℕ → ℝ} {E : Frames n} (hE : SingularFrames F tk E)
    {Qclock : ℕ → ℝ} {N j₀ : ℕ} {M hm scale K eps : ℝ}
    (hhm : 0 < hm) (hgrid : GridLayout Qclock N M hm j₀)
    (hdom : ∀ k, t₀ ≤ tk k) (hρ : ∀ k, ρ o (tk k) = gridClock Qclock N M hm j₀ k)
    (hs2 : ∀ k, 2 ≤ gridClock Qclock N M hm j₀ k)
    {L : Changes n} {C c : ℝ} (hc : 0 < c)
    (hL : ∀ k, Regular Qclock N M (macroAt Qclock N M hm j₀ k) →
      ChangeAt (diagonal F tk E) (weight Qclock N M hm scale K eps j₀ (rate F tk E))
        (macroAt Qclock N M hm j₀) (macroClock hm) C c L k)
    {r : ℝ} {last : Fin n} {logs : ℕ → ComplexVector n → ℂ}
    {B : ℕ → ℕ → MvPolynomial (Fin n) ℂ} {ell Evol : ℕ → MvPolynomial (Fin n) ℂ}
    {A Ainv V : ℕ → PolyMap n}
    (hVol : CoherentVolume F tk (gridClock Qclock N M hm j₀) d r last logs B ell Evol A Ainv V)
    {kLate : ℕ} {Cq BF : ℝ} {qsol : JetData n}
    (hQ : RegularJetSolution (normalizedRegularTransition F tk A Ainv E L) (diagonal F tk E)
      (fun k => if Regular Qclock N M (macroAt Qclock N M hm j₀ (k + 1)) then alignedJump E L k else 1)
      (weight Qclock N M hm scale K eps j₀ (rate F tk E))
      (fun k => kLate ≤ k ∧ Regular Qclock N M (macroAt Qclock N M hm j₀ k))
      d Dsix (gridClock Qclock N M hm j₀) Cq qsol)
    (hFnorm : ∀ k, jetNorm (F (tk k) (tk (k + 1))) d ≤ BF) :
    let s := gridClock Qclock N M hm j₀
    let reg := fun k => Regular Qclock N M (macroAt Qclock N M hm j₀ k)
    let T := primaryDerivative reg E L
    let H := fun k => coordinateJet d (A k) (qsol.correction k) (T k)
    let Hinv := fun k => inverseCoordinateJet d (Ainv k) (qsol.inverseJet k) (T k)
    let J := fun k => if reg (k + 1) then alignedJump E L k else 1
    let active := fun k => kLate ≤ k ∧ reg k
    let Jet := fun k => badStepJet d (qsol.correction (k + 1)) (V k) (qsol.inverseJet k) (T k) (T (k + 1))
    ∃ R Rinv : ℕ → PolyMap n,
      (∀ k, IsPolyAutomorphism (R k) (Rinv k) ∧ PolyMap.JetEq (R k) (Jet k) d ∧
        (R k).degree ≤ Dd ∧ (Rinv k).degree ≤ Dd ∧
        (R k).coeffNorm + (Rinv k).coeffNorm ≤
          Craw * (1 + (Jet k).coeffNorm + matOpNorm (Jet k).linearPart⁻¹) ^ Craw) ∧
      PolynomialModels X o ρ F d hm (1 + |Craw|) (Dtotal : ℝ) tk H Hinv
        (assembledModel active J qsol R) (assembledInverseModel active J qsol Rinv) := by
  let s := gridClock Qclock N M hm j₀
  let reg := fun k => Regular Qclock N M (macroAt Qclock N M hm j₀ k)
  let T := primaryDerivative reg E L
  let H := fun k => coordinateJet d (A k) (qsol.correction k) (T k)
  let Hinv := fun k => inverseCoordinateJet d (Ainv k) (qsol.inverseJet k) (T k)
  let J := fun k => if reg (k + 1) then alignedJump E L k else 1
  let active := fun k => kLate ≤ k ∧ reg k
  let Jet := fun k => badStepJet d (qsol.correction (k + 1)) (V k) (qsol.inverseJet k) (T k) (T (k + 1))
  have hs k : 1 ≤ s k := (by norm_num : (1 : ℝ) ≤ 2).trans (hs2 k)
  have hSmooth k := shrinking_transition_smooth hcharts (hdom k) (hE k).2.1.le
  have hF k : ContDiffAt ℂ d (F (tk k) (tk (k + 1))) 0 :=
    (hSmooth k).1.of_le (WithTop.coe_le_coe.mpr le_top)
  have hF0 k : F (tk k) (tk (k + 1)) 0 = 0 := (hSmooth k).2
  have hBF : 0 ≤ BF := (jetNorm_nonneg _ d).trans (hFnorm 0)
  have hCoord := coordinate_data_from_original_outputs (reg := reg) hE hL hVol hd hQ
  have hInputs := badStepJet_data_from_original_outputs (reg := reg) hE hL hVol hd hQ hF hF0
  obtain ⟨R, Rinv, hR⟩ := original_realizations_on_all_steps (Jet := Jet) hrealize (fun k => (hInputs k).1)
  let G := assembledModel active J qsol R
  let Ginv := assembledInverseModel active J qsol Rinv
  have hRjet k : PolyMap.JetEq (R k) (Jet k) d := (hR k).2.1
  have hRzero k : (R k).FixesZero := jetEq_fixesZero (hRjet k) (hInputs k).1.1
  have hJunit k (hk : active k) : IsUnit (J k) := regular_alignedJump_isUnit hE hL hk.2
  have hAuto := assembled_models_automorphisms hQ hJunit (fun k => (hR k).1)
  have hZero := assembled_model_fixesZero (J := J) hQ hRzero
  have hDegrees := assembled_models_degree (J := J) hQ (fun k => ⟨(hR k).2.2.1, (hR k).2.2.2.1⟩)
  have hDmax : max Dd Dsix ≤ Dtotal := max_le hDrealize hDsix
  have hConjugacy := assembled_models_original_conjugacy (reg := reg) hE hL hVol hd hQ hF hF0 hRjet
  have hMatrices := actual_models_center_conjugacies (reg := reg) hE hL hVol hd hQ hF hF0 hRjet
  obtain ⟨Cp, hCp, hCenter⟩ := center_bounds_from_original_changes hcharts hE hhm hgrid hdom hρ hs2 hc hL
  obtain ⟨Ch, hCh, hHcoeff⟩ := coordinate_coeffNorm_sqrt_bounds hE hhm hgrid hc hL hVol hd hQ
  obtain ⟨ch, Chgrid, hch, hChgrid, hsteps⟩ := hgrid.2.2.2.2.2
  have hUpper k : s (k + 1) - s k ≤ (Real.exp hm - 1) * s k := (hsteps k).2.1
  have hHenv : ∃ C : ℝ, 0 ≤ C ∧ ∀ k, (H k).coeffNorm ≤ Real.exp (C * Real.sqrt (s k)) :=
    ⟨Ch, hCh, fun k => (hHcoeff k).1⟩
  have hIenv : ∃ C : ℝ, 0 ≤ C ∧ ∀ k, (Hinv k).coeffNorm ≤ Real.exp (C * Real.sqrt (s k)) :=
    ⟨Ch, hCh, fun k => (hHcoeff k).2⟩
  obtain ⟨Cjet, hCjet, hJetCoeff⟩ := transitionJet_coeffNorm_sqrt_bounds hs hUpper hBF hF hF0 hFnorm
    hHenv hIenv (fun k => (hCoord k).2.1) (fun k => (hInputs k).1.2.1)
    (fun k => germJetEq_symm (hInputs k).2)
  have hJetInv k : matOpNorm (Jet k).linearPart⁻¹ ≤
      Real.exp ((s (k + 1) - s k) / 2 + (4 * |Cp|) * Real.sqrt (s k)) :=
    inverse_growth_sqrt_envelope (hs k) (zero_le_one.trans hCp)
      ((hCenter k).2.2 (Jet k).linearPart (hMatrices k).1)
  obtain ⟨Cj, hCj, hJump⟩ := alignedJump_coeffNorm_sqrt_bound hE hhm hgrid hs2 hc hL
  have hΔ k : 0 ≤ s (k + 1) - s k := sub_nonneg.2 (hgrid.2.1.monotone (Nat.le_succ k))
  obtain ⟨Cg, hCg, hGcoeff⟩ := assembled_models_coeffNorm_bound (J := J) (Jet := Jet) hQ hs hΔ hCj
    (fun k hk => hJump k hk.2) hJetCoeff hJetInv (fun k => (hR k).2.2.2.2)
  let Cη := max Ch Cg
  let η := fun k => Cη / Real.sqrt (s k)
  have hη := sqrt_error_tendsto hgrid.2.2.1 Cη
  have hηid k : η k * s k = Cη * Real.sqrt (s k) := sqrt_error_identity (by linarith [hs k])
  have hρfun : (fun k => ρ o (tk k)) = s := funext hρ
  refine ⟨R, Rinv, hR, ?_⟩
  change PolynomialModels X o ρ F d hm (1 + |Craw|) (Dtotal : ℝ) tk H Hinv G Ginv
  refine ⟨strictMono_nat_of_lt_succ (fun k => (hE k).2.1), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hρfun]
    exact hgrid.2.2.1
  · obtain ⟨c₁, C₁, hc₁, hzero, hendpoints, hsubdivision⟩ := canonical_macro_subdivision hhm hgrid
    refine ⟨j₀, c₁, C₁, hc₁, ?_, ?_, ?_⟩
    · simpa only [hρ, macroClock] using hzero
    · intro j hj
      obtain ⟨k, hk⟩ := hendpoints j hj
      exact ⟨k, by simpa only [hρ, macroClock] using hk⟩
    · intro j hj
      simpa only [hρ, macroClock] using hsubdivision j hj
  · refine ⟨ch, hch, 0, ?_⟩
    intro k hk
    simpa only [hρ] using And.intro (hsteps k).1 (hsteps k).2.1
  · intro k
    obtain ⟨hH0, hI0, hHdegree, hIdegree, hHlinear, hIlinear, hTunit, hHleft, hHright⟩ := hCoord k
    have hDet : (H k).linearPart.det ≠ 0 := by
      rw [hHlinear]
      exact isUnit_iff_ne_zero.1 ((Matrix.isUnit_iff_isUnit_det _).1 hTunit)
    exact ⟨hH0, hI0, hIdegree, hZero k, hAuto k, hDet, hHleft⟩
  · intro k
    exact hConjugacy k
  · intro k
    have hHdegree := (hCoord k).2.2.1
    refine ⟨?_, ?_, ?_⟩
    · exact_mod_cast hHdegree.trans hDd
    · exact_mod_cast (hDegrees k).1.trans hDmax
    · exact_mod_cast (hDegrees k).2.trans hDmax
  · refine ⟨η, hη, ?_⟩
    intro k
    have hHmax : Ch * Real.sqrt (s k) ≤ Cη * Real.sqrt (s k) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
    have hGmax : Cg * Real.sqrt (s k) ≤ Cη * Real.sqrt (s k) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _)
    refine ⟨?_, ?_, ?_⟩
    · change (H k).coeffNorm ≤ Real.exp (η k * ρ o (tk k))
      rw [hρ k, hηid k]
      exact (hHcoeff k).1.trans (Real.exp_le_exp.2 hHmax)
    · change (Hinv k).coeffNorm ≤ Real.exp (η k * ρ o (tk k))
      rw [hρ k, hηid k]
      exact (hHcoeff k).2.trans (Real.exp_le_exp.2 hHmax)
    · change (G k).coeffNorm + (Ginv k).coeffNorm ≤
        Real.exp ((1 + |Craw|) * (ρ o (tk (k + 1)) - ρ o (tk k)) + η k * ρ o (tk k))
      rw [hρ k, hρ (k + 1), hηid k]
      exact (hGcoeff k).trans (Real.exp_le_exp.2 (by linarith))
  · refine ⟨Nat.ceil Cp, ?_⟩
    intro k
    have hCeil : Cp ≤ (Nat.ceil Cp : ℝ) := Nat.le_ceil Cp
    have hOnePow : (1 + s k) ^ Cp ≤ (1 + s k) ^ (Nat.ceil Cp) := by
      calc
        _ ≤ (1 + s k) ^ (Nat.ceil Cp : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [hs k]) hCeil
        _ = _ := Real.rpow_natCast _ _
    have hSPow : s k ^ Cp ≤ s k ^ (Nat.ceil Cp) := by
      calc
        _ ≤ s k ^ (Nat.ceil Cp : ℝ) := Real.rpow_le_rpow_of_exponent_le (hs k) hCeil
        _ = _ := Real.rpow_natCast _ _
    have hHlinear := (hCoord k).2.2.2.2.1
    have hTnorm := (hCenter k).1
    have hTinorm := (hCenter k).2.1
    have hGnorm := (hCenter k).2.2 (G k).linearPart (hMatrices k).2
    refine ⟨?_, ?_, ?_⟩
    · change matOpNorm (H k).linearPart ≤ (1 + ρ o (tk k)) ^ (Nat.ceil Cp)
      rw [hρ k, hHlinear]
      exact hTnorm.trans hOnePow
    · change matOpNorm (H k).linearPart⁻¹ ≤ (1 + ρ o (tk k)) ^ (Nat.ceil Cp)
      rw [hρ k, hHlinear]
      exact hTinorm.trans hOnePow
    · change matOpNorm (G k).linearPart⁻¹ ≤ ρ o (tk k) ^ (Nat.ceil Cp) *
        Real.exp ((ρ o (tk (k + 1)) - ρ o (tk k)) / 2)
      rw [hρ k, hρ (k + 1)]
      exact hGnorm.trans (mul_le_mul_of_nonneg_right hSPow (Real.exp_pos _).le)
  · exact all_forward_automorphisms hAuto

end Yau.Proofs.Y01Aux
