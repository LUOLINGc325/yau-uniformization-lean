import Yau.LeafProofs.L16InteriorLocalization

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

theorem spatialDifferenceQuotient_local_flux {n : ℕ} {Q : Set (Point n)}
    {a : Point n → Mat n} {H P : Point n → Yau.RIdx n → ℝ}
    (hP : ∀ p ∈ Q, ∀ i, P p i = energyFlux a H p i)
    (e : Space n) (h : ℝ) {p : Point n} (hp : p ∈ Q)
    (hq : spatialTranslatePoint (h • e) p ∈ Q) (i : Yau.RIdx n) :
    spatialDifferenceQuotient (fun q => P q i) e h p =
      energyFlux (spatialTranslate (h • e) a)
        (fun q j => spatialDifferenceQuotient (fun z => H z j) e h q) p i+
      energyFlux (spatialDifferenceQuotient a e h) H p i := by
  have hEq0 := hP p hp i
  have hEq1 := hP (spatialTranslatePoint (h • e) p) hq i
  simp only [spatialTranslatePoint] at hEq1
  have hDiff : spatialDifferenceQuotient (fun q => P q i) e h p =
      spatialDifferenceQuotient (fun q => energyFlux a H q i) e h p := by
    simp only [spatialDifferenceQuotient,hEq0,hEq1]
  rw [hDiff,spatialDifferenceQuotient_energyFlux]

theorem spatialDifferenceQuotient_local_source {n : ℕ} {Q : Set (Point n)}
    {c H : Point n → Yau.RIdx n → ℝ} {R : Point n → ℝ}
    (hR : ∀ p ∈ Q, R p = ∑ j, c p j*H p j)
    (e : Space n) (h : ℝ) {p : Point n} (hp : p ∈ Q)
    (hq : spatialTranslatePoint (h • e) p ∈ Q) :
    spatialDifferenceQuotient R e h p =
      (∑ j, spatialTranslate (h • e) c p j*spatialDifferenceQuotient (fun q => H q j) e h p)+
      ∑ j, spatialDifferenceQuotient (fun q => c q j) e h p*H p j := by
  have hEq0 := hR p hp
  have hEq1 := hR (spatialTranslatePoint (h • e) p) hq
  simp only [spatialTranslatePoint] at hEq1
  have hDiff : spatialDifferenceQuotient R e h p =
      spatialDifferenceQuotient (fun q => ∑ j, c q j*H q j) e h p := by
    simp only [spatialDifferenceQuotient,hEq0,hEq1]
  rw [hDiff,spatialDifferenceQuotient_driftPairing]

theorem exists_uniform_difference_energy_constant (n : ℕ) (lam upper C M : ℝ)
    (hlam : 0 < lam) (hC : 0 ≤ C) (hM : 0 ≤ M) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (Q : Set (Point n)) (a : Point n → Mat n) (c : Point n → Yau.RIdx n → ℝ)
        (θ w : Point n → ℝ) (H P : Point n → Yau.RIdx n → ℝ) (R : Point n → ℝ),
      Elliptic Q a lam upper → ContDiff ℝ ∞ a → (∀ j, ContDiff ℝ ∞ (fun p => c p j)) →
      (∀ p, ‖a p‖ ≤ C) → (∀ j p, |c p j| ≤ C) →
      (∀ i h p, ‖spatialDifferenceQuotient a (Yau.realVec i) h p‖ ≤ C) →
      (∀ j i h p, |spatialDifferenceQuotient (fun q => c q j) (Yau.realVec i) h p| ≤ C) →
      Test Q θ → (∀ p, |θ p| ≤ 1) → (∀ p, |fderiv ℝ θ p (0,1)| ≤ M) →
      (∀ p i, |fderiv ℝ θ p (Yau.realVec i,0)| ≤ M) →
      MemLp w 2 volume → (∀ j, MemLp (fun p => H p j) 2 volume) →
      (∀ j, MemLp (fun p => P p j) 2 volume) → MemLp R 2 volume →
      HasCompactSupport w → (∀ j, HasCompactSupport (fun p => H p j)) →
      (∀ j, HasCompactSupport (fun p => P p j)) → HasCompactSupport R →
      WeakGradient Set.univ Set.univ w H → WeakDivergenceEvolution Set.univ Set.univ w P R →
      (∀ p ∈ Q, ∀ j, P p j = energyFlux a H p j) →
      (∀ p ∈ Q, R p = ∑ j, c p j*H p j) →
      ∀ (i : Yau.RIdx n) (h : ℝ), h ≠ 0 →
      (∀ p ∈ tsupport θ, spatialTranslatePoint (h • Yau.realVec i) p ∈ Q) →
      (∫ p, (θ p)^2*(∑ j, (spatialDifferenceQuotient (fun q => H q j) (Yau.realVec i) h p)^2)) ≤
        B*(∫ p, ∑ j, (H p j)^2) := by
  obtain ⟨C0,hC0,hEstimate⟩ := exists_caccioppoli_constant n lam upper C C M hlam hC hC hM
  let N : ℝ := Fintype.card (Yau.RIdx n)
  let D : ℝ := (N^2+N)*C^2
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨C0*(1+D),by positivity,?_⟩
  intro Q a c θ w H P R hEll ha hc hAVal hCVal hADq hCDq hθ hθBound hθTime hθSpace
    hw hH hP hR hcw hcH hcP hcR hGrad hEq hFlux hSource i h hh hShift
  let e : Space n := Yau.realVec i
  let Qh : Set (Point n) := {p | p ∈ Q ∧ spatialTranslatePoint (h • e) p ∈ Q}
  let Wd : Point n → ℝ := spatialDifferenceQuotient w e h
  let Hd : Point n → Yau.RIdx n → ℝ := fun p j => spatialDifferenceQuotient (fun q => H q j) e h p
  let Pd : Point n → Yau.RIdx n → ℝ := fun p j => spatialDifferenceQuotient (fun q => P q j) e h p
  let Rd : Point n → ℝ := spatialDifferenceQuotient R e h
  let Fd : Point n → Yau.RIdx n → ℝ := energyFlux (spatialDifferenceQuotient a e h) H
  let fd : Point n → ℝ := fun p => ∑ j, spatialDifferenceQuotient (fun q => c q j) e h p*H p j
  have hWd : MemLp Wd 2 volume := memLp_spatialDifferenceQuotient hw e h
  have hHd (j : Yau.RIdx n) : MemLp (fun p => Hd p j) 2 volume := memLp_spatialDifferenceQuotient (hH j) e h
  have hPd (j : Yau.RIdx n) : MemLp (fun p => Pd p j) 2 volume := memLp_spatialDifferenceQuotient (hP j) e h
  have hRd : MemLp Rd 2 volume := memLp_spatialDifferenceQuotient hR e h
  obtain ⟨hFd,hfd,hForce⟩ := spatialDifferenceQuotient_forcing_L2_bounds hC ha hc hH e h
    (hADq i h) (fun p j => hCDq j i h p)
  have hGradD : WeakGradient Set.univ Set.univ Wd Hd :=
    weakGradient_spatialDifferenceQuotient hw hH hGrad e h
  have hEqD : WeakDivergenceEvolution Set.univ Set.univ Wd Pd Rd :=
    weakDivergenceEvolution_spatialDifferenceQuotient hw hP hR hEq e h
  have hcθ2 : HasCompactSupport (fun p => (θ p)^2) := by
    have hS : HasCompactSupport (fun p => θ p*θ p) := hθ.2.1.mul_right
    simpa only [pow_two] using hS
  have hEnergy : compactEnergyFunctional (fun p => (θ p)^2) Wd Hd Pd Rd = 0 :=
    weakDivergenceEvolution_compact_energy_identity hWd hHd hPd hRd
      (hasCompactSupport_spatialDifferenceQuotient hcw e h)
      (fun j => hasCompactSupport_spatialDifferenceQuotient (hcH j) e h)
      (fun j => hasCompactSupport_spatialDifferenceQuotient (hcP j) e h)
      (hasCompactSupport_spatialDifferenceQuotient hcR e h) hGradD hEqD (hθ.1.pow 2) hcθ2
  have hEllShift : Elliptic Qh (spatialTranslate (h • e) a) lam upper := by
    refine ⟨hEll.1,hEll.2.1,?_⟩
    intro p hp
    exact hEll.2.2 (spatialTranslatePoint (h • e) p) hp.2
  have hθQh : Test Qh θ := ⟨hθ.1,hθ.2.1,fun p hp => ⟨hθ.2.2 hp,hShift p hp⟩⟩
  have hLocalFlux (p : Point n) (hp : p ∈ tsupport θ) (j : Yau.RIdx n) :
      Pd p j = energyFlux (spatialTranslate (h • e) a) Hd p j+Fd p j :=
    spatialDifferenceQuotient_local_flux hFlux e h (hθ.2.2 hp) (hShift p hp) j
  have hLocalSource (p : Point n) (hp : p ∈ tsupport θ) :
      Rd p = (∑ j, spatialTranslate (h • e) c p j*Hd p j)+fd p :=
    spatialDifferenceQuotient_local_source hSource e h (hθ.2.2 hp) (hShift p hp)
  have hEst := hEstimate Qh (spatialTranslate (h • e) a) (spatialTranslate (h • e) c)
    θ Wd fd Hd Pd Fd Rd hEllShift
    (fun p _ j k => (frobenius_entry_abs_le (a (spatialTranslatePoint (h • e) p)) j k).trans (hAVal _))
    (fun p _ j => hCVal j _) hθQh hθBound hθTime hθSpace hWd hHd hPd hRd hFd hfd
    hLocalFlux hLocalSource hEnergy
  have hSquareInt {z : Point n → ℝ} (hz : MemLp z 2 volume) : Integrable (fun p => (z p)^2) volume := by
    have hZ := (memLp_two_iff_integrable_sq_norm hz.aestronglyMeasurable).mp hz
    simpa only [Real.norm_eq_abs,sq_abs] using hZ
  have hSingle : (∫ p, (H p i)^2) ≤ ∫ p, ∑ j, (H p j)^2 := by
    apply integral_mono (hSquareInt (hH i)) (integrable_sum_component_sq hH)
    intro p
    exact Finset.single_le_sum (s := Finset.univ) (f := fun j => (H p j)^2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hWBound : (∫ p, (Wd p)^2) ≤ ∫ p, ∑ j, (H p j)^2 :=
    (weakGradient_spatialDifferenceQuotient_L2_bound hw hcw hGrad i (hH i) (hcH i) hh).2.trans hSingle
  have hSplit1 := integral_add ((hSquareInt hWd).add (integrable_sum_component_sq hFd)) (hSquareInt hfd)
  have hSplit2 := integral_add (hSquareInt hWd) (integrable_sum_component_sq hFd)
  simp only [Pi.add_apply] at hSplit1 hSplit2
  have hData : (∫ p, (Wd p)^2+(∑ j, (Fd p j)^2)+(fd p)^2) ≤
      (1+D)*(∫ p, ∑ j, (H p j)^2) := by
    rw [hSplit1,hSplit2]
    calc
      _ = (∫ p, (Wd p)^2)+((∫ p, ∑ j, (Fd p j)^2)+(∫ p, (fd p)^2)) := by ring
      _ ≤ (∫ p, ∑ j, (H p j)^2)+D*(∫ p, ∑ j, (H p j)^2) := add_le_add hWBound hForce
      _ = _ := by ring
  have hFinal := hEst.trans (mul_le_mul_of_nonneg_left hData hC0.le)
  simpa only [mul_assoc] using hFinal

end Yau.LeafProofs.L16Aux
