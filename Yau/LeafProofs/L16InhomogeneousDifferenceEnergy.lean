import Yau.LeafProofs.L16UniformDifferenceEnergy

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

theorem exists_uniform_inhomogeneous_difference_energy_constant (n : ℕ) (lam upper C M : ℝ)
    (hlam : 0 < lam) (hC : 0 ≤ C) (hM : 0 ≤ M) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (Q : Set (Point n)) (a : Point n → Mat n) (c : Point n → Yau.RIdx n → ℝ)
        (θ w : Point n → ℝ) (H P : Point n → Yau.RIdx n → ℝ) (R f : Point n → ℝ) (F J : Point n → Yau.RIdx n → ℝ)
        (K : Yau.RIdx n → Point n → Yau.RIdx n → ℝ),
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
      (∀ j, MemLp (fun p => F p j) 2 volume) → MemLp f 2 volume →
      (∀ j k, MemLp (fun p => K j p k) 2 volume) → (∀ k, MemLp (fun p => J p k) 2 volume) →
      (∀ j, HasCompactSupport (fun p => F p j)) → HasCompactSupport f →
      (∀ j k, HasCompactSupport (fun p => K j p k)) → (∀ k, HasCompactSupport (fun p => J p k)) →
      (∀ j, WeakGradient Set.univ Set.univ (fun p => F p j) (K j)) →
      WeakGradient Set.univ Set.univ f J →
      (∀ p ∈ Q, ∀ j, P p j = energyFlux a H p j+F p j) →
      (∀ p ∈ Q, R p = (∑ j, c p j*H p j)+f p) →
      ∀ (i : Yau.RIdx n) (h : ℝ), h ≠ 0 →
      (∀ p ∈ tsupport θ, spatialTranslatePoint (h • Yau.realVec i) p ∈ Q) →
      (∫ p, (θ p)^2*(∑ j, (spatialDifferenceQuotient (fun q => H q j) (Yau.realVec i) h p)^2)) ≤
        B*((∫ p, ∑ j, (H p j)^2)+(∑ j, ∫ p, ∑ k, (K j p k)^2)+
          (∫ p, ∑ k, (J p k)^2)) := by
  obtain ⟨C0,hC0,hEstimate⟩ := exists_caccioppoli_constant n lam upper C C M hlam hC hC hM
  let N : ℝ := Fintype.card (Yau.RIdx n)
  let D : ℝ := (N^2+N)*C^2
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨C0*(3+2*D),by positivity,?_⟩
  intro Q a c θ w H P R f F J K hEll ha hc hAVal hCVal hADq hCDq hθ hθBound hθTime hθSpace
    hw hH hP hR hcw hcH hcP hcR hGrad hEq hF hf hK hJ hcF hcf hcK hcJ hGradF hGradf hFlux hSource i h hh hShift
  let e : Space n := Yau.realVec i
  let Qh : Set (Point n) := {p | p ∈ Q ∧ spatialTranslatePoint (h • e) p ∈ Q}
  let Wd : Point n → ℝ := spatialDifferenceQuotient w e h
  let Hd : Point n → Yau.RIdx n → ℝ := fun p j => spatialDifferenceQuotient (fun q => H q j) e h p
  let Pd : Point n → Yau.RIdx n → ℝ := fun p j => spatialDifferenceQuotient (fun q => P q j) e h p
  let Rd : Point n → ℝ := spatialDifferenceQuotient R e h
  let Fc : Point n → Yau.RIdx n → ℝ := energyFlux (spatialDifferenceQuotient a e h) H
  let fc : Point n → ℝ := fun p => ∑ j, spatialDifferenceQuotient (fun q => c q j) e h p*H p j
  let FD : Point n → Yau.RIdx n → ℝ := fun p j => spatialDifferenceQuotient (fun q => F q j) e h p
  let fD : Point n → ℝ := spatialDifferenceQuotient f e h
  let Fd : Point n → Yau.RIdx n → ℝ := fun p j => Fc p j+FD p j
  let fd : Point n → ℝ := fun p => fc p+fD p
  have hWd : MemLp Wd 2 volume := memLp_spatialDifferenceQuotient hw e h
  have hHd (j : Yau.RIdx n) : MemLp (fun p => Hd p j) 2 volume := memLp_spatialDifferenceQuotient (hH j) e h
  have hPd (j : Yau.RIdx n) : MemLp (fun p => Pd p j) 2 volume := memLp_spatialDifferenceQuotient (hP j) e h
  have hRd : MemLp Rd 2 volume := memLp_spatialDifferenceQuotient hR e h
  obtain ⟨hFc,hfc,hForce⟩ := spatialDifferenceQuotient_forcing_L2_bounds hC ha hc hH e h
    (hADq i h) (fun p j => hCDq j i h p)
  have hFD (j : Yau.RIdx n) : MemLp (fun p => FD p j) 2 volume := memLp_spatialDifferenceQuotient (hF j) e h
  have hfD : MemLp fD 2 volume := memLp_spatialDifferenceQuotient hf e h
  have hFd (j : Yau.RIdx n) : MemLp (fun p => Fd p j) 2 volume := by
    convert! (hFc j).add (hFD j) using 1
  have hfd : MemLp fd 2 volume := by convert! hfc.add hfD using 1
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
      Pd p j = energyFlux (spatialTranslate (h • e) a) Hd p j+Fd p j := by
    have hOld := spatialDifferenceQuotient_local_flux
      (P := fun p j => P p j-F p j)
      (fun q hq k => by rw [hFlux q hq k]; ring) e h
      (hθ.2.2 hp) (hShift p hp) j
    have hSub : spatialDifferenceQuotient (fun q => P q j-F q j) e h p = Pd p j-FD p j := by
      simp only [spatialDifferenceQuotient,Pd,FD,smul_eq_mul]
      ring
    rw [hSub] at hOld
    dsimp only [Fd,Fc]
    linarith
  have hLocalSource (p : Point n) (hp : p ∈ tsupport θ) :
      Rd p = (∑ j, spatialTranslate (h • e) c p j*Hd p j)+fd p := by
    have hOld := spatialDifferenceQuotient_local_source
      (R := fun p => R p-f p)
      (fun q hq => by rw [hSource q hq]; ring) e h
      (hθ.2.2 hp) (hShift p hp)
    have hSub : spatialDifferenceQuotient (fun q => R q-f q) e h p = Rd p-fD p := by
      simp only [spatialDifferenceQuotient,Rd,fD,smul_eq_mul]
      ring
    rw [hSub] at hOld
    dsimp only [fd,fc]
    linarith
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
  let EH : ℝ := ∫ p, ∑ j, (H p j)^2
  let EK : ℝ := ∑ j, ∫ p, ∑ k, (K j p k)^2
  let EJ : ℝ := ∫ p, ∑ k, (J p k)^2
  have hEH : 0 ≤ EH := integral_nonneg (fun p => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hEK : 0 ≤ EK := Finset.sum_nonneg (fun _ _ => integral_nonneg (fun p => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  have hEJ : 0 ≤ EJ := integral_nonneg (fun p => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hFDSingle (j : Yau.RIdx n) : (∫ p, (FD p j)^2) ≤ ∫ p, ∑ k, (K j p k)^2 := by
    have hBound := (weakGradient_spatialDifferenceQuotient_L2_bound (hF j) (hcF j)
      (hGradF j) i (hK j i) (hcK j i) hh).2
    refine hBound.trans (integral_mono (hSquareInt (hK j i)) (integrable_sum_component_sq (hK j)) ?_)
    intro p
    exact Finset.single_le_sum (s := Finset.univ) (f := fun k => (K j p k)^2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have hFDBound : (∫ p, ∑ j, (FD p j)^2) ≤ EK := by
    rw [integral_finsetSum Finset.univ (fun j _ => hSquareInt (hFD j))]
    exact Finset.sum_le_sum (fun j _ => hFDSingle j)
  have hfDBound : (∫ p, (fD p)^2) ≤ EJ := by
    have hBound := (weakGradient_spatialDifferenceQuotient_L2_bound hf hcf hGradf i (hJ i) (hcJ i) hh).2
    refine hBound.trans (integral_mono (hSquareInt (hJ i)) (integrable_sum_component_sq hJ) ?_)
    intro p
    exact Finset.single_le_sum (s := Finset.univ) (f := fun k => (J p k)^2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have hAddSq {x y : Point n → ℝ} (hx : MemLp x 2 volume) (hy : MemLp y 2 volume) :
      (∫ p, (x p+y p)^2) ≤ 2*((∫ p, (x p)^2)+(∫ p, (y p)^2)) := by
    have hxy : MemLp (fun p => x p+y p) 2 volume := by convert! hx.add hy using 1
    have hInt : Integrable (fun p => 2*((x p)^2+(y p)^2)) volume := by
      convert! ((hSquareInt hx).add (hSquareInt hy)).const_mul 2 using 1
    calc
      _ ≤ ∫ p, 2*((x p)^2+(y p)^2) := by
        apply integral_mono (hSquareInt hxy) hInt
        intro p
        nlinarith [sq_nonneg (x p-y p)]
      _ = _ := by rw [integral_const_mul,integral_add (hSquareInt hx) (hSquareInt hy)]
  have hFdBound : (∫ p, ∑ j, (Fd p j)^2) ≤
      2*((∫ p, ∑ j, (Fc p j)^2)+(∫ p, ∑ j, (FD p j)^2)) := by
    rw [integral_finsetSum Finset.univ (fun j _ => hSquareInt (hFd j)),
      integral_finsetSum Finset.univ (fun j _ => hSquareInt (hFc j)),
      integral_finsetSum Finset.univ (fun j _ => hSquareInt (hFD j))]
    calc
      _ ≤ ∑ j, 2*((∫ p, (Fc p j)^2)+(∫ p, (FD p j)^2)) :=
        Finset.sum_le_sum (fun j _ => hAddSq (hFc j) (hFD j))
      _ = _ := by rw [← Finset.mul_sum,Finset.sum_add_distrib]
  have hfdBound := hAddSq hfc hfD
  have hForceAll : (∫ p, ∑ j, (Fd p j)^2)+(∫ p, (fd p)^2) ≤
      2*D*EH+2*(EK+EJ) := by
    have hTotal := add_le_add hFdBound hfdBound
    dsimp only [D,N,EH] at *
    nlinarith
  have hSplit1 := integral_add ((hSquareInt hWd).add (integrable_sum_component_sq hFd)) (hSquareInt hfd)
  have hSplit2 := integral_add (hSquareInt hWd) (integrable_sum_component_sq hFd)
  simp only [Pi.add_apply] at hSplit1 hSplit2
  have hData : (∫ p, (Wd p)^2+(∑ j, (Fd p j)^2)+(fd p)^2) ≤
      (3+2*D)*(EH+EK+EJ) := by
    rw [hSplit1,hSplit2]
    have hBase : (∫ p, (Wd p)^2)+(∫ p, ∑ j, (Fd p j)^2)+(∫ p, (fd p)^2) ≤
        EH+2*D*EH+2*(EK+EJ) := by
      have hSum := add_le_add hWBound hForceAll
      dsimp only [EH] at *
      linarith
    refine hBase.trans ?_
    nlinarith [mul_nonneg hD hEK,mul_nonneg hD hEJ]
  have hFinal := hEst.trans (mul_le_mul_of_nonneg_left hData hC0.le)
  simpa only [EH,EK,EJ,mul_assoc] using hFinal

end Yau.LeafProofs.L16Aux
