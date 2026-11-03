import Yau.LeafProofs.L21WeakFirstOrderGain

/-! Localizing a genuine weak graph equation and obtaining its actual weak
first derivatives. The cutoff commutator is computed from the original rows. -/

open MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

def LocallyL2On (u : X n → ℂ) (O : Set (X n)) : Prop :=
  ∀ K : Set (X n), IsCompact K → K ⊆ O →
    MemLp u 2 ((Yau.lebesgueC n).restrict K)

def DbarWeakOn (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (u : X n → ℂ) (w : X n → Fin n → ℂ) (O : Set (X n)) : Prop :=
  ∀ i (ψ : X n → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ O →
    (∫ x, (ψ x : ℂ) * w x i ∂Yau.lebesgueC n) =
      ∫ x, u x * transposeRow A i ψ x ∂Yau.lebesgueC n

def cutoffDbarOutput (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (χ : X n → ℝ) (u : X n → ℂ) (w : X n → Fin n → ℂ) (x : X n) (i : Fin n) : ℂ :=
  (χ x : ℂ) * w x i + dbarA A i (fun y => (χ y : ℂ)) x * u x

theorem locallyIntegrableOn_of_locallyL2On {O : Set (X n)} (hO : IsOpen O)
    {u : X n → ℂ} (hu : LocallyL2On u O) :
    LocallyIntegrableOn u O (Yau.lebesgueC n) := by
  apply (locallyIntegrableOn_iff hO.isLocallyClosed).mpr
  intro K hKO hK
  letI : IsFiniteMeasure ((Yau.lebesgueC n).restrict K) := isFiniteMeasure_restrict.mpr (by
    rw [Yau.LeafProofs.lebesgueC_eq_volume]
    exact hK.measure_lt_top.ne)
  exact (hu K hK hKO).integrable (by norm_num)

theorem local_weak_first_order_gain {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    (hsmall : ∀ x ∈ O, Yau.LeafCandidates.matrixOpNorm (A x) ≤ 1 / 2)
    (u : X n → ℂ) (w : X n → Fin n → ℂ)
    (hu : LocallyL2On u O) (hw : ∀ i, LocallyL2On (fun x => w x i) O)
    (heq : DbarWeakOn A u w O)
    (χ : X n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ O) :
    ∃ (L : Set (X n)) (G : X n → Yau.RIdx n → ℂ), IsCompact L ∧ L ⊆ O ∧
      (∀ a, MemLp (fun x => G x a) 2 (Yau.lebesgueC n)) ∧
      (∀ a, tsupport (fun x => G x a) ⊆ L) ∧
      (∀ a, ComplexWeakDerivative (fun x => (χ x : ℂ) * u x)
        (fun x => G x a) (Yau.realVec a)) ∧
      (∑ a : Yau.RIdx n, ∫ x, ‖G x a‖ ^ 2 ∂Yau.lebesgueC n) ≤
        16 * ∑ i : Fin n, ∫ x, ‖cutoffDbarOutput A χ u w x i‖ ^ 2 ∂Yau.lebesgueC n := by
  let a := fun (i : Fin n) (_ : Unit) (r : Yau.RIdx n) x => dbarRealCoefficient A i r x
  let b := fun (_ : Fin n) (_ : Unit) (_ : X n) => (0 : ℂ)
  let u' := fun x (_ : Unit) => u x
  have hW (x : X n) (i : Fin n) :
      Yau.LeafProofs.L14Aux.localizedComplexSystemOutput Yau.realVec a χ u' w x i =
        cutoffDbarOutput A χ u w x i := by
    simp only [Yau.LeafProofs.L14Aux.localizedComplexSystemOutput, Fintype.sum_unique,
      cutoffDbarOutput, dbarA_eq_real_rows, fderiv_ofReal_apply
      (hχ.differentiable (by simp) x), Finset.sum_mul, a, u']
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    ring
  have hr : ∀ i (ψ : X n → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ O →
      (∫ x, (ψ x : ℂ) * w x i ∂Yau.lebesgueC n) =
        ∫ x, ∑ c : Unit, u' x c *
          Yau.LeafProofs.L14Aux.complexFormalAdjointTestRow Yau.realVec a b i c ψ x
          ∂Yau.lebesgueC n := by
    intro i ψ hψ hcψ hsψ
    simpa only [u', a, b, Yau.LeafProofs.L14Aux.complexFormalAdjointTestRow,
      Fintype.sum_unique, zero_mul, add_zero, transposeRow] using heq i ψ hψ hcψ hsψ
  have hweak : DbarWeakEquation A (fun x => (χ x : ℂ) * u x) (cutoffDbarOutput A χ u w) := by
    intro i ψ hψ hcψ
    have hh := Yau.LeafProofs.L14Aux.complex_firstOrder_rows_localize hO Yau.realVec a b
      (fun i _ r => dbarRealCoefficient_smoothOn hA i r) (fun _ _ => contDiffOn_const)
      u' w (fun _ => locallyIntegrableOn_of_locallyL2On hO hu)
      (fun i => locallyIntegrableOn_of_locallyL2On hO (hw i)) hr χ hχ hcχ hsχ i ψ hψ hcψ
    simpa only [hW, u', a, b, Yau.LeafProofs.L14Aux.complexFormalAdjointTestRow,
      Fintype.sum_unique, zero_mul, add_zero, transposeRow] using hh
  have hmu := Yau.LeafProofs.L14Aux.localizedComplexSystemInput_memLp χ hχ hcχ hsχ u hu
  have hmw (i : Fin n) : MemLp (fun x => cutoffDbarOutput A χ u w x i) 2 (Yau.lebesgueC n) := by
    simpa only [hW] using
      Yau.LeafProofs.L14Aux.localizedComplexSystemOutput_memLp hO Yau.realVec a
        (fun i _ r => dbarRealCoefficient_smoothOn hA i r)
        χ hχ hcχ hsχ u' w (fun _ => hu) hw i
  have hsw (i : Fin n) : tsupport (fun x => cutoffDbarOutput A χ u w x i) ⊆ tsupport χ := by
    simpa only [hW] using
      Yau.LeafProofs.L14Aux.localizedComplexSystemOutput_tsupport_subset Yau.realVec a χ u' w i
  exact compact_weak_first_order_gain hO hcχ hsχ hA hsmall
    (fun x => (χ x : ℂ) * u x) (cutoffDbarOutput A χ u w) hmu hmw
    (tsupport_mul_subset_left.trans (tsupport_comp_subset Complex.ofReal_zero χ)) hsw hweak

end Yau.LeafProofs.L21Aux
