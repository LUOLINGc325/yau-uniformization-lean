import spec.CHAIN.LeafCandidates

/-! Real linear normalization of a complex structure, without an existing
complex atlas or a normed complex scalar action for that structure. -/

open scoped ContDiff
noncomputable section

namespace Yau.LeafProofs.L21Aux

/-- A separate carrier lets the new complex action coexist with the standard
complex action on the target. Its real norm and real scalar action are unchanged. -/
def Twisted (n : ℕ) := Yau.ComplexVector n

instance (n : ℕ) : NormedAddCommGroup (Twisted n) :=
  inferInstanceAs (NormedAddCommGroup (Yau.ComplexVector n))

instance (n : ℕ) : NormedSpace ℝ (Twisted n) :=
  inferInstanceAs (NormedSpace ℝ (Yau.ComplexVector n))

instance (n : ℕ) : FiniteDimensional ℝ (Twisted n) :=
  inferInstanceAs (FiniteDimensional ℝ (Yau.ComplexVector n))

def twistEquiv (n : ℕ) : Yau.ComplexVector n ≃ₗ[ℝ] Twisted n :=
  LinearEquiv.refl ℝ (Yau.ComplexVector n)

/-- Every real complex structure on the standard real space is conjugate to
multiplication by `I`. No compatibility of its original norm with the new
complex action is needed. -/
theorem exists_linear_normalization (n : ℕ)
    (L : Yau.ComplexVector n →L[ℝ] Yau.ComplexVector n)
    (hL : ∀ v, L (L v) = -v) :
    ∃ S : Yau.ComplexVector n ≃L[ℝ] Yau.ComplexVector n,
      ∀ v, S (L v) = Complex.I • S v := by
  let L' : Module.End ℝ (Twisted n) := L.toLinearMap
  have hL' : L' * L' = -1 := by
    ext v
    exact hL v
  let a : ℂ →ₐ[ℝ] Module.End ℝ (Twisted n) := Complex.liftAux L' hL'
  letI : Module ℂ (Twisted n) := Module.compHom (Twisted n) a.toRingHom
  letI : IsScalarTower ℝ ℂ (Twisted n) := ⟨by
    intro r c v
    change a (r • c) v = r • a c v
    rw [map_smul]
    rfl⟩
  letI : FiniteDimensional ℂ (Twisted n) :=
    Module.Finite.of_restrictScalars_finite ℝ ℂ (Twisted n)
  have hdim : Module.finrank ℂ (Twisted n) = Module.finrank ℂ (Yau.ComplexVector n) := by
    have ht := Module.finrank_mul_finrank ℝ ℂ (Twisted n)
    have hs := Module.finrank_mul_finrank ℝ ℂ (Yau.ComplexVector n)
    have he := (twistEquiv n).finrank_eq
    rw [Complex.finrank_real_complex] at ht hs
    omega
  let e : Twisted n ≃ₗ[ℂ] Yau.ComplexVector n :=
    LinearEquiv.ofFinrankEq (Twisted n) (Yau.ComplexVector n) hdim
  let S := ((twistEquiv n).trans (e.restrictScalars ℝ)).toContinuousLinearEquiv
  refine ⟨S, fun v => ?_⟩
  change e (L v) = Complex.I • e ((twistEquiv n) v)
  rw [← e.map_smul]
  congr 1
  change L v = a Complex.I v
  rw [Complex.liftAux_apply_I]
  rfl

/-- The original chart conclusion in complex dimension zero. -/
theorem dimension_zero_chart
    (O : Set (Yau.ComplexVector 0))
    (J : Yau.ComplexVector 0 → Yau.ComplexVector 0 →L[ℝ] Yau.ComplexVector 0)
    (p : Yau.ComplexVector 0) (hp : p ∈ O) :
    ∃ e : OpenPartialHomeomorph (Yau.ComplexVector 0) (Yau.ComplexVector 0),
      p ∈ e.source ∧ e.source ⊆ O ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ x ∈ e.source, ∀ v,
        fderiv ℝ e x (J x v) = Complex.I • fderiv ℝ e x v := by
  refine ⟨OpenPartialHomeomorph.refl _, by simp, ?_, contDiff_id.contDiffOn,
    contDiff_id.contDiffOn, ?_⟩
  · intro x _
    simpa only [Subsingleton.elim x p] using hp
  · intro x _ v
    exact Subsingleton.elim _ _

end Yau.LeafProofs.L21Aux
