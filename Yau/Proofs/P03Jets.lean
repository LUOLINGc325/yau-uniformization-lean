import Yau.Blueprint.Analytic

open scoped Manifold Topology ContDiff
open Filter

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem jetAgreeFn_mono {f : M.Carrier → ℂ} {p : M.Carrier}
    {P : MvPolynomial (Fin n) ℂ} {k l : ℕ}
    (h : JetAgreeFn f p P k) (hl : l ≤ k) : JetAgreeFn f p P l := by
  intro j hj
  exact h j (hj.trans hl)

theorem jetAgreeField_mono {V : VectorField M} {p : M.Carrier}
    {P : Fin n → MvPolynomial (Fin n) ℂ} {k l : ℕ}
    (h : JetAgreeField V p P k) (hl : l ≤ k) : JetAgreeField V p P l := by
  intro j hj
  exact h j (hj.trans hl)

/-- Equality of the local germs preserves the full native scalar jet. -/
theorem jetAgreeFn_congr_germ {f g : M.Carrier → ℂ} {p : M.Carrier}
    {P : MvPolynomial (Fin n) ℂ} {k : ℕ}
    (hfg : inChart p f =ᶠ[𝓝 (chartPt p p)] inChart p g)
    (hf : JetAgreeFn f p P k) : JetAgreeFn g p P k := by
  intro j hj
  have he := hfg.sub (Filter.EventuallyEq.rfl (f :=
    fun z : ComplexVector n => MvPolynomial.eval (fun i => z i - chartPt p p i) P))
  have hd := (he.iteratedFDeriv ℂ j).self_of_nhds
  exact hd.symm.trans (hf j hj)

/-- Equality of the local field-coordinate germs preserves the full native jet. -/
theorem jetAgreeField_congr_germ {V W : VectorField M} {p : M.Carrier}
    {P : Fin n → MvPolynomial (Fin n) ℂ} {k : ℕ}
    (hVW : fieldCoords V p =ᶠ[𝓝 (chartPt p p)] fieldCoords W p)
    (hV : JetAgreeField V p P k) : JetAgreeField W p P k := by
  intro j hj
  have he := hVW.sub (Filter.EventuallyEq.rfl (f := fun z : ComplexVector n =>
    WithLp.toLp 2 (fun i => MvPolynomial.eval (fun l => z l - chartPt p p l) (P i))))
  have hd := (he.iteratedFDeriv ℂ j).self_of_nhds
  exact hd.symm.trans (hV j hj)

/-- A local polynomial germ gives precisely the requested scalar jet, at
every order, with the centering used by the original contract. -/
theorem jetAgreeFn_of_polynomial_germ {f : M.Carrier → ℂ} {p : M.Carrier}
    {P : MvPolynomial (Fin n) ℂ}
    (hf : inChart p f =ᶠ[𝓝 (chartPt p p)]
      (fun z => MvPolynomial.eval (fun i => z i - chartPt p p i) P))
    (k : ℕ) : JetAgreeFn f p P k := by
  intro j hj
  have he : (fun z : ComplexVector n => inChart p f z -
      MvPolynomial.eval (fun i => z i - chartPt p p i) P) =ᶠ[𝓝 (chartPt p p)]
      (fun _ => (0 : ℂ)) := hf.mono fun z hz => sub_eq_zero.mpr hz
  simpa using (he.iteratedFDeriv ℂ j).self_of_nhds

theorem jetAgreeField_of_polynomial_germ {V : VectorField M} {p : M.Carrier}
    {P : Fin n → MvPolynomial (Fin n) ℂ}
    (hV : fieldCoords V p =ᶠ[𝓝 (chartPt p p)] (fun z => WithLp.toLp 2
      (fun i => MvPolynomial.eval (fun l => z l - chartPt p p l) (P i))))
    (k : ℕ) : JetAgreeField V p P k := by
  intro j hj
  have he : (fun z : ComplexVector n => fieldCoords V p z - WithLp.toLp 2
      (fun i => MvPolynomial.eval (fun l => z l - chartPt p p l) (P i)))
      =ᶠ[𝓝 (chartPt p p)] (fun _ => (0 : ComplexVector n)) :=
    hV.mono fun z hz => sub_eq_zero.mpr hz
  simpa using (he.iteratedFDeriv ℂ j).self_of_nhds

end Yau.NodeProofs.P03Aux
