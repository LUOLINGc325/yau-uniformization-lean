import Yau.Proofs.P03Cutoffs

open scoped Manifold Topology ContDiff
open Filter

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ} {M : ComplexManifold n}

/-- Before solving dbar, all finite scalar jet prescriptions already admit a
single smooth compactly supported seed with the correct germs. -/
theorem exists_finite_scalar_seed (pts : Finset M.Carrier)
    (Pj : M.Carrier → MvPolynomial (Fin n) ℂ) :
    ∃ f : M.Carrier → ℂ,
      (∀ a, ContDiffOn ℝ ∞ (inChart a f) (chartTarget a)) ∧
      HasCompactSupport f ∧
      ∀ p ∈ pts,
        (inChart p f =ᶠ[𝓝 (chartPt p p)]
          (fun z => MvPolynomial.eval (fun i => z i - chartPt p p i) (Pj p))) ∧
        ∀ k, JetAgreeFn f p (Pj p) k := by
  classical
  let U : pts → Set M.Carrier := fun i => {x | x ∈ pts ∧ x ≠ i.1}ᶜ
  have hU (i : pts) : U i ∈ 𝓝 i.1 := by
    have hfin : Set.Finite {x : M.Carrier | x ∈ pts ∧ x ≠ i.1} :=
      pts.finite_toSet.subset fun x hx => hx.1
    exact hfin.isClosed.isOpen_compl.mem_nhds (by simp [U])
  choose fs hsmooth hcompact hsupp hgerm hjets using
    fun i : pts => exists_scalar_seed i.1 (Pj i.1) (hU i)
  let f : M.Carrier → ℂ := fun x => ∑ i : pts, fs i x
  have hfsmooth : ∀ a, ContDiffOn ℝ ∞ (inChart a f) (chartTarget a) := by
    intro a
    change ContDiffOn ℝ ∞ (fun z => ∑ i : pts, fs i (chartInv a z)) (chartTarget a)
    exact ContDiffOn.sum (s := Finset.univ) (fun i _ => hsmooth i a)
  have hfcompact : HasCompactSupport f := by
    have heq : f = ∑ i : pts, fs i := by
      funext x
      simp only [f, Finset.sum_apply]
    rw [heq]
    exact HasCompactSupport.finset_sum (s := Finset.univ) (f := fs) (fun i _ => hcompact i)
  refine ⟨f, hfsmooth, hfcompact, ?_⟩
  intro p hp
  let j : pts := ⟨p, hp⟩
  have hlocal (i : pts) :
      inChart p (fs i) =ᶠ[𝓝 (chartPt p p)]
        (if i = j then
          (fun z => MvPolynomial.eval (fun l => z l - chartPt p p l) (Pj p))
         else 0) := by
    by_cases hij : i = j
    · subst i
      simpa [j] using hgerm j
    · rw [if_neg hij]
      have hout : p ∉ tsupport (fs i) := by
        intro hmem
        have hnot := hsupp i hmem
        apply hnot
        refine ⟨hp, ?_⟩
        intro hpi
        exact hij (Subtype.ext hpi.symm)
      have heq : fs i =ᶠ[𝓝 p] 0 := notMem_tsupport_iff_eventuallyEq.mp hout
      have hcp : Tendsto (chartInv p) (𝓝 (chartPt p p)) (𝓝 p) := by
        change Tendsto (extChartAt (ComplexModel n) p).symm
          (𝓝 ((extChartAt (ComplexModel n) p) p)) (𝓝 p)
        simpa only [extChartAt_to_inv] using
          (continuousAt_extChartAt_symm (I := ComplexModel n) p).tendsto
      exact heq.comp_tendsto hcp
  have hsum := Filter.eventually_all.mpr hlocal
  have hfg : inChart p f =ᶠ[𝓝 (chartPt p p)]
      (fun z => MvPolynomial.eval (fun l => z l - chartPt p p l) (Pj p)) := by
    filter_upwards [hsum] with z hz
    simp only [inChart, f]
    calc
      (∑ i : pts, fs i (chartInv p z)) =
          ∑ i : pts, if i = j then
            MvPolynomial.eval (fun l => z l - chartPt p p l) (Pj p) else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        simpa only [inChart, Pi.zero_apply, ite_apply] using hz i
      _ = _ := by simp
  exact ⟨hfg, jetAgreeFn_of_polynomial_germ hfg⟩

end Yau.NodeProofs.P03Aux
