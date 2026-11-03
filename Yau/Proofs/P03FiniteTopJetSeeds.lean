import Yau.Proofs.P03CompactTopJetSeeds
import Yau.LeafProofs.L14CompactDbar

open scoped Manifold Topology ContDiff
open Filter MeasureTheory Bundle

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar Yau.LeafProofs.L14Aux

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem top_coefficients_sum {ι : Type*} [Fintype ι]
    (s : ι → NQForm E 0) (a : M.Carrier) (z : ComplexVector n) :
    coefficients (r := r) E (∑ i, s i) a z Fin.elim0 =
      ∑ i, coefficients (r := r) E (s i) a z Fin.elim0 := by
  ext α : 1
  rw [coefficients_sum]
  exact (map_sum (EuclideanSpace.proj α) _ _).symm

theorem form_eventually_zero_of_notMem_support {q : ℕ} (f : NQForm E q)
    {a : M.Carrier} (ha : a ∉ closure {x | f x ≠ (0 : NQForm E q) x}) :
    ∀ᶠ x in 𝓝 a, f x = (0 : NQForm E q) x := by
  filter_upwards [isClosed_closure.isOpen_compl.mem_nhds ha] with x hx
  by_contra hn
  exact hx (subset_closure hn)

theorem notMem_formSupport_of_eventually_zero {q : ℕ} (f : NQForm E q)
    {a : M.Carrier} (ha : ∀ᶠ x in 𝓝 a, f x = (0 : NQForm E q) x) :
    a ∉ closure {x | f x ≠ (0 : NQForm E q) x} := by
  intro hc
  obtain ⟨x, hx0, hxn⟩ := mem_closure_iff_nhds.mp hc {x | f x = (0 : NQForm E q) x} ha
  exact hxn hx0

/-- One finite smooth seed has all prescribed polynomial germs. Its one
actual Dolbeault source is closed and supported in one compact set disjoint
from every prescribed pole. -/
theorem exists_finite_top_jet_source (hE : Holomorphic (r := r) E)
    (pts : Finset M.Carrier) (Pj : M.Carrier → Fin r → MvPolynomial (Fin n) ℂ) :
    ∃ (s : NQForm E 0) (f : NQForm E 1),
      SmoothForm (r := r) E s ∧ SmoothForm (r := r) E f ∧
      IsDbarOf (r := r) E s f ∧ WeakDbar (r := r) E s f ∧ WeaklyClosed (r := r) E f ∧
      IsCompact (closure {x | s x ≠ (0 : NQForm E 0) x}) ∧
      IsCompact (closure {x | f x ≠ (0 : NQForm E 1) x}) ∧
      ∀ p ∈ pts,
        ((fun z => coefficients (r := r) E s p z Fin.elim0) =ᶠ[𝓝 (chartPt p p)]
          (fun z => WithLp.toLp 2
            (fun α => MvPolynomial.eval (fun i => z i - chartPt p p i) (Pj p α)))) ∧
        p ∉ closure {x | f x ≠ (0 : NQForm E 1) x} := by
  classical
  let U : pts → Set M.Carrier := fun i => {x | x ∈ pts ∧ x ≠ i.1}ᶜ
  have hU (i : pts) : U i ∈ 𝓝 i.1 := by
    have hfin : Set.Finite {x : M.Carrier | x ∈ pts ∧ x ≠ i.1} :=
      pts.finite_toSet.subset fun _ hx => hx.1
    exact hfin.isClosed.isOpen_compl.mem_nhds (by simp [U])
  choose ss fs hs hf hD hw hclosed hsc hssupport hfc hfsupport hsgerm hfgerm using
    fun i : pts => exists_compact_top_jet_seed E hE i.1 (Pj i.1) (hU i)
  let s := ∑ i : pts, ss i
  let f := ∑ i : pts, fs i
  have hsmooth : SmoothForm (r := r) E s := smoothForm_sum E ss hs
  have hfsmooth : SmoothForm (r := r) E f := smoothForm_sum E fs hf
  have hDsum : IsDbarOf (r := r) E s f := smoothDbarRepresents_sum E ss fs hs hD
  have hweak := weakDbar_of_smooth_isDbarOf E s f hsmooth hfsmooth hDsum
  refine ⟨s, f, hsmooth, hfsmooth, hDsum, hweak,
    weakDbar_weaklyClosed_top E s f hweak,
    compact_formSupport_sum E ss hsc, compact_formSupport_sum E fs hfc, ?_⟩
  intro p hp
  let j : pts := ⟨p, hp⟩
  have hcp : Tendsto (chartInv p) (𝓝 (chartPt p p)) (𝓝 p) := by
    change Tendsto (extChartAt (ComplexModel n) p).symm
      (𝓝 ((extChartAt (ComplexModel n) p) p)) (𝓝 p)
    simpa only [extChartAt_to_inv] using
      (continuousAt_extChartAt_symm (I := ComplexModel n) p).tendsto
  have hother (i : pts) (hi : i ≠ j) : p ∈ {x | x ∈ pts ∧ x ≠ i.1} := by
    refine ⟨hp, ?_⟩
    intro hpi
    exact hi (Subtype.ext hpi.symm)
  have hlocal (i : pts) :
      (fun z => coefficients (r := r) E (ss i) p z Fin.elim0) =ᶠ[𝓝 (chartPt p p)]
        (if i = j then (fun z => WithLp.toLp 2
          (fun α => MvPolynomial.eval (fun l => z l - chartPt p p l) (Pj p α))) else 0) := by
    by_cases hi : i = j
    · subst i
      simpa only [ite_true] using hsgerm j
    · rw [if_neg hi]
      have hout : p ∉ closure {x | ss i x ≠ (0 : NQForm E 0) x} :=
        fun h => hssupport i h (hother i hi)
      have hz := hcp.eventually (form_eventually_zero_of_notMem_support E (ss i) hout)
      filter_upwards [hz] with z hz
      unfold coefficients
      rw [hz]
      simp only [nqForm_zero_apply, AlternatingMap.zero_apply, map_zero, Pi.zero_apply]
  have hall := Filter.eventually_all.mpr hlocal
  have hg : (fun z => coefficients (r := r) E s p z Fin.elim0) =ᶠ[𝓝 (chartPt p p)]
      (fun z => WithLp.toLp 2
        (fun α => MvPolynomial.eval (fun i => z i - chartPt p p i) (Pj p α))) := by
    filter_upwards [hall] with z hz
    rw [show coefficients (r := r) E s p z Fin.elim0 =
      ∑ i : pts, coefficients (r := r) E (ss i) p z Fin.elim0 from top_coefficients_sum E ss p z]
    calc
      _ = ∑ i : pts, if i = j then WithLp.toLp 2
          (fun α => MvPolynomial.eval (fun l => z l - chartPt p p l) (Pj p α)) else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        simpa only [ite_apply, Pi.zero_apply] using hz i
      _ = _ := by simp
  have hzero (i : pts) : ∀ᶠ x in 𝓝 p, fs i x = (0 : NQForm E 1) x := by
    by_cases hi : i = j
    · subst i
      exact hfgerm j
    · apply form_eventually_zero_of_notMem_support E (fs i)
      exact fun h => hfsupport i h (hother i hi)
  have hzeroall := Filter.eventually_all.mpr hzero
  have hfzero : ∀ᶠ x in 𝓝 p, f x = (0 : NQForm E 1) x := by
    filter_upwards [hzeroall] with x hx
    apply Subtype.ext
    change ((∑ i : pts, fs i) x).1 = ((0 : NQForm E 1) x).1
    rw [nqForm_sum_value]
    simp only [hx, nqForm_zero_apply, Finset.sum_const_zero]
  exact ⟨hg, notMem_formSupport_of_eventually_zero E f hfzero⟩

end Yau.NodeProofs.P03Aux
