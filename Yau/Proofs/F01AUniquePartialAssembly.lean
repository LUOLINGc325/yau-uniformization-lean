import Yau.Proofs.F01AInterfaces
import Yau.Proofs.F01ACompatibleSections
import Yau.Proofs.F01ControlledPotentialUniqueness
import Yau.Proofs.F01NativePotentialTupleCongruence

/-! Closed-slab restriction, uniqueness on overlaps, and the actual unique
partial potential solution on the supremum of the existence intervals. -/
noncomputable section
open Set
open scoped Matrix ComplexOrder ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Blueprint
variable {n : ℕ} {M : ComplexManifold n}

/-- The shared existential-constant slab is exactly an actual finite tuple. -/
theorem nativePotentialSlab_iff_exists_tuple {g : HermitianField M} {T : ℝ}
    {h : ℝ → HermitianField M} {U : M.Carrier → ℝ → ℝ} :
    NativePotentialSlab g T h U ↔ ∃ C, NativePotentialTuple g T C h U := by
  constructor
  · rintro ⟨hh0, hh, hU, hU0, C, hC, hdata⟩
    exact ⟨C, hC, hh0, hh, hU, hU0, hdata⟩
  · rintro ⟨C, hC, hh0, hh, hU, hU0, hdata⟩
    exact ⟨hh0, hh, hU, hU0, C, hC, hdata⟩

/-- Restrict an actual solution using the released finite-tuple API. -/
theorem nativePotentialSlab_restrict {g : HermitianField M} {T S : ℝ}
    {h : ℝ → HermitianField M} {U : M.Carrier → ℝ → ℝ}
    (hsol : NativePotentialSlab g T h U) (hST : S ≤ T) :
    NativePotentialSlab g S h U := by
  obtain ⟨C, hTuple⟩ := nativePotentialSlab_iff_exists_tuple.mp hsol
  exact nativePotentialSlab_iff_exists_tuple.mpr ⟨C, hTuple.restrict hST⟩

/-- Agreement on the actual slab preserves all solution clauses. -/
theorem nativePotentialSlab_congr {g : HermitianField M} {T : ℝ} (hT : 0 ≤ T)
    {h k : ℝ → HermitianField M} {U V : M.Carrier → ℝ → ℝ}
    (hsol : NativePotentialSlab g T h U)
    (hhk : ∀ t ∈ Icc 0 T, k t = h t)
    (hUV : ∀ x t, t ∈ Icc 0 T → V x t = U x t) :
    NativePotentialSlab g T k V := by
  obtain ⟨C, hTuple⟩ := nativePotentialSlab_iff_exists_tuple.mp hsol
  exact nativePotentialSlab_iff_exists_tuple.mpr
    ⟨C, hTuple.congr hT (fun t ht => (hhk t ht).symm)
      (fun x t ht => (hUV x t ht).symm)⟩

/-- The previously uncompiled tuple-uniqueness draft, proved by the actual
nonlinear uniqueness theorem on the common closed interval. -/
theorem controlled_native_tuples_agree
    (X : KahlerManifold n) (o : Pt X) (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    {L : ℝ} (ho : u o < L)
    (h k : ℝ → HermitianField (sublevelManifold X.manifold u hu.1 o L ho))
    (U V : (sublevelManifold X.manifold u hu.1 o L ho).Carrier → ℝ → ℝ)
    {T S C D : ℝ} (hT : 0 < T) (hS : 0 < S)
    (hTuple : NativePotentialTuple (approximatingMetric X.manifold X.metric.form u hu.1 o L ho) T C h U)
    (kTuple : NativePotentialTuple (approximatingMetric X.manifold X.metric.form u hu.1 o L ho) S D k V) :
    (∀ x t, t ∈ Icc 0 (min T S) → U x t = V x t) ∧
      ∀ t ∈ Icc 0 (min T S), h t = k t := by
  obtain ⟨hC, _, _, hU, hU0, hDataU⟩ := hTuple.restrict (min_le_left T S)
  obtain ⟨hD, _, _, hV, hV0, hDataV⟩ := kTuple.restrict (min_le_right T S)
  exact controlled_potential_solutions_unique X o u hu ho h k U V (min T S) C D
    (lt_min hT hS) hC hD hU hV hU0 hV0 hDataU hDataV

/-- The existing controlled uniqueness theorem applies to distinct horizons
by restricting both solutions to their common closed interval. -/
theorem controlled_native_slabs_overlap_unique (X : KahlerManifold n) (o : Pt X)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u) {L : ℝ} (ho : u o < L) :
    let N := sublevelManifold X.manifold u hu.1 o L ho
    let α := approximatingMetric X.manifold X.metric.form u hu.1 o L ho
    ∀ {T S : ℝ} {h k : ℝ → HermitianField N} {U V : N.Carrier → ℝ → ℝ},
      0 < T → 0 < S → NativePotentialSlab α T h U → NativePotentialSlab α S k V →
      (∀ x t, t ∈ Icc 0 (min T S) → U x t = V x t) ∧
        ∀ t ∈ Icc 0 (min T S), h t = k t := by
  dsimp only
  intro T S h k U V hT hS hsol hsol'
  obtain ⟨C, hTuple⟩ := nativePotentialSlab_iff_exists_tuple.mp hsol
  obtain ⟨C', kTuple⟩ := nativePotentialSlab_iff_exists_tuple.mp hsol'
  exact controlled_native_tuples_agree X o u hu ho h k U V hT hS hTuple kTuple

/-- Every genuine closed prefix of a partial solution is an actual slab. -/
theorem nativePartialPotential_prefix {g : HermitianField M} {Tstar S : ℝ}
    {h : ℝ → HermitianField M} {U : M.Carrier → ℝ → ℝ}
    (hpartial : NativePartialPotential g Tstar h U) (hS : 0 ≤ S) (hSstar : S < Tstar) :
    NativePotentialSlab g S h U := by
  obtain ⟨hh0, hh, hU, hU0, ⟨C, hC, hdata⟩, hpde⟩ := hpartial
  refine ⟨hh0, hh S hS hSstar, hU S hS hSstar, hU0, C, hC, ?_⟩
  intro x t ht
  have hxt := hdata x t ⟨ht.1, ht.2.trans_lt hSstar⟩
  exact ⟨hxt.1, hxt.2.1, hxt.2.2, hpde S hS hSstar x t ht⟩

/-- Any two actual partial solutions agree on their entire common half-open
interval; this includes the initial time and all spatial values at once. -/
theorem controlled_native_partials_unique (X : KahlerManifold n) (o : Pt X)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u) {L : ℝ} (ho : u o < L) :
    let N := sublevelManifold X.manifold u hu.1 o L ho
    let α := approximatingMetric X.manifold X.metric.form u hu.1 o L ho
    ∀ {Tstar : ℝ} {h k : ℝ → HermitianField N} {U V : N.Carrier → ℝ → ℝ},
      NativePartialPotential α Tstar h U → NativePartialPotential α Tstar k V →
      (∀ x t, t ∈ Ico 0 Tstar → U x t = V x t) ∧
        ∀ t ∈ Ico 0 Tstar, h t = k t := by
  dsimp only
  intro Tstar h k U V hpartial kpartial
  have heq (t : ℝ) (ht : t ∈ Ico 0 Tstar) :
      (∀ x, U x t = V x t) ∧ h t = k t := by
    let S := (t + Tstar) / 2
    have hS : 0 < S := by dsimp only [S]; linarith [ht.1, ht.2]
    have hSstar : S < Tstar := by dsimp only [S]; linarith [ht.2]
    have htS : t ∈ Icc 0 (min S S) := by
      rw [min_self]
      exact ⟨ht.1, by dsimp only [S]; linarith [ht.2]⟩
    have h := controlled_native_slabs_overlap_unique X o u hu ho hS hS
      (nativePartialPotential_prefix hpartial hS.le hSstar)
      (nativePartialPotential_prefix kpartial hS.le hSstar)
    exact ⟨fun x => h.1 x t htS, h.2 t htS⟩
  exact ⟨fun x t ht => (heq t ht).1 x, fun t ht => (heq t ht).2⟩

/-- All existence times through a prescribed horizon. -/
def controlledExistenceTimes (X : KahlerManifold n) (o : Pt X)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u) {L : ℝ} (ho : u o < L)
    (H : ℝ) : Set ℝ :=
  {T | 0 < T ∧ T ≤ H ∧
    ∃ (h : ℝ → HermitianField (sublevelManifold X.manifold u hu.1 o L ho))
      (U : (sublevelManifold X.manifold u hu.1 o L ho).Carrier → ℝ → ℝ),
      NativePotentialSlab
        (approximatingMetric X.manifold X.metric.form u hu.1 o L ho) T h U}

/-- A common a priori sandwich and overlap uniqueness produce an actual
partial solution at the positive supremum of all existence times. -/
theorem controlled_unique_partial_at_sup (X : KahlerManifold n) (o : Pt X)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u) {L : ℝ} (ho : u o < L)
    (H : ℝ)
    (hne : (controlledExistenceTimes X o u hu ho H).Nonempty) :
    let N := sublevelManifold X.manifold u hu.1 o L ho
    let α := approximatingMetric X.manifold X.metric.form u hu.1 o L ho
    (∃ C : ℝ, 1 ≤ C ∧ ∀ T, 0 < T → T ≤ H → ∀ h U,
      NativePotentialSlab α T h U → ∀ x t, t ∈ Icc 0 T →
        (gMat (h t) x - ((C⁻¹ : ℝ) : ℂ) • gMat α x).PosSemidef ∧
        ((C : ℂ) • gMat α x - gMat (h t) x).PosSemidef) →
    ∃ (h : ℝ → HermitianField N) (U : N.Carrier → ℝ → ℝ),
      NativePartialPotential α (sSup (controlledExistenceTimes X o u hu ho H)) h U := by
  classical
  dsimp only
  intro hcommon
  let N := sublevelManifold X.manifold u hu.1 o L ho
  let α := approximatingMetric X.manifold X.metric.form u hu.1 o L ho
  let E := controlledExistenceTimes X o u hu ho H
  have hprops (a : E) : 0 < (a : ℝ) ∧ (a : ℝ) ≤ H ∧
      ∃ (h : ℝ → HermitianField N) (U : N.Carrier → ℝ → ℝ),
        NativePotentialSlab α a h U := a.property
  choose hs Us hsol using fun a : E => (hprops a).2.2
  let F : E → ℝ → (HermitianField N × (N.Carrier → ℝ)) :=
    fun a t => (hs a t, fun x => Us a x t)
  have hcompat : ∀ a b : E, ∀ t, t ∈ Icc 0 (min (a : ℝ) b) → F a t = F b t := by
    intro a b t ht
    have heq := controlled_native_slabs_overlap_unique X o u hu ho
      (hprops a).1 (hprops b).1 (hsol a) (hsol b)
    exact Prod.ext (heq.2 t ht) (funext fun x => heq.1 x t ht)
  obtain ⟨f, hf⟩ := compatible_sections_on_sup E hne F hcompat
  let h : ℝ → HermitianField N := fun t => (f t).1
  let U : N.Carrier → ℝ → ℝ := fun x t => (f t).2 x
  have hpref (S : ℝ) (hS : 0 ≤ S) (hSstar : S < sSup E) :
      NativePotentialSlab α S h U := by
    obtain ⟨a, ha, hfa⟩ := hf S hSstar
    apply nativePotentialSlab_congr hS
      (nativePotentialSlab_restrict (hsol a) ha.le)
    · intro t ht
      exact congrArg Prod.fst (hfa t ht)
    · intro x t ht
      exact congrArg (fun p : HermitianField N × (N.Carrier → ℝ) => p.2 x) (hfa t ht)
  have hstarpos : 0 < sSup E :=
    (positive_sup_of_existence_times E hne (fun T hT => hT.1) (fun T hT => hT.2.1)).1
  have hzero := hpref 0 le_rfl hstarpos
  rcases hcommon with ⟨C, hC, hbound⟩
  refine ⟨h, U, hzero.1, (fun S hS hSstar => (hpref S hS hSstar).2.1),
    (fun S hS hSstar => (hpref S hS hSstar).2.2.1), hzero.2.2.2.1,
    ⟨C, hC, ?_⟩, ?_⟩
  · intro x t ht
    obtain ⟨a, ha, hfa⟩ := hf t ht.2
    have ht' : t ∈ Icc 0 (a : ℝ) := ⟨ht.1, ha.le⟩
    have hha : h t = hs a t := congrArg Prod.fst (hfa t ⟨ht.1, le_rfl⟩)
    have hUa : (fun y => U y t) = fun y => Us a y t :=
      funext fun y => congrArg (fun p : HermitianField N × (N.Carrier → ℝ) => p.2 y)
        (hfa t ⟨ht.1, le_rfl⟩)
    obtain ⟨hlo, hhi⟩ := hbound a (hprops a).1 (hprops a).2.1
      (hs a) (Us a) (hsol a) x t ht'
    obtain ⟨Ca, hCa, hdata⟩ := (hsol a).2.2.2.2
    refine ⟨by simpa only [hha] using hlo, by simpa only [hha] using hhi, ?_⟩
    calc
      gMat (h t) x = gMat (hs a t) x := congrArg (fun q => gMat q x) hha
      _ = gMat α x - (t : ℂ) • ricci α x + levi (fun y => Us a y t) x :=
        (hdata x t ht').2.2.1
      _ = gMat α x - (t : ℂ) • ricci α x + levi (fun y => U y t) x :=
        congrArg (fun V : N.Carrier → ℝ =>
          gMat α x - (t : ℂ) • ricci α x + levi V x) hUa.symm
  · intro S hS hSstar x t ht
    obtain ⟨Cs, hCs, hdata⟩ := (hpref S hS hSstar).2.2.2.2
    exact (hdata x t ht).2.2.2

end Yau.NodeProofs.F01Aux
