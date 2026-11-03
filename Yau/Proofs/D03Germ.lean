import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Germ
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

/-! The ring of convergent scalar holomorphic germs at the origin used by D03.
Its equivalence relation is equality on an actual neighbourhood of zero. -/

noncomputable section

open Filter Topology

namespace Yau.Proofs.D03Aux

/-- Analytic germs form a subring of the ring of all neighbourhood germs. -/
def analyticGermRing : Subring (Germ (𝓝 (0 : ℂ)) ℂ) where
  carrier := {g | ∃ f : ℂ → ℂ, AnalyticAt ℂ f 0 ∧ Germ.ofFun f = g}
  zero_mem' := ⟨0, analyticAt_const, rfl⟩
  one_mem' := ⟨1, analyticAt_const, rfl⟩
  add_mem' := by
    rintro a b ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, hf.add hg, rfl⟩
  neg_mem' := by
    rintro a ⟨f, hf, rfl⟩
    exact ⟨-f, hf.neg, rfl⟩
  mul_mem' := by
    rintro a b ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, hf.mul hg, rfl⟩

/-- Actual convergent analytic germs, rather than formal power series. -/
abbrev AnalyticGerm := analyticGermRing

def ofAnalytic (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) : AnalyticGerm :=
  ⟨Germ.ofFun f, f, hf, rfl⟩

@[simp]
theorem ofAnalytic_eq_iff {f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    ofAnalytic f hf = ofAnalytic g hg ↔ f =ᶠ[𝓝 0] g := by
  exact Subtype.ext_iff.trans Germ.coe_eq

@[simp]
theorem ofAnalytic_zero : ofAnalytic 0 analyticAt_const = 0 := rfl

@[simp]
theorem ofAnalytic_one : ofAnalytic 1 analyticAt_const = 1 := rfl

@[simp]
theorem ofAnalytic_add (f g : ℂ → ℂ) (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) :
    ofAnalytic (f + g) (hf.add hg) = ofAnalytic f hf + ofAnalytic g hg := rfl

@[simp]
theorem ofAnalytic_neg (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) :
    ofAnalytic (-f) hf.neg = -ofAnalytic f hf := rfl

@[simp]
theorem ofAnalytic_mul (f g : ℂ → ℂ) (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) :
    ofAnalytic (f * g) (hf.mul hg) = ofAnalytic f hf * ofAnalytic g hg := rfl

@[simp]
theorem ofAnalytic_pow (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    ofAnalytic (f ^ n) (hf.pow n) = ofAnalytic f hf ^ n := rfl

/-- Constants give the canonical complex algebra structure. -/
def constantGerm : ℂ →+* AnalyticGerm where
  toFun a := ofAnalytic (fun _ => a) analyticAt_const
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

instance : Algebra ℂ AnalyticGerm := constantGerm.toAlgebra

/-- Evaluation uses the centre of the neighbourhood filter. -/
def germValue : AnalyticGerm →+* ℂ :=
  Germ.valueRingHom.comp analyticGermRing.subtype

@[simp]
theorem germValue_ofAnalytic (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) :
    germValue (ofAnalytic f hf) = f 0 := rfl

@[simp]
theorem germValue_constant (a : ℂ) : germValue (constantGerm a) = a := rfl

/-- A representative is chosen together with its actual analyticity proof. -/
def analyticRepresentative (g : AnalyticGerm) : ℂ → ℂ := g.property.choose

theorem analyticRepresentative_analytic (g : AnalyticGerm) :
    AnalyticAt ℂ (analyticRepresentative g) 0 := g.property.choose_spec.1

@[simp]
theorem ofAnalytic_representative (g : AnalyticGerm) :
    ofAnalytic (analyticRepresentative g) (analyticRepresentative_analytic g) = g :=
  Subtype.ext g.property.choose_spec.2

@[simp]
theorem germValue_representative (g : AnalyticGerm) :
    analyticRepresentative g 0 = germValue g := by
  exact congrArg germValue (ofAnalytic_representative g)

/-- Invertibility is exactly nonvanishing at the origin. -/
theorem isUnit_iff_germValue_ne_zero (g : AnalyticGerm) :
    IsUnit g ↔ germValue g ≠ 0 := by
  constructor
  · intro h
    exact (h.map germValue).ne_zero
  · intro h
    let f := analyticRepresentative g
    have hf : AnalyticAt ℂ f 0 := analyticRepresentative_analytic g
    have hf0 : f 0 ≠ 0 := by simpa [f] using h
    let v : AnalyticGerm := ofAnalytic (fun z => (f z)⁻¹) (hf.inv hf0)
    have hv' : ofAnalytic f hf * v = 1 := by
      apply Subtype.ext
      change Germ.ofFun (fun z => f z * (f z)⁻¹) = Germ.ofFun (fun _ => 1)
      apply Germ.coe_eq.mpr
      filter_upwards [hf.continuousAt.eventually_ne hf0] with z hz
      exact mul_inv_cancel₀ hz
    have hv : g * v = 1 := by
      simpa only [f, ofAnalytic_representative] using hv'
    exact isUnit_iff_exists_inv.mpr ⟨v, hv⟩

instance : IsLocalRing AnalyticGerm :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun g => by
    by_cases h : germValue g = 0
    · right
      apply (isUnit_iff_germValue_ne_zero _).mpr
      simp [map_sub, h]
    · exact Or.inl ((isUnit_iff_germValue_ne_zero g).mpr h)

/-- The maximal ideal consists of germs vanishing at zero. -/
def germMaximalIdeal : Ideal AnalyticGerm := RingHom.ker germValue

theorem germMaximalIdeal_ne_top : germMaximalIdeal ≠ ⊤ := by
  intro h
  have h1 : (1 : AnalyticGerm) ∈ germMaximalIdeal := h ▸ Submodule.mem_top
  have : (1 : ℂ) = 0 := by simpa [germMaximalIdeal] using h1
  exact one_ne_zero this

/-- The genuine local coordinate germ. -/
def zGerm : AnalyticGerm := ofAnalytic id analyticAt_id

@[simp]
theorem germValue_zGerm : germValue zGerm = 0 := rfl

/-- A nonzero convergent germ factors into a power of the coordinate and a unit. -/
theorem exists_pow_mul_unit (g : AnalyticGerm) (hg : g ≠ 0) :
    ∃ (d : ℕ) (u : AnalyticGerm), IsUnit u ∧ g = zGerm ^ d * u := by
  let f := analyticRepresentative g
  have hf : AnalyticAt ℂ f 0 := analyticRepresentative_analytic g
  have hfne : ¬ ∀ᶠ z in 𝓝 0, f z = 0 := by
    intro h
    apply hg
    rw [← ofAnalytic_representative g]
    exact (ofAnalytic_eq_iff (analyticRepresentative_analytic g) (analyticAt_const : AnalyticAt ℂ (0 : ℂ → ℂ) 0)).mpr h
  obtain ⟨d, v, hv, hv0, hfv⟩ := hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hfne
  refine ⟨d, ofAnalytic v hv, (isUnit_iff_germValue_ne_zero _).mpr hv0, ?_⟩
  calc
    g = ofAnalytic f hf := (ofAnalytic_representative g).symm
    _ = ofAnalytic (fun z => z ^ d * v z) ((analyticAt_id.pow d).mul hv) := by
      apply (ofAnalytic_eq_iff _ _).mpr
      filter_upwards [hfv] with z hz
      simpa only [sub_zero, smul_eq_mul] using hz
    _ = zGerm ^ d * ofAnalytic v hv := rfl

end Yau.Proofs.D03Aux
