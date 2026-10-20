-- scripts/census_fixture.lean -- the hypothesis census's self-test fixture
-- (doc 71 round G, T2; the reader's package 2, doc 02 §6).
--
-- NOT part of the library: `scripts/census_selftest.py` splices this file
-- after `scripts/census_probe.lean.template` (which imports `Sanctions` and
-- defines `#census`), runs `#census` over the three theorems below, and checks
-- that the probe and the builder report each construction as specified:
--
--   * an implicit scalar binder is counted among the top-level parameters;
--   * an inherited proof field is reported under its DECLARING structure
--     (`Base.hq`, not `Sub.hq`), once per schema;
--   * a field whose type is a project structure is expanded one level more
--     (`Cert.D : Base` yields `Base.q`, `Base.hq` at level 2);
--   * a `Prop` field or binder whose head is a project definition is unfolded
--     one level (`Pred a` becomes `0 < a`); a reducible alias unfolds one step;
--   * an opaque predicate is NOT unfolded and produces no `UNFOLD` record;
--   * a structure nested two levels deep produces `FRONTIER` records, not
--     silent omission;
--   * two binders that differ only in a bound-variable name are two display
--     keys (the interim display mode is not alpha-invariant; this pins the
--     limitation as behaviour rather than hiding it).
--
-- The namespace sits under `Sanctions` so `censusIsProject` treats it as
-- project code; nothing here is imported by the library.
namespace Sanctions.CensusFixture

structure Base where
  q : ℝ
  hq : 0 < q

structure Sub extends Base where
  hq1 : 1 ≤ q

def Pred (x : ℝ) : Prop := 0 < x

abbrev PredAlias (x : ℝ) : Prop := Pred x

opaque Opq : ℝ → Prop

structure Cert where
  D : Base
  hD : Pred D.q
  hAlias : PredAlias D.q

structure Deep where
  C : Cert

theorem thm1 {a : ℝ} (S : Sub) (C : Cert) (h : Pred a) (hop : Opq a)
    (hh : ∀ y ∈ Set.Icc (0 : ℝ) 1, y ≤ a) : a = a := by
  have _ := S; have _ := C; have _ := h; have _ := hop; have _ := hh
  rfl

theorem thm2 {b : ℝ} (S : Sub) (h : Pred b) : b = b := by
  have _ := S; have _ := h
  rfl

theorem thm3 (Dp : Deep) : True := by
  have _ := Dp
  trivial

end Sanctions.CensusFixture
