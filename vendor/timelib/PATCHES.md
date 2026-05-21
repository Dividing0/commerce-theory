# Local Patches

This vendored copy is based on `ammkrn/timelib` commit
`2c69e4a597a99d1ce748dea67af430db20ca0ea8`.

The upstream package targets Lean `v4.19.0-rc2`. The local changes keep the API
the project imports, while making the package compile under Lean `v4.29.1`:

- `Timelib/Date/Year.lean`: replace a removed `Nat.add_right_eq_self` simp
  reference and update deprecated integer nat-cast naming.
- `Timelib/Util.lean` and `Timelib/Duration/ESignedDuration.lean`: make
  `Option`-backed order proofs use definitional reduction instead of an older
  `simp` shape.
- `Timelib/DateTime/Parse.lean`: update deprecated integer nat-cast naming.
- `Timelib/DateTime/Naive.lean`: replace instance-unfolding `simp` proofs with
  `rfl`.
- `Timelib/Date/Convert.lean`: avoid running `omega` after branches already
  solved by `simp`.
- `Timelib/Duration/SignedDuration.lean`: use `String.ofList` for the Lean
  `v4.29.1` string representation and update deprecated nat-cast nonnegativity.
- `Timelib/Date/Month.lean`, `Timelib/Date/Ymd.lean`,
  `Timelib/Date/Ordinal.lean`, `Timelib/Duration/SignedDuration.lean`, and
  `Timelib/Duration/Constants.lean`: remove stale simp arguments reported by
  Lean `v4.29.1`'s unused-simp-argument linter.
- `Timelib.lean` and `lakefile.toml`: restrict the vendored library target to
  the date, naive timestamp, and signed-duration modules CommerceTheory uses.
- `lean-toolchain`: align the vendored package with the workspace toolchain.
